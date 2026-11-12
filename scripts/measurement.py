"""Bounded Linux child observations and provisional evidence publication.

Use from a single-threaded caller in a privately owned evidence directory.
The on-disk payload cannot confirm its own publication; use the returned receipt.
"""
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import hashlib
import math
import platform
import sys
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import tempfile
import time


@dataclass(frozen=True)
class Limits:
    wall: float = 25
    cpu: tuple[int, int] = (15, 16)
    address_space: int | None = None
    output_bytes: int = 8 * 1024**2
    cleanup: float = 2

    def __post_init__(self):
        if not all(math.isfinite(value) and value > 0 for value in (self.wall, self.cleanup)):
            raise ValueError('wall and cleanup budgets must be finite and positive')
        if (len(self.cpu) != 2 or any(type(value) is not int or value <= 0 for value in self.cpu)
                or self.cpu[0] > self.cpu[1]):
            raise ValueError('CPU limits must be positive soft/hard integers in order')
        if type(self.output_bytes) is not int or self.output_bytes <= 0:
            raise ValueError('output cap must be a positive integer')
        if self.address_space is not None and (type(self.address_space) is not int or self.address_space <= 0):
            raise ValueError('address-space cap must be a positive integer')


def publish(path, record):
    """Replace an owned record; return publication confirmation outside its payload."""
    started = time.monotonic()
    record = dict(record, publication='unknown', success=False)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', dir=Path(path).parent,
                                         delete=False) as output:
            temporary = Path(output.name)
            json.dump(record, output, indent=2)
            output.write('\n')
        temporary.replace(path)
        record['publication'] = 'confirmed'
    except OSError as error:
        record.update(publication='failed', recording_error=str(error))
    finally:
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError as error:
                record.update(publication='failed', recording_error=str(error))
    record['publication_seconds'] = time.monotonic()-started
    record['success'] = (record.get('status') == 'exited'
                         and record.get('returncode') == 0
                         and record.get('cleanup') == 'confirmed'
                         and record.get('output') == 'complete'
                         and record['publication'] == 'confirmed')
    return record


def _wait(process, seconds):
    deadline = time.monotonic() + seconds
    while True:
        pid, status, usage = os.wait4(process.pid, os.WNOHANG)
        if pid:
            process.returncode = os.waitstatus_to_exitcode(status)
            return usage
        if time.monotonic() >= deadline:
            raise subprocess.TimeoutExpired(process.args, seconds)
        time.sleep(min(.01, max(0, deadline-time.monotonic())))


def run_attempt(command, *, cwd, prefix, limits, env=None, metadata=None):
    prefix = Path(prefix)
    path = Path(str(prefix) + '.meta.json')
    record = dict(metadata or {}, command=list(command), cwd=str(cwd),
                  started_at=datetime.now(timezone.utc).isoformat(),
                  limits=asdict(limits), status='started', returncode=None,
                  publication='unknown', cleanup='unknown', output='unknown', success=False,
                  environment={key: (os.environ if env is None else env).get(key)
                               for key in ('PATH', 'LEAN_PATH')})
    try:
        with path.open('x') as output:
            json.dump(record, output)
    except OSError as error:
        return dict(record, status='recording_failed', publication='failed', recording_error=str(error))
    started = time.monotonic()
    def caps():
        resource.setrlimit(resource.RLIMIT_CPU, limits.cpu)
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits.output_bytes,) * 2)
        if limits.address_space is not None:
            resource.setrlimit(resource.RLIMIT_AS, (limits.address_space,) * 2)

    owned_logs = []
    process = None
    usage = None
    record['cleanup'] = 'confirmed'  # No child until Popen returns.
    try:
        with Path(str(prefix) + '.stdout').open('xb') as stdout:
            owned_logs.append('stdout')
            with Path(str(prefix) + '.stderr').open('xb') as stderr:
                owned_logs.append('stderr')
                try:
                    process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout,
                                               stderr=stderr, start_new_session=True, preexec_fn=caps)
                except (OSError, subprocess.SubprocessError) as error:
                    record.update(status='spawn_failed', error=str(error))
                if process is not None:
                    record['cleanup'] = 'unknown'
                    try:
                        usage = _wait(process, limits.wall)
                        record['status'] = ('signal' if process.returncode < 0 else
                                            'nonzero' if process.returncode else 'exited')
                        record['cleanup'] = 'confirmed'
                    except subprocess.TimeoutExpired:
                        record['status'] = 'timeout'
                    except KeyboardInterrupt:
                        record['status'] = 'interrupted'
                    except OSError as error:
                        record.update(status='observation_failed', observation_error=str(error))
    except OSError as error:
        record.update(status='recording_failed', recording_error=str(error))
    except KeyboardInterrupt:
        record.update(status='interrupted', cleanup='unknown')
    finally:
        if process is not None and process.returncode is None:
            try:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                usage = _wait(process, limits.cleanup)
                record['cleanup'] = 'confirmed'
            except (OSError, subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                record.update(cleanup='unknown', cleanup_error=repr(error))
        record.update(pid=process.pid if process is not None else None,
                      returncode=process.returncode if process is not None else None,
                      timed_out=record['status'] == 'timeout',
                      max_rss_kib=usage.ru_maxrss if usage is not None else None,
                      wall_seconds=time.monotonic()-started)
    record['output'] = 'complete' if len(owned_logs) == 2 else 'missing'
    for stream in owned_logs:
        try:
            with Path(str(prefix) + '.' + stream).open('rb') as log:
                data = log.read(limits.output_bytes + 1)
            if len(data) >= limits.output_bytes:
                record['output'] = 'overflow'  # At the cap, completeness is unknown.
            try:
                record[stream] = data[:limits.output_bytes].decode('utf-8')
            except UnicodeDecodeError:
                record[stream] = None
                record['output'] = 'invalid_utf8'
        except OSError as error:
            record.update(output='missing', recording_error=str(error))
    if record['cleanup'] != 'confirmed' and record['output'] == 'complete':
        record['output'] = 'incomplete'
    record['completed_at'] = datetime.now(timezone.utc).isoformat()
    record['signal'] = -record['returncode'] if record['returncode'] is not None and record['returncode'] < 0 else None
    return publish(path, record)


def source_identity(root, names):
    """Hash declared inputs; missing inputs are errors, not empty identities."""
    return {str(name): hashlib.sha256((Path(root)/name).read_bytes()).hexdigest()
            for name in sorted(set(names), key=str)}


def host_identity():
    try:
        with open('/proc/cpuinfo') as cpu:
            cpuinfo = cpu.read(65536)
    except OSError:
        cpuinfo = None
    return {'platform': platform.platform(), 'python': sys.version,
            'cpuinfo': cpuinfo, 'affinity': sorted(os.sched_getaffinity(0)),
            'clock': 'time.monotonic seconds; process spawn through observation/cleanup',
            'memory_scope': 'Linux wait4 ru_maxrss KiB for this child, including startup/imports'}

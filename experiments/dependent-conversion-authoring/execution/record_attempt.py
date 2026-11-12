#!/usr/bin/env python3
"""Record one check of an immutable source snapshot; never launch an author."""
import argparse
import datetime
import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import time


def digest(data):
    return hashlib.sha256(data).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_json(path, value):
    with path.open('x') as out:
        json.dump(value, out, indent=2)
        out.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--attempt', type=Path, required=True)
    parser.add_argument('--cwd', type=Path, required=True)
    parser.add_argument('--context', type=Path, required=True,
                        help='non-secret slot/session/route/phase/release/environment identity JSON')
    parser.add_argument('command', nargs=argparse.REMAINDER,
                        help='command after --; a {source} argument names the retained snapshot')
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if '{source}' not in command and '{sources}' not in command:
        parser.error('command must contain a separate {source} or {sources} argument')
    data = args.source.read_bytes()
    context_data = args.context.read_bytes()
    context = json.loads(context_data)
    required = ['slot', 'session', 'route', 'phase', 'release_sha256', 'environment_sha256']
    if any(not isinstance(context.get(key), str) or not context[key] for key in required):
        parser.error('context requires nonempty ' + ', '.join(required))
    attempt = args.attempt.absolute()
    attempt.mkdir(parents=True, exist_ok=False)
    snapshot = attempt / 'source.lean'
    snapshot.write_bytes(data)
    snapshot.chmod(0o444)
    (attempt / 'context.json').write_bytes(context_data)
    write_json(attempt / 'sources.json', [str(snapshot)])
    replacements = {'{source}': str(snapshot), '{sources}': str(attempt / 'sources.json')}
    actual = [replacements.get(item, item) for item in command]
    record = {'schema_version': 1, 'context': context, 'context_sha256': digest(context_data),
              'source_sha256': digest(data), 'source_original': str(args.source.absolute()),
              'command': actual, 'cwd': str(args.cwd.absolute()),
              'start_utc': utc(), 'start_monotonic_ns': time.monotonic_ns(),
              'observations': {'usage': None, 'active_reasoning_seconds': None,
                  'hibernation': 'unknown', 'throttling': 'unknown', 'unrelated_load': 'unknown',
                  'build_lock_wait_seconds': None, 'network_failure': 'unknown',
                  'assistance': 'unknown', 'interruptions': []}}
    write_json(attempt / 'started.json', record)
    exit_code = None
    child = None
    interrupted_signal = None

    def interrupted(signum, _frame):
        nonlocal interrupted_signal
        interrupted_signal = signum
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        with (attempt / 'output.log').open('x') as log:
            child = subprocess.Popen(actual, cwd=args.cwd, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            exit_code = child.wait()
        record['status'] = 'check-passed' if exit_code == 0 else 'check-failed'
    except OSError as error:
        record.update(status='environment-failed', error=str(error))
    except KeyboardInterrupt:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        if child is not None:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                exit_code = child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                exit_code = child.wait()
        record['status'] = 'interrupted'
        record['observations']['interruptions'].append(
            {'signal': interrupted_signal, 'observed_utc': utc(), 'duration_seconds': None})
    record.update(exit_code=exit_code, finish_utc=utc(),
                  finish_monotonic_ns=time.monotonic_ns())
    record['output_sha256'] = digest((attempt / 'output.log').read_bytes())
    write_json(attempt / 'result.json', record)
    print(json.dumps({'attempt': str(attempt), 'status': record['status'],
                      'exit_code': exit_code}))
    return 130 if record['status'] == 'interrupted' else (exit_code if exit_code is not None else 125)


if __name__ == '__main__':
    raise SystemExit(main())

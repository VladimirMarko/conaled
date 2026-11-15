#!/usr/bin/env python3
"""Root-owned serial invocation and closure recording; no mathematical credit."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from datetime import datetime, timezone

OWN = Path(__file__).resolve().parent
CTRL = OWN.parents[1]
BASE = CTRL.parent
WT = BASE / 'conaled-ch01-review'
STATE = BASE / 'conaled-native-state'
PREP = CTRL / 'provenance/chapter02-receiving-targeted-statements1297-prepared-20261104'
FULL = CTRL / 'provenance/chapter02-complete-receiving-full-attempt1-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
L = '726cb9a9b9ff4444a7614383de4fb336e8804aa7'
VERIFY = 'fb794d107281f07ec8470de0f4af0028b1a78c1b774d0e01f742221063493aca'

def now():
    return datetime.now(timezone.utc).isoformat()

def fingerprint(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def checked(row):
    actual = fingerprint(row['path'])
    assert actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256'], row['path']
    return actual

def load(path):
    return json.loads(Path(path).read_text())

def save(path, data):
    with Path(path).open('x') as stream:
        stream.write(json.dumps(data, indent=2) + '\n')
        stream.flush()
        os.fsync(stream.fileno())

def git(*args):
    return subprocess.check_output(['git', '-C', str(WT), *args], text=True).strip()

def unchanged():
    assert git('rev-parse', 'HEAD') == Q
    assert git('rev-parse', 'HEAD^{tree}') == 'fe0bd9f17a5e1a09797be55fd79491e8c363cbd0'
    assert git('status', '--porcelain=v1', '--untracked-files=all') == ''
    assert git('rev-parse', 'refs/heads/work/fdsa-book') == L
    assert fingerprint(WT / '.lake/verification.json')['sha256'] == VERIFY
    assert fingerprint(FULL / 'verification.json')['sha256'] == VERIFY

def close_profile(profile, directory, terminal, before):
    result = load(directory / 'result.json')
    request = load(directory / 'request.json')
    start = load(directory / 'start.json')
    outer = (directory / 'full.log').read_bytes()
    argv = profile['receiving_outer_argv']
    requested = argv[argv.index('--') + 1:]
    expected_native = ['lake', 'env', 'lean', profile['program']['path']]
    assert terminal['actual_exit'] == result['exit_code'] == 0
    assert result['state'] == 'passed' and result['final_head'] == Q and result['final_status'] == ''
    assert not result.get('bookkeeping_error') and not result['progress_bookkeeping_errors']
    assert request['candidate'] == start['candidate'] == result['candidate'] == Q
    assert request['command'] == start['command'] == result['command'] == requested
    assert request['cwd'] == start['cwd'] == str(WT)
    assert start['initial_head'] == Q and start['initial_status'] == ''
    assert len(outer) == result['log_size_bytes']
    assert hashlib.sha256(outer).hexdigest() == result['log_sha256']
    matches = re.findall(rb'^\[result\] exit=0(?:, [^;\n]+)?; (.+/result\.json)$', outer, re.M)
    assert len(matches) == 1
    origin = Path(matches[0].decode()).parent
    assert origin.resolve().parent == (STATE / 'logs').resolve()
    native_start = load(origin / 'start.json')
    native_result = load(origin / 'result.json')
    native = (origin / 'output.log').read_bytes()
    assert native and outer.count(native) == 1
    for record in (native_start, native_result):
        assert record['command'] == expected_native and record['cwd'] == str(WT)
        assert record['lean_threads'] == '1' and record['label'] == 'project-run'
        assert record['log'] == str(origin / 'output.log')
    assert native_result['passed'] is True and native_result['exit_code'] == 0
    assert native_result['timed_out'] is False and native_result['recorder_error'] is None
    assert native_start['started_utc'] == native_result['started_utc']
    times = [terminal['started_utc'], start['started_utc'], native_result['started_utc'], native_result['completed_utc'], result['completed_utc'], terminal['completed_utc']]
    assert [datetime.fromisoformat(x) for x in times] == sorted(datetime.fromisoformat(x) for x in times)
    verification = load(directory / 'verification.json')
    assert fingerprint(directory / 'verification.json')['sha256'] == result['verification_record_sha256'] == VERIFY
    assert verification['candidate'] == Q and verification['result'] == 'passed'
    assert datetime.fromisoformat(verification['completed_at']) < datetime.fromisoformat(times[0])
    after = checked(profile['program'])
    assert before == after
    unchanged()
    offset = outer.index(native)
    prefix, suffix = outer[:offset], outer[offset + len(native):]
    prefix_lines = prefix.splitlines()
    assert len(prefix_lines) == 2 and prefix_lines[0].startswith(b'[lock] project-')
    assert prefix_lines[1] == ('[run] ' + ' '.join(expected_native)).encode()
    assert len(suffix.splitlines()) == 1 and suffix.startswith(b'[result] exit=0')
    copied = directory / 'native-records'
    copied.mkdir(exist_ok=False)
    copied_rows = []
    for name in ('start.json', 'result.json', 'output.log'):
        data = (origin / name).read_bytes()
        with (copied / name).open('xb') as stream:
            stream.write(data)
        assert (copied / name).read_bytes() == data
        copied_rows.append({'origin': str(origin / name), **fingerprint(copied / name)})
    (directory / 'outer-prefix.log').write_bytes(prefix)
    (directory / 'outer-suffix.log').write_bytes(suffix)
    closure = {'recorded_utc': now(), 'candidate': Q, 'profile_number': profile['number'], 'label': profile['label'], 'terminal': terminal, 'program_before': before, 'program_after': after, 'native_origin': str(origin), 'native_records': copied_rows, 'outer_log': fingerprint(directory / 'full.log'), 'native_output_exact_outer_offset': offset, 'outer_prefix': fingerprint(directory / 'outer-prefix.log'), 'outer_suffix': fingerprint(directory / 'outer-suffix.log'), 'complete_closed_log': True, 'inherited_full_verification': fingerprint(directory / 'verification.json'), 'inherited_verification_is_not_a_new_full_check': True, 'mathematical_or_type_qualification_credit': 0}
    save(directory / 'closed-evidence-reconciliation.json', closure)
    return {'profile_number': profile['number'], 'label': profile['label'], 'actual_exit': 0, 'directory': str(directory), 'closed_evidence': fingerprint(directory / 'closed-evidence-reconciliation.json'), 'native_output': fingerprint(copied / 'output.log'), 'program': after}

def main():
    gate = load(OWN / 'execution-release.json')
    assert gate['released_for_serial_execution'] is True and gate['candidate'] == Q
    for row in gate['bound_files']:
        checked(row)
    manifest = load(PREP / 'manifest.json')
    assert manifest['receiver'] == Q and manifest['profile_count'] == 11
    for profile in manifest['profiles']:
        assert not (CTRL / 'provenance' / profile['receiving_run_name']).exists()
        checked(profile['program'])
    unchanged()
    save(OWN / 'execution-start.json', {'started_utc': now(), 'candidate': Q, 'owner': '/root', 'driver_pid': os.getpid(), 'release': fingerprint(OWN / 'execution-release.json'), 'method': fingerprint(__file__), 'exclusive_serial_one_thread': True, 'profiles': 11, 'no_install_hydration_fresh_or_retry': True})
    completed = []
    try:
        for profile in manifest['profiles']:
            unchanged()
            before = checked(profile['program'])
            label = profile['label']
            save(OWN / (label + '-program-before.json'), {'recorded_utc': now(), 'program': before, 'argv': profile['receiving_outer_argv']})
            started = now()
            tick = time.monotonic()
            print(json.dumps({'event': 'starting', 'profile': profile['number'], 'label': label, 'utc': started}), flush=True)
            with (OWN / (label + '-launcher.log')).open('xb') as output:
                child = subprocess.run(profile['receiving_outer_argv'], cwd=WT, stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT, check=False)
            terminal = {'started_utc': started, 'completed_utc': now(), 'actual_exit': child.returncode, 'elapsed_seconds': time.monotonic() - tick, 'owner': '/root serial driver', 'observation': 'subprocess.run returned after actual recorder termination; not a tool-session terminal claim', 'argv': profile['receiving_outer_argv']}
            save(OWN / (label + '-subprocess-terminal.json'), terminal)
            directory = CTRL / 'provenance' / profile['receiving_run_name']
            if directory.is_dir():
                save(directory / 'owned-subprocess-terminal.json', terminal)
            if child.returncode != 0:
                raise RuntimeError('Actual nonzero recorder exit for ' + label + ': ' + str(child.returncode))
            completed.append(close_profile(profile, directory, terminal, before))
            print(json.dumps({'event': 'closed', 'profile': profile['number'], 'label': label, 'actual_exit': child.returncode, 'native_bytes': completed[-1]['native_output']['bytes']}), flush=True)
    except BaseException as error:
        save(OWN / 'execution-result.json', {'completed_utc': now(), 'status': 'stopped-unresolved', 'error': repr(error), 'completed_profiles': completed, 'no_automatic_retry': True})
        raise
    save(OWN / 'execution-result.json', {'completed_utc': now(), 'status': 'all-eleven-closed-zero', 'candidate': Q, 'completed_profiles': completed, 'all_programs_bound_unchanged': True, 'type_qualification_credit': 0, 'post_observation_pending': True, 'independent_final_assessment_pending': True})
    print(json.dumps({'event': 'serial-execution-complete', 'profiles': len(completed), 'result': str(OWN / 'execution-result.json')}), flush=True)

if __name__ == '__main__':
    main()

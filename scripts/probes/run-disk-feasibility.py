#!/usr/bin/env python3
"""Reproduce one historical numerical probe using this checkout's built modules."""
import json
import os
from pathlib import Path
import shlex
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from measurement import Limits, host_identity, publish, run_attempt, source_identity
from project_sources import inventory

ROOT = Path(__file__).resolve().parents[2]
CAPS = Limits(address_space=16 * 1024**3)


def numerical_output(text, args):
    """Validate this probe's textual protocol; keep exact fractions/timings as strings."""
    from fractions import Fraction
    kind, n, num, den, tol_den, bit_cap, mode = args
    planned = int(n) * (3 if kind == 'word' else 1)
    events = []
    for line in text.splitlines():
        fields = [item.split('=', 1) for item in shlex.split(line)]
        if not fields or any(len(item) != 2 for item in fields):
            raise ValueError('malformed numerical event')
        row = dict(fields)
        if len(row) != len(fields):
            raise ValueError('duplicate numerical field')
        events.append(row)
    if not events:
        raise ValueError('missing terminal numerical event')
    terminal = events[-1]
    event = terminal.get('event')
    allowed = {'whole'} if mode == 'whole' else {'complete', 'bit_cutoff', 'rejected'}
    if event not in allowed or (mode == 'whole' and len(events) != 1):
        raise ValueError('unexpected terminal numerical event')
    required = {
        'whole': {'success', 'attempts', 'accepted', 'rejected', 'num_bits', 'den_bits', 'error', 'meets_tolerance', 'elapsed_ns'},
        'step': {'index', 'num_bits', 'den_bits', 'error', 'clock', 'step_ns'},
        'complete': {'accepted', 'error', 'clock', 'meets_tolerance', 'elapsed_ns'},
        'bit_cutoff': {'accepted', 'num_bits', 'den_bits'},
        'rejected': {'index', 'attempts', 'rejected', 'step_ns'},
    }
    for row in events:
        tag = row.get('event')
        if tag not in required or set(row) != required[tag] | {'event'}:
            raise ValueError('missing or unexpected numerical fields')
        for key, value in row.items():
            if key in {'error', 'clock'}:
                if value == 'null':
                    if not (key == 'error' and tag == 'whole' and row['success'] == 'false'):
                        raise ValueError('missing exact budget/clock')
                elif Fraction(value) < 0:
                    raise ValueError('negative budget/clock')
            elif key in {'success', 'meets_tolerance'}:
                if value not in {'true', 'false'}:
                    raise ValueError('invalid boolean')
            elif key != 'event' and (not value.isascii() or not value.isdigit()):
                raise ValueError('invalid nonnegative integer')
    for index, row in enumerate(events[:-1], 1):
        if row['event'] != 'step' or int(row['index']) != index:
            raise ValueError('incomplete or reordered step prefix')
    if mode == 'steps':
        count = int(terminal['index' if event == 'rejected' else 'accepted'])
        if count != len(events)-1 or count > planned:
            raise ValueError('terminal prefix count mismatch')
        if event == 'complete' and count != planned:
            raise ValueError('incomplete schedule')
        if event != 'complete' and count >= planned:
            raise ValueError('failure after entire schedule')
        if event == 'rejected' and (terminal['attempts'], terminal['rejected']) != ('1', '1'):
            raise ValueError('invalid rejected-step accounting')
    else:
        attempts, accepted, rejected = (int(terminal[key]) for key in ('attempts', 'accepted', 'rejected'))
        if attempts != accepted + rejected or not 0 < attempts <= planned:
            raise ValueError('invalid whole-run accounting')
        if terminal['success'] == 'true':
            if accepted != planned or rejected:
                raise ValueError('invalid successful whole-run counts')
        elif rejected != 1 or terminal['error'] != 'null' or terminal['meets_tolerance'] != 'false':
            raise ValueError('invalid unsuccessful whole-run result')
    if event in {'whole', 'complete'} and terminal.get('success', 'true') == 'true':
        if terminal['error'] == 'null':
            raise ValueError('missing final budget')
        meets = Fraction(terminal['error']) <= Fraction(1, int(tol_den))
        if (terminal['meets_tolerance'] == 'true') != meets:
            raise ValueError('inconsistent tolerance observation')
        outcome = 'meets_tolerance' if meets else 'misses_tolerance'
    else:
        outcome = 'bit_cutoff' if event == 'bit_cutoff' else 'checked_rejection'
    return {'outcome': outcome, 'events': events}


def main():
    started = time.monotonic()
    if len(sys.argv) != 10:
        print('usage: run-disk-feasibility.py OUTPUT_DIR NAME KIND N NUM DEN TOL_DEN BIT_CAP MODE', file=sys.stderr)
        return 2
    outdir, name = Path(sys.argv[1]), sys.argv[2]
    args = sys.argv[3:]
    if not name or name in {'.', '..'} or Path(name).name != name:
        print('NAME must be a basename', file=sys.stderr)
        return 2
    prefix = outdir/name
    metadata = {'receipt_kind': 'probe execution; not candidate validation', 'workload': args,
                'caps': {'address_space_gib': 16, 'cpu_seconds': [15, 16],
                         'wall_seconds': 25, 'output_bytes': 8*1024**2}}
    reserved = False
    try:
        outdir.mkdir(parents=True, exist_ok=True)
        if any(Path(str(prefix)+ext).exists() for ext in ('.meta.json', '.stdout', '.stderr')):
            raise FileExistsError('evidence name already exists; choose a new NAME')
        setup = Path(str(prefix)+'.setup')
        setup.mkdir()
        reserved = True
        provisional = publish(setup/'setup.json', dict(metadata, status='started'))
        if provisional['publication'] != 'confirmed':
            raise OSError('initial setup publication failed')
        metadata.update(host_identity())
        kind, n, num, den, tol, cap, mode = args
        if (kind not in {'move', 'turn', 'word', 'hold', 'origin'} or mode not in {'whole', 'steps'}
                or any(not s.isascii() or not s.isdigit() for s in (n, num, den, tol, cap))
                or not 1 <= int(n) <= 256 or min(int(den), int(tol), int(cap)) <= 0):
            raise ValueError('invalid probe parameters')
        names = [str(path.relative_to(ROOT)) for path in inventory(ROOT).values()]
        names += ['scripts/probes/DiskDriverFeasibility.lean', 'scripts/probes/run-disk-feasibility.py',
                  'scripts/measurement.py', 'scripts/project_sources.py', 'lean-toolchain',
                  'lake-manifest.json', 'lakefile.toml', 'flake.lock']
        metadata['sources'] = source_identity(ROOT, names)
        env = dict(os.environ)
        env.pop('LEAN_PATH', None)
        version = run_attempt(['lake', 'env', 'lean', '--version'], cwd=ROOT,
                              prefix=setup/'compiler', limits=CAPS, env=env,
                              metadata={'phase': 'toolchain'})
        if not version['success']:
            raise RuntimeError('compiler observation failed; see setup/compiler.meta.json')
        metadata['version'] = version['stdout'].strip()
        expected = (ROOT/'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
        if f'version {expected},' not in metadata['version']:
            raise ValueError('compiler differs from lean-toolchain')
        metadata['environment'] = {'LEAN_PATH': 'removed; Lake resolves paths', 'PATH': env.get('PATH')}
        command = ['lake', 'env', 'lean', '-j1', '--run', 'scripts/probes/DiskDriverFeasibility.lean', *args]
        metadata['setup_wall_seconds'] = time.monotonic()-started
        result = run_attempt(command, cwd=ROOT, prefix=prefix, limits=CAPS, env=env,
                             metadata=dict(metadata, phase='probe invocation; existing project artifacts'))
        if result['publication'] != 'confirmed':
            print(json.dumps(result))
            return 1
        if source_identity(ROOT, names) != metadata['sources']:
            result.update(status='input_changed', success=False)
        elif result['status'] in {'exited', 'nonzero'} and result['output'] == 'complete':
            try:
                result['numerical'] = numerical_output(result['stdout'], args)
                expected_code = 3 if result['numerical']['outcome'] == 'bit_cutoff' else 0
                if result['returncode'] != expected_code:
                    raise ValueError('terminal event and exit code disagree')
            except (ValueError, KeyError, ZeroDivisionError) as error:
                result.update(status='malformed_output', output_error=str(error))
        result['orchestration_wall_seconds'] = time.monotonic()-started
        result = publish(Path(str(prefix)+'.meta.json'), result)
        print(json.dumps(result))
        return 0 if result['success'] else 1
    except (OSError, ValueError, RuntimeError, KeyboardInterrupt) as error:
        failure = dict(metadata, status='setup_failed', error=str(error), success=False,
                       publication='unknown', returncode=None)
        if reserved and not Path(str(prefix)+'.meta.json').exists():
            failure = publish(Path(str(prefix)+'.meta.json'), failure)
        print(json.dumps(failure))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())

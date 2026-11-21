#!/usr/bin/env python3
"""Compare unchanged classification clients in two pinned, privately built trees.

Run in the development shell. The specialized tree uses original budgets; the
retained direct patch is measured at both the original depth and depth 1024.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
CLIENTS = ('CubicalAuthorTransport', 'CubicalConstructorState',
           'CartesianPackageRecomputation', 'CubicalInterpretationObservations')
SPEC = importlib.util.spec_from_file_location(
    'retained_benchmark', ROOT / 'scripts/benchmark-representable-classification.py')
RETAINED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RETAINED)
# The high threshold suppresses automatic nested traces. Explicit command traces
# still report inclusive internal heartbeat counts; only unindented roots are summed.
PROFILE = ['-DElab.async=false', '-Dtrace.profiler=true',
           '-Dtrace.profiler.useHeartbeats=true',
           '-Dtrace.profiler.threshold=1000000000', '-Dtrace.Elab.command=true']


def measurements(output):
    return [int(n) for n in re.findall(r'^\[Elab\.command\] \[(\d+)\.000000\]',
                                      output, re.MULTILINE)]


def run(workspace, path, recursion=None, heartbeats=None, timeout=30):
    args = ['lake', 'env', 'lean', *PROFILE]
    if recursion is not None:
        args.append(f'-DmaxRecDepth={recursion}')
    if heartbeats is not None:
        args.append(f'-DmaxHeartbeats={heartbeats}')
    args.append(str(path))
    start = time.perf_counter()
    p = subprocess.Popen(args, cwd=workspace, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = p.communicate(timeout=timeout)
        failures = [name for name, marker in (
            ('recursion', 'maximum recursion depth'),
            ('heartbeats', 'maximum number of heartbeats')) if marker in output]
        status = 'pass' if p.returncode == 0 else '+'.join(failures) or 'error'
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        output, _ = p.communicate()
        status = 'timeout'
    elapsed = time.perf_counter() - start
    counts = measurements(output)
    if status == 'pass' and not counts:
        status = 'missing_measurement'
    return {'status': status, 'returncode': p.returncode, 'wall_seconds': elapsed,
            'command_internal_heartbeats': counts,
            'total_internal_heartbeats': sum(counts) if counts else None,
            'command': args, 'diagnostics': output}


def inputs(workspace):
    result = RETAINED.identity(workspace)
    result['clients'] = {name: hashlib.sha256(
        (workspace / f'Examples/{name}.lean').read_bytes()).hexdigest() for name in CLIENTS}
    manifest = json.loads((workspace / 'lake-manifest.json').read_text())
    result['dependencies'] = {
        pkg['name']: {'commit': RETAINED.command(workspace / '.lake/packages' / pkg['name'],
                                               'git', 'rev-parse', 'HEAD'),
                      'status': RETAINED.command(workspace / '.lake/packages' / pkg['name'],
                                               'git', 'status', '--porcelain')}
        for pkg in manifest['packages']}
    if any(dep['status'] for dep in result['dependencies'].values()):
        raise RuntimeError('dependency checkout has local changes')
    for pkg in manifest['packages']:
        if result['dependencies'][pkg['name']]['commit'] != pkg['rev']:
            raise RuntimeError(f'dependency revision mismatch: {pkg["name"]}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--specialized', type=Path, required=True)
    parser.add_argument('--direct', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=2)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.repeats < 1 or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('repeats and finite timeout must be positive')
    workspaces = {label: getattr(args, label).resolve() for label in ('specialized', 'direct')}
    if len({(w / '.lake/build').resolve() for w in workspaces.values()}) != 2:
        parser.error('workspaces must have distinct private build directories')
    report = {'time_utc': datetime.now(timezone.utc).isoformat(),
              'host': platform.uname()._asdict(), 'workspaces': {}, 'results': [],
              'settings': {'repeats': args.repeats, 'timeout': args.timeout,
                           'profiling_options': PROFILE, 'heartbeat_unit': 'internal (1000 per budget unit)'},
              'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'retained_runner_sha256': hashlib.sha256(Path(SPEC.origin).read_bytes()).hexdigest()}
    for label, workspace in workspaces.items():
        before = inputs(workspace)
        report['workspaces'][label] = before
        imports = set()
        for name in CLIENTS:
            text = (workspace / f'Examples/{name}.lean').read_text()
            if re.search(r'\bset_option\s+(maxRecDepth|maxHeartbeats|Elab\.async)\b', text):
                raise RuntimeError(f'client overrides measured options: {name}')
            imports.update(re.findall(r'^import (\S+)\s*$', text, re.MULTILINE))
        subprocess.run(['lake', 'build', *sorted(imports)], cwd=workspace, check=True,
                       stdout=subprocess.DEVNULL)
        if inputs(workspace) != before:
            raise RuntimeError(f'inputs changed during build: {label}')
    if report['workspaces']['specialized']['clients'] != report['workspaces']['direct']['clients']:
        raise RuntimeError('comparison clients differ')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # Alternate forms within each repetition to reduce ordering bias. All builds
    # finish before timing. No client file or dependency is edited by the runner.
    for repeat in range(args.repeats):
        for name in CLIENTS:
            for label, recursion in [('specialized', None), ('direct', None), ('direct', 1024)]:
                row = {'workspace': label, 'client': name, 'repeat': repeat,
                       'maxRecDepth': recursion or 512, 'maxHeartbeats': 200000,
                       'budget_override': {} if recursion is None else {'maxRecDepth': recursion}}
                row.update(run(workspaces[label], Path(f'Examples/{name}.lean'),
                               recursion=recursion, timeout=args.timeout))
                report['results'].append(row)
                args.output.write_text(json.dumps(report, indent=2) + '\n')
                print(label, name, row['maxRecDepth'], row['status'],
                      row['total_internal_heartbeats'], flush=True)
    for label, workspace in workspaces.items():
        if inputs(workspace) != report['workspaces'][label]:
            raise RuntimeError(f'inputs changed during measurement: {label}')
    report['inputs_verified_after'] = True
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Complete unchanged classifier clients under a predeclared finite protocol.

Run in the pinned development shell. Reuses the #648 input identity machinery;
project outputs must be private. JSON diagnostics retain command source ranges.
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
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('clients', ROOT / 'scripts/benchmark-classification-clients.py')
CLIENTS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CLIENTS)
PROFILE = ['-DElab.async=false', '-Dtrace.profiler=true',
           '-Dtrace.profiler.threshold=1000000000', '-Dtrace.Elab.command=true']
MODES = ('heartbeats', 'seconds', 'sync', 'async')


def command_measurements(output, mode):
    """Extract trace-message roots, retaining source ranges for expansion filtering."""
    records = []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(message, dict):
            continue
        text = message.get('data', '')
        match = re.match(r'^\[Elab\.command\] \[([0-9]+\.[0-9]+)\] (.*)', text, re.S)
        if not match:
            continue
        number = float(match[1])
        record = {'line': message['pos']['line'], 'column': message['pos']['column'],
                  'end': message.get('endPos'), 'text': match[2]}
        record['internal_heartbeats' if mode == 'heartbeats' else 'seconds'] = (
            int(number) if mode == 'heartbeats' else number)
        records.append(record)
    return records


def source_roots(traces):
    """Remove expanded commands enclosed by another emitted source command.

    Synchronous scoped commands emit children and their inclusive parent as
    separate messages. Missing or overlapping nonnested ranges prevent a total;
    equal outermost ranges are ambiguous rather than silently deduplicated.
    """
    ranges = []
    for c in traces:
        if c['end'] is None:
            return [], ['missing source end position']
        start = (c['line'], c['column'])
        end = (c['end']['line'], c['end']['column'])
        if end < start:
            return [], ['reversed source range']
        ranges.append((start, end))
    roots = []
    for i, (start, end) in enumerate(ranges):
        contained = any(j != i and a <= start and end <= b and start < b and
                        (a, b) != (start, end) for j, (a, b) in enumerate(ranges))
        if not contained:
            roots.append(i)
    problems = []
    for n, i in enumerate(roots):
        a, b = ranges[i]
        for j in roots[n + 1:]:
            c, d = ranges[j]
            if (a, b) == (c, d) or max(a, c) < min(b, d):
                problems.append({'overlapping_trace_indices': [i, j]})
    return [traces[i] for i in roots], problems


def run(workspace, path, mode, recursion, timeout, heartbeats=200000, line_buffered=True):
    if mode not in MODES or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('known mode and positive finite timeout required')
    args = (['stdbuf', '-oL', '-eL'] if line_buffered else []) + ['lake', 'env', 'lean', '--json']
    if mode in ('heartbeats', 'seconds'):
        args += PROFILE + [f'-Dtrace.profiler.useHeartbeats={str(mode == "heartbeats").lower()}']
    elif mode == 'sync':
        args += ['-DElab.async=false']
    # Explicitly restate the original per-command budget, without disabling it.
    args += [f'-DmaxRecDepth={recursion}', f'-DmaxHeartbeats={heartbeats}', str(path)]
    start = time.perf_counter()
    load_before = os.getloadavg()
    process = subprocess.Popen(args, cwd=workspace, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=timeout)
        failures = [name for name, marker in (
            ('recursion', 'maximum recursion depth'),
            ('heartbeats', 'maximum number of heartbeats')) if marker in output]
        status = 'pass' if process.returncode == 0 else '+'.join(failures) or 'error'
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        status = 'timeout'
    elapsed = time.perf_counter() - start
    traces = command_measurements(output, mode) if mode in ('heartbeats', 'seconds') else []
    commands, problems = source_roots(traces)
    if status == 'pass' and problems:
        status = 'ambiguous_measurement'
    elif status == 'pass' and mode in ('heartbeats', 'seconds') and not commands:
        status = 'missing_measurement'
    return {'status': status, 'returncode': process.returncode, 'wall_seconds': elapsed,
            'commands': commands, 'command_traces': traces, 'aggregation_problems': problems,
            'total_internal_heartbeats': sum(c['internal_heartbeats'] for c in commands)
                if commands and not problems and mode == 'heartbeats' else None,
            'total_command_seconds': sum(c['seconds'] for c in commands)
                if commands and not problems and mode == 'seconds' else None,
            'measurements_complete': status == 'pass' and bool(commands),
            'load_before': load_before, 'load_after': os.getloadavg(),
            'command': args, 'diagnostics': output}


def buffering_control(workspace):
    """A completed declaration followed by sleeping IO isolates pipe buffering."""
    source = 'import Mathlib.Data.Nat.Basic\nexample : 1 + 1 = 2 := by decide\n#eval IO.sleep 10000\n'
    with tempfile.TemporaryDirectory(prefix='classification-buffer-') as tmp:
        path = Path(tmp) / 'Buffering.lean'
        path.write_text(source)
        before = sha(path)
        rows = {name: run(workspace, path, 'heartbeats', 512, 4, line_buffered=buffered)
                for name, buffered in [('default_buffering', False), ('line_buffered', True)]}
        return {'source': source, 'source_sha256': before, 'source_unchanged': sha(path) == before,
                'timeout_seconds': 4, **rows}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--specialized', type=Path, required=True)
    parser.add_argument('--direct', type=Path, required=True)
    parser.add_argument('--protocol', type=Path, default=ROOT / 'experiments/representable-classification/complete-protocol.json')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--pause-between-clients', action='store_true',
                        help='wait for Enter before each client pair, outside measurement')
    args = parser.parse_args()
    protocol = json.loads(args.protocol.read_text())
    timeout = protocol['timeout_seconds']
    if not math.isfinite(timeout) or timeout <= 0:
        parser.error('protocol requires a positive finite timeout')
    if (protocol['per_command_heartbeats'], protocol['specialized_maxRecDepth'],
            protocol['direct_maxRecDepth']) != (200000, 512, 1024):
        parser.error('this protocol retains 200000 heartbeats and specialized512/direct1024')
    for stage in protocol['stages']:
        if (stage['mode'] not in MODES or stage['repeats'] < 1 or
                not set(stage['clients']) <= set(CLIENTS.CLIENTS)):
            parser.error('invalid protocol stage')
    workspaces = {k: getattr(args, k).resolve() for k in ('specialized', 'direct')}
    if len({(w / '.lake/build').resolve() for w in workspaces.values()}) != 2:
        parser.error('private, distinct project build directories required')
    report = {'started_at': datetime.now(timezone.utc).isoformat(),
              'protocol': protocol, 'protocol_sha256': sha(args.protocol),
              'host': platform.uname()._asdict(), 'cpu_count': os.cpu_count(),
              'runners': {p: sha(ROOT / p) for p in (
                  'scripts/benchmark-classification-complete.py',
                  'scripts/benchmark-classification-clients.py',
                  'scripts/benchmark-representable-classification.py')},
              'patch_sha256': sha(ROOT / 'experiments/representable-classification/direct.patch'),
              'prior_results_sha256': sha(ROOT / 'experiments/representable-classification/clients-results.json'),
              'workspaces': {}, 'results': []}
    patch = (ROOT / 'experiments/representable-classification/direct.patch').read_bytes()
    for label, workspace in workspaces.items():
        before = CLIENTS.inputs(workspace)
        if before['commit'] != protocol['source_commit']:
            raise RuntimeError(f'wrong source pin: {label}')
        # Match the entire retained patch, not merely the expected changed paths.
        actual = subprocess.check_output(['git', 'diff', 'HEAD', '--', '*.lean'], cwd=workspace)
        if actual != (patch if label == 'direct' else b''):
            raise RuntimeError(f'unexpected production source difference: {label}')
        imports = set()
        for name in CLIENTS.CLIENTS:
            source = (workspace / f'Examples/{name}.lean').read_text()
            if re.search(r'\bset_option\s+(maxRecDepth|maxHeartbeats|Elab\.async)\b', source):
                raise RuntimeError(f'client overrides measured options: {name}')
            imports.update(re.findall(r'^import (\S+)\s*$', source, re.M))
        subprocess.run(['lake', 'build', *sorted(imports)], cwd=workspace, check=True,
                       stdout=subprocess.DEVNULL)
        if CLIENTS.inputs(workspace) != before:
            raise RuntimeError(f'inputs changed during build: {label}')
        report['workspaces'][label] = before | {'build_directory': str((workspace / '.lake/build').resolve())}
    if report['workspaces']['specialized']['clients'] != report['workspaces']['direct']['clients']:
        raise RuntimeError('client source mismatch')
    prior = json.loads((ROOT / 'experiments/representable-classification/clients-results.json').read_text())
    if report['workspaces']['specialized']['clients'] != prior['workspaces']['specialized']['clients']:
        raise RuntimeError('original #648 client bytes changed')
    report['buffering_control'] = buffering_control(workspaces['specialized'])
    save(args.output, report)
    for stage in protocol['stages']:
        for repeat in range(stage['repeats']):
            for name in stage['clients']:
                if args.pause_between_clients:
                    input(f'READY {stage["mode"]} {repeat} {name}; Enter starts pair\n')
                for label in (('specialized', 'direct') if repeat % 2 == 0 else ('direct', 'specialized')):
                    row = {'workspace': label, 'client': name, 'repeat': repeat, 'mode': stage['mode'],
                           'maxRecDepth': 512 if label == 'specialized' else 1024, 'maxHeartbeats': 200000}
                    print('START', label, name, stage['mode'], repeat, flush=True)
                    row.update(run(workspaces[label], Path(f'Examples/{name}.lean'), stage['mode'],
                                   row['maxRecDepth'], timeout))
                    report['results'].append(row)
                    save(args.output, report)
                    print('END', label, name, stage['mode'], row['status'],
                          row['wall_seconds'], row['total_internal_heartbeats'], flush=True)
    for label, workspace in workspaces.items():
        expected = dict(report['workspaces'][label])
        del expected['build_directory']
        if CLIENTS.inputs(workspace) != expected:
            raise RuntimeError(f'inputs changed during measurement: {label}')
    if sha(args.protocol) != report['protocol_sha256']:
        raise RuntimeError('protocol changed during measurement')
    if any(sha(ROOT / p) != value for p, value in report['runners'].items()):
        raise RuntimeError('runner changed during measurement')
    report['inputs_verified_after'] = True
    report['completed_at'] = datetime.now(timezone.utc).isoformat()
    save(args.output, report)


if __name__ == '__main__':
    main()

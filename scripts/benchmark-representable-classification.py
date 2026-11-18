#!/usr/bin/env python3
"""Bounded, sequential Lean elaboration probes in independently built workspaces.

Run inside the development shell. Each workspace must have a private build tree;
Lake checks its import closure before timing. Output includes complete diagnostics.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def command(workspace, *args):
    return subprocess.check_output(args, cwd=workspace, text=True).strip()


def identity(workspace):
    names = command(workspace, 'git', 'ls-files', '--cached', '--others',
                    '--exclude-standard', '--', '*.lean', 'lean-toolchain',
                    'lakefile.toml', 'lake-manifest.json', 'flake.lock').splitlines()
    digest = hashlib.sha256()
    for name in sorted(set(names)):
        digest.update(name.encode() + b'\0')
        digest.update((workspace / name).read_bytes())
    return {'commit': command(workspace, 'git', 'rev-parse', 'HEAD'),
            'source_sha256': digest.hexdigest(),
            'diff': command(workspace, 'git', 'diff', 'HEAD', '--', '*.lean'),
            'lean': command(workspace, 'lake', 'env', 'lean', '--version'),
            'manifest_sha256': hashlib.sha256((workspace / 'lake-manifest.json').read_bytes()).hexdigest()}


def source(probe, depth, recursion, heartbeats):
    if probe == 'regression':
        original = (ROOT / 'experiments/representable-classification/reduction-repro.lean.txt').read_text()
        setup, measured = original.split('noncomputable def packageIdentity', 1)
        measured = 'noncomputable def packageIdentity' + measured
    else:
        setup = '''import Examples.CubicalFiniteStateIdentity
namespace Examples.NestedRecovery
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
variable {Γ : Context} (A : LocalFamily Γ)
'''
        for i in range(depth + 1):
            value = 'A' if i == 0 else f'decodedLocalFamily (F{i-1} A).code'
            setup += f'def F{i} := {value}\n'
        term = 'Iso.refl A.family'
        for i in range(depth):
            term = f'(F{i} A).decodeCodeIso ≪≫ ({term})'
        measured = f'def result : (F{depth} A).family ≅ A.family := {term}\nend Examples.NestedRecovery\n'
    # The wrapper disables maxHeartbeats; an inner option restores the requested limit.
    # Setup has ordinary defaults so a tiny measured budget still reaches the probe.
    setup = setup.replace('import Examples.CubicalFiniteStateIdentity',
                          'import Examples.CubicalFiniteStateIdentity\nimport Mathlib.Util.CountHeartbeats\nset_option Elab.async false')
    return setup + f'#count_heartbeats in\nset_option maxRecDepth {recursion} in\nset_option maxHeartbeats {heartbeats} in\n' + measured


def run(workspace, text, timeout):
    with tempfile.TemporaryDirectory(prefix='representable-cost-') as tmp:
        path = Path(tmp) / 'Probe.lean'
        path.write_text(text)
        start = time.perf_counter()
        p = subprocess.Popen(['lake', 'env', 'lean', str(path)], cwd=workspace,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             start_new_session=True)
        try:
            output, _ = p.communicate(timeout=timeout)
            code = p.returncode
            if code == 0:
                status = 'pass'
            elif 'maximum recursion depth' in output:
                status = 'recursion'
            elif 'maximum number of heartbeats' in output:
                status = 'heartbeats'
            else:
                status = 'error'
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            output, _ = p.communicate()
            code, status = p.returncode, 'timeout'
        elapsed = time.perf_counter() - start
        counts = re.findall(r'Used (\d+) heartbeats', output)
        if status == 'pass' and len(counts) != 1:
            status = 'missing_measurement'
        return {'status': status, 'returncode': code, 'wall_seconds': elapsed,
                'heartbeats': int(counts[-1]) if counts else None,
                'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
                'diagnostics': output.replace(str(path), 'Probe.lean')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', action='append', required=True, help='label=path')
    parser.add_argument('--depths', default='0,2,4,8,16')
    parser.add_argument('--budgets', default='512:200000,1024:200000,2048:800000')
    parser.add_argument('--probes', default='nested,regression')
    parser.add_argument('--repeats', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    depths = [int(d) for d in args.depths.split(',')]
    budgets = [tuple(map(int, b.split(':'))) for b in args.budgets.split(',')]
    probes = args.probes.split(',')
    if (args.repeats < 1 or args.timeout <= 0 or min(depths) < 0 or
            any(len(b) != 2 or min(b) <= 0 for b in budgets) or
            not set(probes) <= {'nested', 'regression'}):
        parser.error('use nonnegative depths, positive finite budgets/repeats/timeout, and known probes')
    workspaces = []
    for item in args.workspace:
        label, path = item.split('=', 1)
        workspaces.append((label, Path(path).resolve()))
    if len({label for label, _ in workspaces}) != len(workspaces):
        parser.error('workspace labels must be distinct')
    report = {'time_utc': datetime.now(timezone.utc).isoformat(),
              'host': platform.uname()._asdict(), 'workspaces': {}, 'results': [],
              'settings': vars(args) | {'output': str(args.output)},
              'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    # Build all closures before starting any timed measurements.
    for label, workspace in workspaces:
        before = identity(workspace)
        subprocess.run(['lake', 'build', 'Examples.CubicalFiniteStateIdentity',
                        'Mathlib.Util.CountHeartbeats'], cwd=workspace, check=True,
                       stdout=subprocess.DEVNULL)
        if identity(workspace) != before:
            raise RuntimeError(f'inputs changed during build: {label}')
        report['workspaces'][label] = before
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for label, workspace in workspaces:
        for probe in probes:
            for depth in depths if probe == 'nested' else [None]:
                for recursion, heartbeats in budgets:
                    for repeat in range(args.repeats):
                        row = {'workspace': label, 'probe': probe, 'depth': depth,
                               'maxRecDepth': recursion, 'maxHeartbeats': heartbeats, 'repeat': repeat}
                        row.update(run(workspace, source(probe, depth, recursion, heartbeats), args.timeout))
                        report['results'].append(row)
                        args.output.write_text(json.dumps(report, indent=2) + '\n')
                        print(label, probe, depth, recursion, heartbeats, row['status'], row['heartbeats'], flush=True)
        if identity(workspace) != report['workspaces'][label]:
            raise RuntimeError(f'inputs changed during measurement: {label}')
    report['inputs_verified_after'] = True
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Bounded fresh reproduction of one preserved #137 source selection.

Invoke through direnv. The caller owns the shared build lock. --prepare-only
checks and extracts source evidence, but never claims compilation or acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARCHIVE = ROOT / 'docs/history/algorithm-design-haskell/checkpoint-233.zip'
ARCHIVE_SHA = '8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63'
COMPILER_COMMIT = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
GATE = 'next-iteration/restricted-nat-checker/gate/source-manifest.json'
SHARED = ROOT / 'experiments/relative-graph'
# Reuse the existing bounded command executor and source-policy scanner.
spec = importlib.util.spec_from_file_location('isolated_acceptance', SHARED / 'reproduce-acceptance.py')
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_inverse(archive, rows):
    bridge = json.loads(archive.read(GATE))['scoped_original_source_bridge']
    original = archive.read(bridge['original']['path'])
    if hashlib.sha256(original).hexdigest() != bridge['original']['sha256']:
        raise RuntimeError('Original counting source hash mismatch')
    selected = next(r for r in rows if r['module'] == 'ADWH.Chapter15.QueensBitCounting')
    restored = archive.read(selected['member']).decode()
    for edit in reversed(bridge['source_edits']):
        start, end = edit['new_character_start'], edit['new_character_end']
        if restored[start:end] != edit['new']:
            raise RuntimeError('Scoped inverse edit does not match selected source')
        restored = restored[:start] + edit['old'] + restored[end:]
    if restored.encode() != original:
        raise RuntimeError('Scoped inverse does not restore exact original bytes')
    if hashlib.sha256(restored.encode()).hexdigest() != bridge['exact_inverse_sha256']:
        raise RuntimeError('Scoped inverse digest mismatch')
    return True


def verify_reflection_correction(archive):
    correction = json.loads(archive.read(
        'next-iteration/reflection-proof-corrections/PROOF-CORRECTION.json'))
    text = archive.read(correction['original']['path']).decode()
    for edit in correction['exact_source_edits']:
        if hashlib.sha256(text.encode()).hexdigest() != edit['stage_before_identity']['sha256']:
            raise RuntimeError('Reflection correction predecessor mismatch')
        if text.count(edit['before']) != 1:
            raise RuntimeError('Reflection correction is not unique')
        text = text.replace(edit['before'], edit['after'])
        if hashlib.sha256(text.encode()).hexdigest() != edit['stage_after_identity']['sha256']:
            raise RuntimeError('Reflection correction successor mismatch')
    if text.encode() != archive.read(correction['candidate']['path']):
        raise RuntimeError('Reflection correction does not reproduce candidate')
    return True


def selection_file(selection):
    return HERE / ('selection.json' if selection == 'checker' else f'selection-{selection}.json')


def prepare(out, archive_path, profile):
    if sha(archive_path) != ARCHIVE_SHA:
        raise RuntimeError('Archive hash mismatch')
    out.mkdir()  # Refuse existing output directories, including stale receipts.
    source = out / 'source'
    source.mkdir()
    selection = json.loads(selection_file(profile).read_text())
    rows = selection['sources']
    names = [r['module'] for r in rows]
    if names != selection['order'] or len(set(names)) != len(names):
        raise RuntimeError('Selection must give unique modules in compilation order')
    with zipfile.ZipFile(archive_path) as archive:
        inverse = verify_inverse(archive, rows)
        correction = verify_reflection_correction(archive) if profile != 'checker' else None
        seen = set()
        for row in rows:
            name = row['module']
            if any(not part.isidentifier() for part in name.split('.')):
                raise RuntimeError(f'Invalid module name: {name}')
            content = archive.read(row['member'])
            if hashlib.sha256(content).hexdigest() != row['sha256']:
                raise RuntimeError(f'Selected source hash mismatch: {name}')
            path = source.joinpath(*name.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
            deps = shared.imports(path)
            if deps != row['imports']:
                raise RuntimeError(f'Import inventory mismatch: {name}')
            for dep in deps:
                if dep not in seen and dep != 'Init' and dep != 'Std' and not dep.startswith(('Init.', 'Std.', 'Lean.')):
                    raise RuntimeError(f'Import missing or out of order: {name} imports {dep}')
            if shared.FORBIDDEN.search(shared.executable_source(content.decode())):
                raise RuntimeError(f'Forbidden source construct: {name}')
            seen.add(name)
    return {'complete': False, 'archive_sha256': ARCHIVE_SHA, 'selected': rows,
            'inverse_correspondence': inverse, 'selection': profile,
            'reflection_correction': correction}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--archive', type=Path, default=ARCHIVE)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--selection', choices=['checker', 'comparison', 'native'], default='checker')
    args = parser.parse_args()
    out = args.out.resolve()
    if out == ROOT or ROOT in out.parents:
        raise RuntimeError('Output must be outside the checkout')
    receipt = prepare(out, args.archive, args.selection)
    receipt_path = out / 'provenance.json'
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    if args.prepare_only:
        print('Prepared verified sources and exact inverse correspondence; no build performed.')
        return
    try:
        candidate = shared.clean_commit(ROOT)
        local_clients = [] if args.selection == 'native' else ['Squares', 'CheckerClient'] + (['ReflectionClient'] if args.selection == 'comparison' else [])
        inputs = [selection_file(args.selection), HERE / 'reproduce.py', HERE / 'CheckerClient.lean',
                  SHARED / 'reproduce-acceptance.py', SHARED / 'ClosureAudit.lean',
                  ROOT / 'scripts/check.py', ROOT / 'Squares.lean', ROOT / 'lean-toolchain',
                  ROOT / 'flake.nix', ROOT / 'flake.lock']
        if args.selection == 'native':
            inputs.append(HERE / 'native.py')
        if args.selection == 'comparison':
            inputs.append(HERE / 'ReflectionClient.lean')
        tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0'))
        for path in inputs:
            if str(path.relative_to(ROOT)) not in tracked:
                raise RuntimeError(f'Untracked validation input: {path}')
        identities = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
        lean = Path(subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()).resolve()
        env = dict(os.environ, LEAN=str(lean), LEAN_NUM_THREADS='1', LEAN_PATH=str(out / 'output'))
        version = shared.compiler_version(True, env)
        commit = subprocess.check_output([str(lean), '--githash'], text=True).strip()
        if commit != COMPILER_COMMIT:
            raise RuntimeError(f'Compiler commit mismatch: {commit}')
        compiler_hash = sha(lean)
        receipt.update(candidate=candidate, inputs=identities, compiler={'path': str(lean),
            'version': version, 'commit': commit, 'sha256': compiler_hash},
            limits={'virtual_address_gib': 8, 'seconds_per_process': 120,
                    'total_seconds': 1200, 'compiler_processes': 1, 'threads': 1})
        source, output = out / 'source', out / 'output'
        output.mkdir()
        local_sources = {name: (ROOT if name == 'Squares' else HERE) / f'{name}.lean'
                         for name in local_clients}
        local_sources['ClosureAudit'] = SHARED / 'ClosureAudit.lean'
        for name, original in local_sources.items():
            (source / f'{name}.lean').write_bytes(original.read_bytes())
        names = [r['module'] for r in receipt['selected']] + local_clients
        for name in local_clients:
            if shared.FORBIDDEN.search(shared.executable_source((source / f'{name}.lean').read_text())):
                raise RuntimeError(f'Forbidden local source construct: {name}')
        audit = '\n'.join('import ' + name for name in names + ['ClosureAudit'])
        audit += '\n#audit_closure [' + ', '.join(names) + '] local [' + ', '.join(names) + ']\n'
        (source / 'SelectionAudit.lean').write_text(audit)
        source_hashes = {str(p.relative_to(source)): sha(p) for p in source.rglob('*.lean')}
        commands = shared.Commands(out / 'logs', env)
        start = time.monotonic()
        for name in names + ['ClosureAudit', 'SelectionAudit']:
            relative = Path(*name.split('.'))
            target = (output / relative).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            remaining = 1200 - (time.monotonic() - start)
            if remaining <= 0:
                raise RuntimeError('Total 20-minute time limit')
            commands.run(name, [sys.executable, str(HERE / 'reproduce.py'), '--exec-limited',
                str(lean), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                '-DElab.async=false', '-R', str(source), '-o', str(target),
                str((source / relative).with_suffix('.lean'))], source, timeout=min(120, remaining))
        if args.selection == 'native':
            import native
            receipt['native'] = native.reproduce(lean, source, output, receipt['selected'], commands, start)
        if shared.clean_commit(ROOT) != candidate or any(sha(ROOT / p) != h for p, h in identities.items()):
            raise RuntimeError('Candidate inputs changed during reproduction')
        if sha(args.archive) != ARCHIVE_SHA or sha(lean) != compiler_hash or shared.compiler_version(True, env) != version:
            raise RuntimeError('Archive or compiler changed during reproduction')
        if any(sha(source / p) != h for p, h in source_hashes.items()):
            raise RuntimeError('Staged source changed during reproduction')
        receipt.update(complete=True, source_hashes=source_hashes,
            outputs={str(p.relative_to(output)): sha(p) for p in output.rglob('*') if p.is_file()},
            elapsed_seconds=time.monotonic() - start,
            peak_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    except Exception as error:
        receipt['failure'] = str(error)
        raise
    finally:
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--exec-limited':
        resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
        # One CPU is enough; retain portability to hosts without sched affinity.
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
        os.execv(sys.argv[2], sys.argv[2:])
    try:
        main()
    except Exception as error:
        print(f'Reproduction FAILED: {error}', file=sys.stderr)
        sys.exit(1)

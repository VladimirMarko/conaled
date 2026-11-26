#!/usr/bin/env python3
"""Fresh isolated source-closure check using the repository compiler and audit."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import check

spec = importlib.util.spec_from_file_location(
    'isolated_acceptance', ROOT / 'experiments/relative-graph/reproduce-acceptance.py')
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['LEAN'] = lean
    version = check.compiler_version(True, env)
    print(version, flush=True)
    sources = {'Contracts': ROOT / 'experiments/host-target/Contracts.lean'}
    dependencies = {}
    pending = ['Contracts']
    while pending:
        headers = shared.source_imports([sources[name] for name in pending])
        following = []
        for name, imports in zip(pending, headers, strict=True):
            local = []
            for imported in imports:
                path = ROOT / (imported.replace('.', '/') + '.lean')
                if path.is_file():
                    if imported not in sources:
                        sources[imported] = path
                        following.append(imported)
                    local.append(imported)
                elif not (imported in ('Init', 'Lean') or imported.startswith('Lean.')):
                    raise RuntimeError(f'Unexpected external dependency: {imported}')
            dependencies[name] = local
        pending = following
    order, finished, visiting = [], set(), set()

    def visit(name):
        if name in finished:
            return
        if name in visiting:
            raise RuntimeError(f'Import cycle: {name}')
        visiting.add(name)
        for imported in dependencies[name]:
            visit(imported)
        visiting.remove(name)
        finished.add(name)
        order.append(name)

    visit('Contracts')
    audit = ROOT / 'experiments/relative-graph/ArtifactAudit.lean'
    inputs = [*sources.values(), audit, Path(__file__), Path(shared.__file__),
              *shared.SOURCE_CHECK_INPUTS]
    identities = shared.hashes(inputs)
    print('Source inputs: ' + json.dumps(identities, sort_keys=True), flush=True)
    with tempfile.TemporaryDirectory(prefix='conaled-host-target-') as directory:
        root = Path(directory)
        # Audit every current-module safe declaration, including private roots,
        # and traverse its axiom dependencies.
        (root / 'ArtifactAudit.lean').write_bytes(audit.read_bytes())
        modules = {'ArtifactAudit': root / 'ArtifactAudit.lean'}
        for name, source in sources.items():
            target = root / (name.replace('.', '/') + '.lean')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('import ArtifactAudit\n' + source.read_text() + '\n#audit_graph_module\n')
            modules[name] = target
            dependencies[name].append('ArtifactAudit')
        dependencies['ArtifactAudit'] = []
        output = root / 'build'
        output.mkdir()
        env['LEAN_PATH'] = str(output)
        check.ROOT = root
        try:
            check.compile_modules(modules, dependencies, ['ArtifactAudit', *order],
                                  lean, env, output, args.jobs)
        finally:
            check.ROOT = ROOT
    if shared.hashes(inputs) != identities:
        raise RuntimeError('Source or validation inputs changed during compilation')
    if check.compiler_version(True, env) != version:
        raise RuntimeError('Compiler changed during compilation')
    print(f'PASS: {len(modules)} freshly compiled modules; exhaustive per-module audits; {args.jobs} workers.')


if __name__ == '__main__':
    main()

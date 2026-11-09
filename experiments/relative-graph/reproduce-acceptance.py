#!/usr/bin/env python3
"""Fresh isolated #135 acceptance (invoke through direnv, under the build lock).

--plan only inventories sources; it is not validation. A real run requires a
clean committed candidate and a new output directory. External package outputs
may be reused; native, graph and selected ConLeche outputs are rebuilt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check import executable_source, FORBIDDEN, candidate_identity, compiler_version, clean_commit

PIN = '8e166ca53cd1f864b63c13cc1d326d38316d00ea'
IMPORT = re.compile(r'^[ \t]*(?:(?:public|meta)\s+)*import[ \t]+([^\n]+)', re.MULTILINE)
DIAGNOSTICS = {'Lean4LeanAudit', 'ConLecheAudit'}


def imports(path):
    return [item for match in IMPORT.finditer(executable_source(path.read_text()))
            for item in match.group(1).split()]


def inventory():
    graph = {p.stem: p for p in HERE.glob('*.lean') if p.stem not in DIAGNOSTICS}
    sources = dict(graph)
    native = set()
    upstream = {'ConLeche.MainTheorem'}
    order, finished, visiting = [], set(), set()

    def visit(name):
        if name in finished:
            return
        if name in visiting:
            raise RuntimeError(f'Import cycle: {name}')
        visiting.add(name)
        path = sources[name]
        for dep in imports(path):
            if dep.startswith('ConLeche.'):
                upstream.add(dep)
                continue
            local = ROOT.joinpath(*dep.split('.')).with_suffix('.lean')
            if dep not in sources and local.is_file():
                sources[dep] = local
                native.add(dep)
            if dep in sources:
                visit(dep)
            elif dep.startswith(('SquareKit.', 'Applications.', 'Examples.')):
                raise RuntimeError(f'Missing local source: {dep}')
        visiting.remove(name)
        finished.add(name)
        order.append(name)

    for name in sorted(graph):
        visit(name)
    return sources, {'graph': [n for n in order if n in graph],
                     'native': [n for n in order if n in native],
                     'upstream_targets': sorted(upstream)}


def output(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def hashes(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths))}


class Commands:
    """Fail closed on process errors, time limits and diagnostic overflow."""
    def __init__(self, directory, env):
        self.directory, self.env, self.records = directory, env, []
        directory.mkdir()

    def run(self, label, args, cwd, timeout=120, cap=1024 * 1024):
        start = time.monotonic()
        record = {'label': label, 'args': [str(a) for a in args], 'cwd': str(cwd),
                  'timeout_seconds': timeout, 'output_cap_bytes': cap}
        data = bytearray()
        with subprocess.Popen(args, cwd=cwd, env=self.env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, start_new_session=True) as process:
            selector = selectors.DefaultSelector()
            selector.register(process.stdout, selectors.EVENT_READ)
            failure = None
            while selector.get_map():
                if time.monotonic() - start > timeout:
                    failure = 'timeout'
                    break
                for key, _ in selector.select(timeout=0.2):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                    else:
                        remaining = cap - len(data)
                        data.extend(chunk[:remaining])
                        if len(chunk) > remaining:
                            failure = 'output-limit'
                            break
                if failure:
                    break
            selector.close()
            if failure:
                os.killpg(process.pid, signal.SIGKILL)
            try:
                code = process.wait(timeout=max(0.001, timeout - (time.monotonic() - start)))
            except subprocess.TimeoutExpired:
                failure = 'timeout'
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
        record.update(exit=code, failure=failure, wall_seconds=time.monotonic() - start,
                      retained_output_bytes=len(data))
        (self.directory / (label + '.log')).write_bytes(data)
        self.records.append(record)
        (self.directory / 'commands.json').write_text(json.dumps(self.records, indent=2) + '\n')
        print(f'{label}: exit {code}, {record["wall_seconds"]:.2f}s', flush=True)
        if code or failure:
            raise RuntimeError(f'{label} failed ({failure or code}); see {self.directory / (label + ".log")}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', action='store_true')
    parser.add_argument('--run-dir', type=Path)
    args = parser.parse_args()
    if args.run_dir and args.run_dir.exists():
        parser.error('--run-dir must not exist; fresh outputs are required')
    sources, plan = inventory()
    if args.plan:
        print(json.dumps(plan, indent=2))
        return
    if args.run_dir is None:
        parser.error('--run-dir is required unless --plan is used')
    identity = candidate_identity('HEAD')
    candidate = identity['candidate']
    tracked = set(output(['git', 'ls-files']).splitlines())
    if any(str(p.relative_to(ROOT)) not in tracked for p in sources.values()):
        raise RuntimeError('Every isolated source must be tracked in the candidate')
    for name, source in sources.items():
        bad = FORBIDDEN.search(executable_source(source.read_text()))
        if bad:
            raise RuntimeError(f'Forbidden source construct in {name}: {bad.group()}')
    inputs = hashes([*sources.values(), Path(__file__), HERE / 'test-reproduce-acceptance.py',
                     ROOT / 'scripts/check.py', ROOT / 'scripts/lake_integrity.py',
                     ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json', ROOT / 'flake.lock'])
    run = args.run_dir.resolve()
    run.mkdir(parents=True)
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['LAKE_ARTIFACT_CACHE'] = 'false'
    env['LEAN_NUM_THREADS'] = '2'
    commands = Commands(run / 'logs', env)
    lean = output(['elan', 'which', 'lean'])
    env['LEAN'] = lean
    compiler = compiler_version(True, env)
    lake = str(Path(lean).with_name('lake'))
    upstream = run / 'con-leche'
    provenance = {'candidate': candidate, 'source_hashes': inputs, 'plan': plan,
                  'lean': lean, 'compiler': compiler, 'upstream_pin': PIN,
                  'candidate_identity': identity,
                  'external_outputs_reused': True, 'lean_num_threads': 2, 'complete': False}
    manifest = run / 'provenance.json'
    manifest.write_text(json.dumps(provenance, indent=2) + '\n')
    commands.run('clone', ['git', 'clone', '--quiet', 'https://github.com/leanprover/con-leche', str(upstream)], ROOT, 300)
    commands.run('pin', ['git', 'checkout', '--quiet', '--detach', PIN], upstream)
    if output(['git', 'rev-parse', 'HEAD'], upstream) != PIN:
        raise RuntimeError('Upstream pin mismatch')
    if (upstream / 'lean-toolchain').read_text() != (ROOT / 'lean-toolchain').read_text():
        raise RuntimeError('Native and upstream toolchains differ')
    commands.run('upstream-build', [lake, '--no-cache', '--rehash', 'build',
                                  *['+' + n for n in plan['upstream_targets']]], upstream,
                 timeout=7200, cap=16 * 1024 * 1024)
    upstream_out = upstream / '.lake/build/lib/lean'
    upstream_modules = sorted('.'.join(p.relative_to(upstream_out).with_suffix('').parts)
                              for p in upstream_out.rglob('*.olean'))
    if not upstream_modules or any(not n.startswith('ConLeche.') for n in upstream_modules):
        raise RuntimeError('Unexpected or empty upstream output inventory')
    dependency_manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dependency_paths = [ROOT / dependency_manifest['packagesDir'] / p['name'] / '.lake/build/lib/lean'
                        for p in dependency_manifest['packages']]
    absent_outputs = [package['name'] for package, path in zip(dependency_manifest['packages'], dependency_paths)
                      if not path.is_dir()]
    dependency_paths = [path for path in dependency_paths if path.is_dir()]
    if not (ROOT / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib').is_dir():
        raise RuntimeError('External package outputs missing; run lake exe cache get first')
    native_out, graph_out = run / 'native', run / 'graph'
    native_out.mkdir()
    graph_out.mkdir()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [graph_out, native_out, upstream_out, *dependency_paths]))
    provenance.update(lean_path=env['LEAN_PATH'], upstream_modules=upstream_modules,
                      manifest_packages_without_outputs=absent_outputs,
                      upstream_manifest=json.loads((upstream / 'lake-manifest.json').read_text()))
    manifest.write_text(json.dumps(provenance, indent=2) + '\n')
    for kind, dest, source_root in [('native', native_out, ROOT), ('graph', graph_out, HERE)]:
        for name in plan[kind]:
            target = dest.joinpath(*name.split('.')).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            commands.run(kind + '-' + name, [lean, '-D', 'Elab.async=false', '-R', str(source_root),
                         '-o', str(target), str(sources[name])], ROOT)
    all_modules = [*upstream_modules, *plan['native'], *plan['graph']]
    local_modules = [*plan['native'], *plan['graph']]
    audit = run / 'AcceptanceAudit.lean'
    audit.write_text('\n'.join('import ' + name for name in all_modules) +
                     '\n#audit_closure [' + ', '.join(all_modules) + '] local [' +
                     ', '.join(local_modules) + ']\n')
    commands.run('closure-audit', [lean, '-D', 'Elab.async=false', str(audit)], ROOT, 600)
    if inputs != hashes(ROOT / p for p in inputs):
        raise RuntimeError('Candidate source changed during acceptance')
    if candidate_identity(candidate) != identity or compiler_version(True, env) != compiler:
        raise RuntimeError('Candidate, dependency or compiler identity changed during acceptance')
    if clean_commit(upstream) != PIN:
        raise RuntimeError('Upstream source changed during acceptance')
    provenance['complete'] = True
    manifest.write_text(json.dumps(provenance, indent=2) + '\n')
    print(f'Isolated acceptance PASSED: {candidate}; evidence {run}', flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'Acceptance FAILED: {error}', file=sys.stderr)
        sys.exit(1)

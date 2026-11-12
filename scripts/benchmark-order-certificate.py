#!/usr/bin/env python3
"""Fresh bounded checker build/audit, runtime observation, and kernel proof timings.

Run with direnv exec . python3 scripts/benchmark-order-certificate.py.
Each Lean process has CPU/wall limits and Lean's memory limit. Retains inputs/logs.
"""
from pathlib import Path
import hashlib
import json
import os
import sys
import tempfile
import time

from measurement import Limits, host_identity, publish, run_attempt, source_identity
from project_sources import inventory, SOURCE_TREES

ROOT = Path(__file__).resolve().parents[1]
LIMIT_SECONDS = 60
LIMIT_BYTES = 4 * 1024**3
CAPS = Limits(wall=LIMIT_SECONDS, cpu=(LIMIT_SECONDS, LIMIT_SECONDS))


def runtime_output(text):
    rows = []
    expected = [(algorithm, size) for size in (64, 256, 1024)
                for algorithm in ('reference', 'adjacent')]
    for line, (algorithm, size) in zip(text.splitlines(), expected, strict=True):
        fields = line.split()
        if len(fields) != 5 or fields[0] != algorithm:
            raise ValueError('malformed checker runtime output')
        row = dict(item.split('=', 1) for item in fields[1:])
        if set(row) != {'n', 'repeats', 'accepted', 'ns'}:
            raise ValueError('missing checker measurement')
        if row['n'] != str(size) or row['repeats'] != '20' or row['accepted'] != '20':
            raise ValueError('unexpected checker workload/result')
        if not row['ns'].isascii() or not row['ns'].isdigit():
            raise ValueError('invalid checker timing')
        rows.append(dict(algorithm=algorithm, **row))
    return rows


def execute(work, records):
    output = work/'out'
    output.mkdir()
    (work/'attempts').mkdir()
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    records.update(host_identity())
    records['cpu'] = next((line.split(':', 1)[1].strip()
                           for line in (records['cpuinfo'] or '').splitlines()
                           if line.startswith('model name')), None)
    records.update(seconds_per_process=LIMIT_SECONDS, lean_memory_limit_mib=LIMIT_BYTES//1024**2)
    modules = inventory(ROOT)
    names = [str(path.relative_to(ROOT)) for path in modules.values()]
    names += ['scripts/benchmark-order-certificate.py', 'scripts/measurement.py',
              'scripts/lean-source-info.lean', 'scripts/project_sources.py',
              'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'flake.lock']
    records['inputs'] = source_identity(ROOT, names)
    records['manifest_sha256'] = records['inputs']['lake-manifest.json']
    records['environment'] = {'PATH': env.get('PATH'), 'LEAN_PATH': 'removed pending Lake resolution'}

    def save():
        receipt = publish(work/'results.json', records)
        if receipt['publication'] != 'confirmed':
            raise OSError('result publication failed: ' + receipt.get('recording_error', 'unknown'))

    def command(name, argv, phase, cwd=work):
        record = run_attempt(argv, cwd=cwd, prefix=work/'attempts'/name,
                             limits=CAPS, env=env, metadata={'name': name, 'phase': phase})
        record['seconds'] = record.get('wall_seconds')
        records['runs'].append(record)
        save()
        if record['publication'] != 'confirmed' or not record['success']:
            raise RuntimeError(f'{name}: {record["status"]}; see {work/"attempts"}')
        with (work/f'{name}.log').open('x') as log:
            log.write(record['stdout'] + record['stderr'])
        print(f'{name}: {record["seconds"]:.4f}s, exit {record["returncode"]}', flush=True)
        return record['stdout']

    def run(name, args, phase):
        return command(name, ['lean', '-j2', '-M4096', *args], phase)

    def write_source(name, text):
        destination = work/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
        records['sources'][name] = hashlib.sha256(destination.read_bytes()).hexdigest()

    records['version'] = command('compiler', ['lean', '--version'], 'toolchain', ROOT).strip()
    expected = (ROOT/'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
    if f'version {expected},' not in records['version']:
        raise RuntimeError('compiler differs from lean-toolchain')
    manifest = work/'source-manifest.json'
    manifest.write_text(json.dumps([str(path.relative_to(ROOT)) for path in modules.values()]))
    imports = json.loads(command('source-preflight', ['lean', '--run', 'scripts/lean-source-info.lean',
                                                     str(manifest)], 'source preflight', ROOT))
    if not isinstance(imports, list) or len(imports) != len(modules):
        raise ValueError('invalid native import response')
    dependencies = dict(zip(modules, imports, strict=True))
    order, visiting, finished = [], set(), set()

    def visit(name):
        if name in finished:
            return
        if name in visiting:
            raise ValueError('cyclic local imports')
        visiting.add(name)
        if not isinstance(dependencies[name], list):
            raise ValueError('invalid native imports')
        for dependency in dependencies[name]:
            if not isinstance(dependency, str):
                raise ValueError('invalid native import name')
            if dependency in modules:
                visit(dependency)
            elif dependency.startswith(tuple(tree+'.' for tree in SOURCE_TREES)):
                raise ValueError('missing local source: '+dependency)
        visiting.remove(name)
        finished.add(name)
        order.append(name)

    visit('Examples.OrderCertificate')
    lake_paths = command('dependency-paths', ['lake', 'env', 'printenv', 'LEAN_PATH'],
                         'dependency environment', ROOT).strip()
    dependency_paths = []
    for entry in lake_paths.split(os.pathsep):
        if entry:
            path = Path(entry)
            if not path.is_absolute():
                path = ROOT/path
            if path.resolve() != (ROOT/'.lake/build/lib/lean').resolve():
                dependency_paths.append(str(path.resolve()))
    env['LEAN_PATH'] = os.pathsep.join([str(output), *dependency_paths])
    records['environment']['LEAN_PATH'] = env['LEAN_PATH']
    for module in order:
        source = modules[module].relative_to(ROOT)
        data = (ROOT/source).read_bytes()
        if hashlib.sha256(data).hexdigest() != records['inputs'][str(source)]:
            raise RuntimeError('source changed before capture: '+str(source))
        target = work/source
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        records['sources'][str(source)] = hashlib.sha256(data).hexdigest()
        artifact = output/source.with_suffix('.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run(module, ['-o', str(artifact), str(source)], 'build')
    write_source('scripts/project_sources.py', (ROOT/'scripts/project_sources.py').read_text())
    audit = (ROOT/'ProofAudit.lean').read_text()
    if audit.count('import SquareApplications\n') != 1:
        raise ValueError('unsupported audit import layout')
    write_source('ProofAudit.lean', audit.replace('import SquareApplications\n',
                                               'import Examples.OrderCertificate\n', 1))
    run('audit', ['-o', str(output/'ProofAudit.olean'), 'ProofAudit.lean'], 'audit')
    header = "import Examples.OrderCertificate\nopen OrderCertificate Examples.OrderCertificate\n"
    write_source("Baseline.lean", header)
    run("import-baseline", ["Baseline.lean"], "import baseline")
    for size in (64, 256):
        for algorithm in ("reference", "adjacent"):
            proof = "" if algorithm == "reference" else "  rw [← refinement lt_law]\n"
            source = ("import ProofAudit\n" + header + "set_option maxHeartbeats 10000000\n"
                      "set_option maxRecDepth 100000\n"
                      f"theorem certificate : (List.range {size}).Pairwise (· < ·) := by\n"
                      "  apply (reference_correct lt_law _).mp\n" + proof +
                      "  decide +kernel\n#print axioms certificate\n#audit_project_axioms\n")
            name = f"Proof_{algorithm}_{size}"
            write_source(f"Examples/{name}.lean", source)
            run(name, [f"Examples/{name}.lean"], "kernel checking")

    runtime = header + '''
def main : IO Unit := do
  for n in [64, 256, 1024] do
    for (name, checker) in [("reference", reference ltCmp), ("adjacent", adjacent ltCmp)] do
      let start ← IO.monoNanosNow
      let mut accepted := 0
      for offset in [:20] do
        -- Vary the input to avoid timing repeated calls on one constant expression.
        let xs := (List.range n).map (· + offset)
        if checker xs then accepted := accepted + 1
      let elapsed := (← IO.monoNanosNow) - start
      if accepted != 20 then throw (IO.userError "unexpected rejection")
      IO.println s!"{name} n={n} repeats=20 accepted={accepted} ns={elapsed}"
'''
    write_source("Runtime.lean", runtime)
    observed = run("runtime", ["--run", "Runtime.lean"], "execution")
    try:
        records['measurements'] = runtime_output(observed)
    except ValueError:
        records['status'] = 'malformed_output'
        raise
    if source_identity(ROOT, names) != records['inputs']:
        records['status'] = 'input_changed'
        raise RuntimeError('source identity changed during benchmark')
    print(observed, end='')


def main():
    started = time.monotonic()
    work = None
    records = {'status': 'started', 'sources': {}, 'runs': [], 'success': False}
    try:
        (ROOT/'.lake').mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix='order-certificate-', dir=ROOT/'.lake'))
        print(f'Evidence: {work}', flush=True)
        initial = publish(work/'results.json', records)
        if initial['publication'] != 'confirmed':
            raise OSError('initial result publication failed')
        execute(work, records)
        records.update(status='exited', returncode=0, cleanup='confirmed', output='complete')
    except (OSError, ValueError, KeyError, RuntimeError, KeyboardInterrupt) as error:
        records.update(status=records['status'] if records['status'] != 'started' else 'failed',
                       error=str(error), success=False)
    records['orchestration_wall_seconds'] = time.monotonic()-started
    receipt = publish(work/'results.json', records) if work is not None else records
    if not receipt.get('success'):
        print(json.dumps(receipt), file=sys.stderr)
        return 1
    print('PASS: fresh closure/audit and bounded measurements; runtime is not proof evidence.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

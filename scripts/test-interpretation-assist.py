#!/usr/bin/env python3
"""Real CLI/checker tests. All attempts remain in the required output directory."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=False)
results = []


def run(name, route, status, *extra):
    out = a.out / name
    cmd = [sys.executable, str(ROOT / 'scripts/interpretation-assist.py'), route, '--out', str(out), *extra]
    result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    (a.out / (name + '.stdout')).write_text(result.stdout + result.stderr)
    receipt = json.loads((out / 'receipt.json').read_text())
    assert receipt['status'] == status, (name, receipt['status'], receipt['detail'])
    assert result.returncode == (0 if status == 'checked' else 2), name
    results.append({'name': name, 'status': status, 'checks': len(receipt['checks'])})
    return receipt


run('composition', 'composition', 'checked')
run('missing', 'extension', 'missing evidence', '--omit', 'extension')
run('wrong-type', 'extension', 'rejected evidence', '--certificate', 'extension=True.intro')
run('omitted', 'omitted', 'refuted obligation')
run('image', 'image', 'checked')
run('erasure', 'erasure', 'refuted obligation')
run('resource', 'resource', 'checked')
run('exhausted', 'not-registered', 'registry exhausted')

registry = json.loads((ROOT / 'experiments/interpretation-assistance/registry.json').read_text())
registry['routes']['axiom'] = dict(registry['routes']['extension'], certificates={'extension': 'by sorry'})
registry['routes']['unavailable'] = dict(registry['routes']['extension'], imports=['NonexistentPrototypeModule'])
registry_path = a.out / 'negative-registry.json'
registry_path.write_text(json.dumps(registry))
run('forbidden-certificate', 'axiom', 'rejected evidence', '--registry', str(registry_path))
run('unavailable', 'unavailable', 'checker failure', '--registry', str(registry_path))

# A valid result must not hide an unused private axiom in the current module.
source = a.out / 'private-root.lean'
source.write_text('import SquareKit.InterpretationDiagnostics\nnamespace Fixture\n'
                  'private axiom hidden : True\n'
                  'theorem result : True := True.intro\n'
                  '#transport_audit Fixture.result\nend Fixture\n')
proc = subprocess.run(['lake', 'env', 'lean', str(source.resolve())], cwd=ROOT, text=True, capture_output=True)
(a.out / 'private-root.log').write_text(proc.stdout + proc.stderr)
assert proc.returncode != 0 and 'Forbidden axiom' in proc.stdout, proc.stdout
results.append({'name': 'unused-private-axiom', 'status': 'rejected', 'checks': 1})
(a.out / 'summary.json').write_text(json.dumps(results, indent=2) + '\n')
print(f'{len(results)} real checker/CLI cases passed; receipts in {a.out}')

# Both routes share a hard external counter; a denied invocation starts no Lean.
budget = a.out / 'budget' / 'state.json'
runner = ROOT / 'scripts/interpretation-trial-check.py'
subprocess.run([sys.executable, str(runner), '--state', str(budget), '--initialize', '--rounds', '1'], check=True)
good = a.out / 'budget-good.lean'
good.write_text('import SquareKit.InterpretationDiagnostics\n'
                'theorem result : True := True.intro\n#transport_audit result\n')
cmd = [sys.executable, str(runner), '--state', str(budget), '--source', str(good)]
first = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
second = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
assert first.returncode == 0 and second.returncode == 75
assert json.loads(budget.read_text())['count'] == 1
(a.out / 'budget-denied.log').write_text(second.stdout + second.stderr)

# A multi-phase CLI must stop before its next internal check at the same cap.
budget2 = a.out / 'budget-cli-state' / 'state.json'
subprocess.run([sys.executable, str(runner), '--state', str(budget2), '--initialize', '--rounds', '2'], check=True)
r = run('budget-cli', 'composition', 'budget exhausted', '--budget', str(budget2))
assert sum(c['checker_started'] for c in r['checks']) == 2
assert json.loads(budget2.read_text())['count'] == 2

# Deadline checks and coordinator cutoff snapshots are independent of the author.
expired = a.out / 'expired' / 'state.json'
subprocess.run([sys.executable, str(runner), '--state', str(expired), '--initialize', '--minutes', '0'], check=True)
proc = subprocess.run([sys.executable, str(runner), '--state', str(expired), '--source', str(good)], capture_output=True)
assert proc.returncode == 75 and json.loads(expired.read_text())['count'] == 0
workspace = a.out / 'cutoff-input'
workspace.mkdir()
(workspace / 'answer.lean').write_bytes(good.read_bytes())
subprocess.run([sys.executable, str(runner), '--state', str(expired), '--watch', str(workspace)], check=True)
assert (expired.parent / 'cutoff/answer.lean').read_bytes() == good.read_bytes()

# Author-supplied declarations are included and audited in every source snapshot.
support = a.out / 'support.lean'
support.write_text('theorem supplied : Examples.DiagonalCoverage.good.Extension '
                   'Examples.DiagonalConstruction.sourceSelected := Examples.DiagonalCoverage.good_extra\n')
run('support', 'missing', 'checked', '--support', str(support), '--certificate', 'extension=supplied')
(a.out / 'summary.json').write_text(json.dumps(results, indent=2)+'\n')
print('External budgets, cutoff snapshot and author-supplied certificate also passed.')

# Inject real process failures after a successful request check. A PATH launcher
# forwards to the real Lake/Lean; it never fabricates a successful checker result.
import os
import shutil
lake = shutil.which('lake')
for mode in ('infrastructure', 'terminated', 'runner'):
    fault = a.out / ('fault-' + mode)
    fault.mkdir()
    launcher = fault / 'lake'
    launcher.write_text(f'''#!{sys.executable}
import os, pathlib, signal, subprocess, sys, time
command = [{lake!r}, *sys.argv[1:]]
source = pathlib.Path(sys.argv[-1])
first = source.parent.name == 'round-001'
if first:
    proc = subprocess.run(command)
    if {mode!r} == 'infrastructure':
        pathlib.Path(__file__).chmod(0)
    if {mode!r} == 'runner':
        (source.parent.parent / 'state.json').write_text('invalid state')
    sys.exit(proc.returncode)
proc = subprocess.Popen(command, start_new_session=True)
time.sleep(0.1)
os.killpg(proc.pid, signal.SIGTERM)
proc.wait()
os.kill(os.getpid(), signal.SIGTERM)
''')
    launcher.chmod(0o755)
    state = fault / 'budget/state.json'
    subprocess.run([sys.executable, str(runner), '--state', str(state), '--initialize'], check=True)
    out = fault / 'request'
    for tool in ('lean', 'git', 'dirname'):
        (fault / tool).symlink_to(shutil.which(tool))
    env = dict(os.environ, PATH=str(fault.resolve()))
    proc = subprocess.run([sys.executable, str(ROOT / 'scripts/interpretation-assist.py'), 'extension',
                           '--out', str(out), '--budget', str(state)], cwd=ROOT, env=env,
                          capture_output=True, text=True)
    (fault / 'cli.log').write_text(proc.stdout + proc.stderr)
    receipt = json.loads((out / 'receipt.json').read_text())
    assert receipt['checks'][0]['exit'] == 0
    assert receipt['status'] == 'checker failure', receipt
    if mode == 'runner':
        assert receipt['checks'][-1]['exit'] == 1
    else:
        assert receipt['checks'][-1]['exit'] not in (0, 1, 75), receipt
    if mode == 'infrastructure':
        assert receipt['checks'][-1]['exit'] == 74
    results.append({'name': mode + '-during-certificate', 'status': receipt['status'], 'checks': len(receipt['checks'])})
(a.out / 'summary.json').write_text(json.dumps(results, indent=2)+'\n')
print('Actual infrastructure failure, terminated checker and broken runner remain checker failures.')

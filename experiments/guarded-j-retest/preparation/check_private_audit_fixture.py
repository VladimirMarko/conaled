"""Reject an unused forbidden axiom beside the exact private validation bodies."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess
import sys
import tempfile

repo = Path(__file__).resolve().parents[3]
prep = Path(__file__).resolve().parent
dest = prep / 'checks' / sys.argv[1]
dest.mkdir(parents=True, exist_ok=False)
module = repo / 'Examples/GuardedJRetestValidation.lean'
audit = repo / 'ProofAudit.lean'
module_source = module.read_text()
audit_source = audit.read_text()
imports, bodies = [], []
for source in [module_source, audit_source]:
    lines = source.splitlines()
    # Do not import the integrated copy of the same declarations into this fixture.
    imports.extend(line for line in lines if line.startswith('import ') and line != 'import SquareApplications')
    bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
source = '\n'.join(dict.fromkeys(imports)) + '\n' + bodies[0] + '\n' + \
    'axiom GuardedJRetest.AuditFixture.forbidden : False\n' + bodies[1] + '\n'
(dest / 'Forbidden.lean.txt').write_text(source)
record = {'start': datetime.now(timezone.utc).isoformat(),
          'module_source_sha256': sha256(module_source.encode()).hexdigest(),
          'audit_source_sha256': sha256(audit_source.encode()).hexdigest(),
          'fixture_source_sha256': sha256(source.encode()).hexdigest(),
          'expected': 'nonzero exit and forbidden-axiom diagnostic from recognized private validation module'}
with tempfile.TemporaryDirectory(prefix='guarded-j-audit-negative-') as directory:
    root = Path(directory)
    lean = root / 'Examples/GuardedJRetestValidationNegative.lean'
    lean.parent.mkdir()
    lean.write_text(source)
    command = ['lake', 'env', 'lean', '--root=' + str(root), str(lean)]
    record['command'] = command
    with (dest / 'stdout.log').open('wb') as stdout, (dest / 'stderr.log').open('wb') as stderr:
        result = subprocess.run(command, cwd=repo, stdout=stdout, stderr=stderr)
output = (dest / 'stdout.log').read_text()
counts = re.findall(r'  Examples\.GuardedJRetestValidationNegative: (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations', output)
covered = len(counts) == 1 and int(counts[0][0]) > 0
rejected = result.returncode != 0 and covered and \
    "Forbidden transitive axioms in 'GuardedJRetest.AuditFixture.forbidden'" in output
record.update(command_exit=result.returncode, expected_rejection_verified=rejected,
              finish=datetime.now(timezone.utc).isoformat())
if covered:
    record['audited_module_counts'] = dict(zip(['logical', 'theorem', 'unsafe_runtime'], map(int, counts[0])))
record['evidence_sha256'] = {p.name: sha256(p.read_bytes()).hexdigest() for p in sorted(dest.iterdir())}
(dest / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'archive': str(dest), 'expected_rejection_verified': rejected,
                  'command_exit': result.returncode}))
raise SystemExit(0 if rejected else 1)

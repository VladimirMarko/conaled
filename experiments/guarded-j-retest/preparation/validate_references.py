"""Check exact private reference/case sources, optionally with the project audit."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import time

repo = Path(__file__).resolve().parents[3]
prep = Path(__file__).resolve().parent
name = sys.argv[1]
audit = '--audit' in sys.argv[2:]
dest = prep / 'checks' / name
dest.mkdir(parents=True, exist_ok=False)
inputs = [prep / p for p in ['BaselineReference.lean', 'CandidateReference.lean', 'NativeCases.lean']]
if audit:
    inputs.append(repo / 'ProofAudit.lean')
imports, bodies = [], []
record = {'start': datetime.now(timezone.utc).isoformat(), 'audit': audit, 'inputs': {}}
for source in inputs:
    content = source.read_bytes()
    (dest / (source.name + '.txt')).write_bytes(content)
    record['inputs'][str(source.relative_to(repo))] = sha256(content).hexdigest()
    lines = content.decode().splitlines()
    imports.extend(line for line in lines if line.startswith('import '))
    bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
combined = '\n'.join(dict.fromkeys(imports)) + '\n' + '\n'.join(bodies)
(dest / 'Combined.lean.txt').write_text(combined)
record['combined_sha256'] = sha256(combined.encode()).hexdigest()
with tempfile.TemporaryDirectory(prefix='guarded-j-reference-check-') as directory:
    source = Path(directory) / 'Combined.lean'
    source.write_text(combined)
    command = ['lake', 'env', 'lean', str(source)]
    record['command'] = command
    started = time.monotonic()
    with (dest / 'stdout.log').open('wb') as stdout, (dest / 'stderr.log').open('wb') as stderr:
        result = subprocess.run(command, cwd=repo, stdout=stdout, stderr=stderr)
    record.update(exit=result.returncode, elapsed_seconds=time.monotonic() - started,
                  finish=datetime.now(timezone.utc).isoformat())
record['evidence_sha256'] = {p.name: sha256(p.read_bytes()).hexdigest() for p in sorted(dest.iterdir())}
(dest / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'archive': str(dest), 'exit': result.returncode, 'audit': audit}))
raise SystemExit(result.returncode)

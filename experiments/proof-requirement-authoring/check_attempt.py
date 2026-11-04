#!/usr/bin/env python3
"""Archive one author source and its exact Lean diagnostics without overwriting."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys


def now():
    return datetime.now(timezone.utc).isoformat()


source = Path(sys.argv[1])
root = Path.cwd()
source.resolve().relative_to((root / "attempts").resolve())
if source.suffix != ".lean":
    raise SystemExit("Expected a .lean source inside attempts/")
archive = root / "attempts" / "checks" / source.stem
archive.mkdir(parents=True, exist_ok=False)
snapshot = archive / "Source.lean"
data = source.read_bytes()
snapshot.write_bytes(data)
command = ["lake", "env", "lean", str(snapshot.relative_to(root))]
record = {"source": str(source), "sha256": sha256(data).hexdigest(),
          "command": command, "start": now()}
(archive / "command.json").write_text(json.dumps(record, indent=2) + "\n")
with (archive / "diagnostics.log").open("wb") as output:
    result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
record.update(finish=now(), exit=result.returncode)
(archive / "result.json").write_text(json.dumps(record, indent=2) + "\n")
print((archive / "diagnostics.log").read_text())
print(f"Exit {result.returncode}; archived at {archive.relative_to(root)}")
raise SystemExit(result.returncode)

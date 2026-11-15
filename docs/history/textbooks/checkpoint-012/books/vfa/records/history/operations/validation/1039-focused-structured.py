"""Compile the five actual StructuredCosts source modules in private outputs.

Diagnostic evidence only: no Lake, cache repair, or integrated gate credit.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root, output, candidate, result_path = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
def git(*args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
assert git("rev-parse", "HEAD") == candidate
assert not git("status", "--porcelain=v1")
assert not output.exists()
output.mkdir(parents=True)
modules = ["Squares", "Applications.Resources.Measured", "Applications.Optimization.Basic",
           "Applications.Optimization.Transport", "Applications.Linear.StructuredCosts"]
sources = {name: root / (name.replace(".", "/") + ".lean") for name in modules}
hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}
dependencies = sorted((root / ".lake/packages").glob("*/.lake/build/lib/lean"))
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *dependencies]))
record = {"candidate": candidate, "root": str(root), "private_output": str(output),
          "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "source_sha256_before": hashes, "LEAN_PATH": env["LEAN_PATH"],
          "scope": "Five actual source modules; diagnostic only", "gate_credit": False, "modules": []}
code = 0
for name in modules:
    target = output / (name.replace(".", "/") + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    argv = ["lean", "-o", str(target), str(sources[name].relative_to(root))]
    print("[focused] " + name, flush=True)
    started = time.monotonic()
    completed = subprocess.run(argv, cwd=root, env=env)
    record["modules"].append({"module": name, "argv": argv,
                              "exit_code": completed.returncode, "seconds": time.monotonic() - started})
    print("[focused result] " + name + " exit=" + str(completed.returncode), flush=True)
    if completed.returncode:
        code = completed.returncode if completed.returncode > 0 else 128 - completed.returncode
        break
record["source_sha256_after"] = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}
record["head_after"] = git("rev-parse", "HEAD")
record["status_after"] = git("status", "--porcelain=v1")
assert record["source_sha256_after"] == hashes and record["head_after"] == candidate and not record["status_after"]
record["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record["exit_code"] = code
result_path.write_text(json.dumps(record, indent=2) + "\n")
sys.exit(code)

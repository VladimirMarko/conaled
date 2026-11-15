"""Check the actual remaining consumer closure in private diagnostic outputs.

No Lake/cache repair and no integrated-build or exhaustive-audit credit.
The module order is a separately preserved, candidate-bound source inventory.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root, output, candidate, order_path, result_path = (
    Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], Path(sys.argv[4]), Path(sys.argv[5]))

def git(*args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

assert git("rev-parse", "HEAD") == candidate
assert not git("status", "--porcelain=v1", "--untracked-files=all")
assert not output.exists() and not output.is_symlink()
order_bytes = order_path.read_bytes()
inventory = json.loads(order_bytes)
assert inventory["candidate"] == candidate
modules = inventory["module_order"]
assert len(modules) == len(set(modules)) == 116
assert modules[0] == "SquareKit.Temporal.Monitor"
assert "ProofAudit" not in modules and "SquareApplications" not in modules
assert "Verification" in modules
sources = {name: root / (name.replace(".", "/") + ".lean") for name in modules}
tracked = set(subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
              .decode().rstrip("\0").split("\0"))
assert all(str(path.relative_to(root)) in tracked for path in sources.values())
hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}
assert hashes == {name: inventory["source_records"][name]["sha256"] for name in modules}
seen = set()
for name in modules:
    assert set(inventory["source_records"][name]["local_imports"]) <= seen
    seen.add(name)
dependencies = sorted((root / ".lake/packages").glob("*/.lake/build/lib/lean"))
assert len(dependencies) == 9
output.mkdir(parents=True)
env = os.environ.copy()
env["LEAN_PATH"] = os.pathsep.join(map(str, [output, *dependencies]))
record = {
    "candidate": candidate, "root": str(root), "private_output": str(output),
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "module_order_file": str(order_path),
    "module_order_sha256": hashlib.sha256(order_bytes).hexdigest(),
    "source_sha256_before": hashes, "LEAN_PATH": env["LEAN_PATH"],
    "scope": "116 actual source modules: Monitor plus all remaining consumers except the import-only public aggregator",
    "gate_credit": False, "modules": [],
}
code = 0
for index, name in enumerate(modules, 1):
    target = output / (name.replace(".", "/") + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    argv = ["lean", "-o", str(target), str(sources[name].relative_to(root))]
    print(f"[focused {index}/{len(modules)}] {name}", flush=True)
    started = time.monotonic()
    completed = subprocess.run(argv, cwd=root, env=env)
    record["modules"].append({"module": name, "argv": argv,
                              "exit_code": completed.returncode,
                              "seconds": time.monotonic() - started})
    print("[focused result] " + name + " exit=" + str(completed.returncode), flush=True)
    if completed.returncode:
        code = completed.returncode if completed.returncode > 0 else 128 - completed.returncode
        break
record["source_sha256_after"] = {
    name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}
record["head_after"] = git("rev-parse", "HEAD")
record["status_after"] = git("status", "--porcelain=v1", "--untracked-files=all")
assert record["source_sha256_after"] == hashes
assert record["head_after"] == candidate and not record["status_after"]
assert order_path.read_bytes() == order_bytes
record["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record["exit_code"] = code
result_path.write_text(json.dumps(record, indent=2) + "\n")
sys.exit(code)

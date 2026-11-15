"""Record actual native identity/proof checks against the final adapter bytes."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

CONTROL = Path(__file__).resolve().parents[2]
ROOT = CONTROL.parent.parent
REPO = CONTROL.parent / "conaled-ch01-review"
ADAPTER = CONTROL / "tooling/native_toolchain.py"
HERE = Path(__file__).resolve().parent
OUT = HERE / "native-smoke"
OUT.mkdir(exist_ok=False)
SOURCE = CONTROL / "provenance/qemu-environment-20261103/smoke/QemuKernelSmoke.lean"
EXPECTED = "07e480f6ec9958d4975bb90151005b84f2907614"


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert git(REPO, "rev-parse", "HEAD") == EXPECTED
assert not git(REPO, "status", "--porcelain=v1", "--untracked-files=all")
commands = [
    ("description", ["--describe"]),
    ("bare-version", ["--", "lean", "--version"]),
    ("bare-githash", ["--", "lean", "--githash"]),
    ("bare-prefix", ["--", "lean", "--print-prefix"]),
    ("lake-version", ["--", "lake", "--version"]),
    ("lake-child-version", ["--", "lake", "env", "lean", "--version"]),
    ("lake-child-path", ["--", "lake", "env", sys.executable, "-c",
                         "import json,os,shutil; print(json.dumps({'lean':shutil.which('lean'),'lake':shutil.which('lake'),'LD_PRELOAD':os.environ.get('LD_PRELOAD'),'LEAN_SYSROOT':os.environ.get('LEAN_SYSROOT')}))"]),
    ("bare-proof", ["--", "lean", "--root", str(SOURCE.parent), "-o", str(OUT / "Bare.olean"), str(SOURCE)]),
    ("lake-child-proof", ["--", "lake", "env", "lean", "--root", str(SOURCE.parent), "-o", str(OUT / "Lake.olean"), str(SOURCE)]),
    ("cache-help", ["--", "lake", "env", str(REPO / ".lake/packages/mathlib/.lake/build/bin/cache"), "--help"]),
]
report = {"started_utc": datetime.now(timezone.utc).isoformat(),
          "candidate": EXPECTED, "adapter_sha256": sha(ADAPTER),
          "shim_source_sha256": sha(CONTROL / "tooling/native/app_path_compat.c"),
          "shim_sha256": sha(CONTROL / "tooling/native/libapp_path_compat.so"),
          "proof_source_sha256": sha(SOURCE), "commands": [],
          "scope": "Native runtime/real proof/cache-startup smoke; no full project validation."}
result_path = HERE / "native-smoke-results.json"
for name, args in commands:
    command = [sys.executable, str(ADAPTER), *args]
    start = time.monotonic()
    result = subprocess.run(command, cwd=REPO, text=True, capture_output=True, timeout=90)
    report["commands"].append({"name": name, "command": command,
                               "exit_code": result.returncode,
                               "elapsed_seconds": time.monotonic() - start,
                               "stdout": result.stdout, "stderr": result.stderr})
    result_path.write_text(json.dumps(report, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(f"Native smoke failed: {name}; actual result retained.")
report["proof_artifacts"] = {name: {"size_bytes": (OUT / name).stat().st_size,
                                    "sha256": sha(OUT / name)}
                              for name in ("Bare.olean", "Lake.olean")}
assert all(value["sha256"] == "fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980"
           for value in report["proof_artifacts"].values())
assert git(REPO, "rev-parse", "HEAD") == EXPECTED
assert not git(REPO, "status", "--porcelain=v1", "--untracked-files=all")
manifest = json.loads((REPO / "lake-manifest.json").read_text())
report["dependencies"] = []
for package in manifest["packages"]:
    path = REPO / manifest["packagesDir"] / package["name"]
    head = git(path, "rev-parse", "HEAD")
    status = git(path, "status", "--porcelain=v1", "--untracked-files=all")
    assert head == package["rev"] and not status
    report["dependencies"].append({"name": package["name"], "head": head, "status": status})
report.update(outcome="passed", completed_utc=datetime.now(timezone.utc).isoformat(),
              final_head=EXPECTED, final_status="")
result_path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"outcome": report["outcome"], "commands": len(commands),
                  "proof_artifacts": report["proof_artifacts"],
                  "timings": {item["name"]: item["elapsed_seconds"] for item in report["commands"]},
                  "result": str(result_path)}, indent=2))

#!/usr/bin/env python3
"""Run exactly the authorized bounded staging check; never write project outputs."""
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import subprocess
import time

stage = Path(__file__).resolve().parent
root = stage.parents[2]
workdir = root / "conaled"
compiler = "/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
command = [
    "timeout", "--signal=TERM", "--kill-after=5s", "180s",
    "nix", "develop", "--command", compiler,
    str(stage / "Applications/FRP/Spec.lean"),
    "-o", str(stage / "out/Spec.olean"),
    "-i", str(stage / "out/Spec.ilean"),
    "-c", str(stage / "out/Spec.c"),
    "--setup", str(stage / "Spec.setup.json"),
    "--json",
]
environment = os.environ.copy()
environment["PATH"] = "/root/.nix-profile/bin:" + environment.get("PATH", "")
environment["NIX_CONFIG"] = "build-users-group =\nexperimental-features = nix-command flakes"
environment["LEAN_NUM_THREADS"] = "1"
started = datetime.now(timezone.utc).isoformat()
metadata = {
    "command": command,
    "working_directory": str(workdir),
    "explicit_environment": {
        "PATH_prefix": "/root/.nix-profile/bin:",
        "NIX_CONFIG": environment["NIX_CONFIG"],
        "LEAN_NUM_THREADS": "1",
    },
    "started_utc": started,
    "timeout_seconds": 180,
    "status": "running",
}
record = stage / "initial-result.json"
record.write_text(json.dumps(metadata, indent=2) + "\n")
print("Starting one bounded import-only staging check.", flush=True)
clock = time.monotonic()
with (stage / "initial-diagnostics.jsonl").open("wb") as log:
    result = subprocess.run(command, cwd=workdir, env=environment,
                            stdout=log, stderr=subprocess.STDOUT)
metadata.update({
    "finished_utc": datetime.now(timezone.utc).isoformat(),
    "elapsed_seconds": round(time.monotonic() - clock, 3),
    "exit_code": result.returncode,
    "timed_out": result.returncode == 124,
    "status": "passed" if result.returncode == 0 else "timeout" if result.returncode == 124 else "failed",
})
record.write_text(json.dumps(metadata, indent=2) + "\n")
print(json.dumps(metadata, indent=2), flush=True)
print((stage / "initial-diagnostics.jsonl").read_text(), end="", flush=True)
raise SystemExit(result.returncode)

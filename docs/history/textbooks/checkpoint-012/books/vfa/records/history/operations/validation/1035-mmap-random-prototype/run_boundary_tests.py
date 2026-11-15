#!/usr/bin/env python3
"""One bounded run of the agreed negative/passthrough prototype boundaries."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

evidence = Path(__file__).resolve().parent
root = evidence.parents[2]
runtime = root / "runtime-tmp/1035-mmap-random-prototype"
record_path = evidence / "boundary-suite.json"
if record_path.exists():
    raise SystemExit("Existing boundary evidence is preserved; this runner is one-use.")
executable = str(Path(sys.executable).resolve())
keys = ["LD_PRELOAD", "CONALED_MMAP_RANDOM", "CONALED_MMAP_RANDOM_EXE",
        "CONALED_MMAP_RANDOM_REPORT"]
base = dict(os.environ)
for key in keys:
    base.pop(key, None)
matched = {"LD_PRELOAD": str(runtime / "libconaled_mmap_random.so"),
           "CONALED_MMAP_RANDOM": "1", "CONALED_MMAP_RANDOM_EXE": executable,
           "CONALED_MMAP_RANDOM_REPORT": "1"}
cases = [
    ("optin_unset", {"CONALED_MMAP_RANDOM": None}, "none", False, ""),
    ("optin_zero", {"CONALED_MMAP_RANDOM": "0"}, "none", False, ""),
    ("optin_invalid", {"CONALED_MMAP_RANDOM": "1x"}, "none", False, ""),
    ("identity_unset", {"CONALED_MMAP_RANDOM_EXE": None}, "none", False, ""),
    ("identity_mismatch", {"CONALED_MMAP_RANDOM_EXE": "/conaled-other-executable"}, "none", False, ""),
    ("identity_relative", {"CONALED_MMAP_RANDOM_EXE": Path(executable).name}, "none", False, ""),
    ("diagnostic_default_off", {"CONALED_MMAP_RANDOM_REPORT": None}, "success", False, ""),
    ("advice_failure", {"LD_PRELOAD": str(runtime / "libfail_madvise_test_only.so") + ":" + matched["LD_PRELOAD"]},
     "failure", False, "selected=1 bytes=4096 success=0 failure=1 last_errno=11"),
    ("passthrough_libc", {"LD_PRELOAD": str(runtime / "libred_snapshot.so")}, "none", True, ""),
    ("passthrough_prototype", {}, "none", True, "selected=0 bytes=0 success=0 failure=0 last_errno=0"),
]
records = []
for name, overrides, expected, passthrough, diagnostic in cases:
    selected = dict(matched)
    for key, value in overrides.items():
        if value is None:
            selected.pop(key, None)
        else:
            selected[key] = value
    env = dict(base, **selected)
    command = [executable, "-B", str(evidence / "test_mmap_random.py"),
               "--fixture", str(runtime / name), "--expect-advice", expected]
    if passthrough:
        command.append("--passthrough")
    record = {"case": name, "command": command, "cwd": str(evidence),
              "selected_environment": selected, "timeout_seconds": 15}
    start = time.monotonic()
    try:
        result = subprocess.run(command, cwd=evidence, env=env, capture_output=True,
                                text=True, timeout=15)
        record.update(returncode=result.returncode, outcome="completed",
                      stdout=result.stdout, stderr=result.stderr)
        record["passed"] = result.returncode == 0 and (
            diagnostic in result.stderr if diagnostic else result.stderr == "")
    except subprocess.TimeoutExpired as exc:
        def text(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else (value or "")
        record.update(returncode=None, outcome="timed_out", passed=False,
                      stdout=text(exc.stdout), stderr=text(exc.stderr))
    record["wall_seconds"] = time.monotonic() - start
    records.append(record)
    print(json.dumps({"case": name, "returncode": record["returncode"],
                      "passed": record["passed"], "wall_seconds": record["wall_seconds"]}), flush=True)
    if not record["passed"]:
        break

def normalized_calls(record):
    observation = json.loads(record["stdout"])
    return [{"name": c["name"], "length": c["length"], "prot": c["prot"],
             "flags": c["flags"], "offset": c["offset"], "errno": c["errno"],
             "failed": c["result"] == (1 << 64) - 1}
            for c in observation["mmap_calls"]]

complete = len(records) == len(cases) and all(r["passed"] for r in records)
passthrough_equal = complete and normalized_calls(records[-2]) == normalized_calls(records[-1])
inputs = [evidence / name for name in ["mmap_random.c", "mmap_random.h", "test_mmap_random.py", "run_boundary_tests.py", "fail_madvise.c"]]
inputs += [runtime / name for name in ["libconaled_mmap_random.so", "libfail_madvise_test_only.so", "libred_snapshot.so"]]
report = {"passed": complete and passthrough_equal, "cases": records,
          "libc_passthrough_results_match": passthrough_equal,
          "input_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
          "scope": "One-page fixtures only; counters are public diagnostics; advice failure is explicitly injected; no Lean execution."}
record_path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "record": str(record_path),
                  "libc_passthrough_results_match": passthrough_equal}), flush=True)
raise SystemExit(0 if report["passed"] else 1)

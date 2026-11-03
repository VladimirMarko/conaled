#!/usr/bin/env python3
"""Exercise the public Lean/Lake CLI with genuine successful and rejected input."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--runner", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    root = args.workspace.resolve()
    distribution = root / "toolchains/lean-4.35.0-linux"
    env = os.environ.copy()
    env.update({
        "PATH": str(distribution / "bin") + os.pathsep + env.get("PATH", ""),
        "LD_LIBRARY_PATH": os.pathsep.join(str(distribution / p) for p in ("lib/lean", "lib")),
        "LEAN_SYSROOT": str(distribution),
        "LEAN_NUM_THREADS": "1",
    })
    prefix = ([sys.executable, str(args.runner.resolve()), "--workspace", str(root), "--"]
              if args.runner else [])
    probes = []

    def run(command, cwd):
        start = time.monotonic()
        result = subprocess.run(prefix + command, cwd=cwd, env=env,
                                text=True, capture_output=True, timeout=180)
        probe = {"command": prefix + command, "returncode": result.returncode,
                 "stdout": result.stdout, "stderr": result.stderr,
                 "elapsed_seconds": time.monotonic() - start}
        probes.append(probe)
        return probe

    temporary_parent = root / "session/tools"
    temporary_parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="toolchain-smoke-", dir=temporary_parent) as temp:
        work = Path(temp)
        (work / "Valid.lean").write_text(
            "import Lean\n"
            "theorem launcher_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n\n"
            "#print axioms launcher_add_zero\n")
        (work / "Invalid.lean").write_text("import Lean\nexample : False := by exact True.intro\n")
        lean_version = run(["lean", "--version"], work)
        lake_version = run(["lake", "--version"], work)
        valid = run(["lean", "Valid.lean"], work)
        invalid = run(["lean", "Invalid.lean"], work)
        checks = {
            "exact_lean_version": lean_version["returncode"] == 0 and lean_version["stdout"].strip() ==
                "Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)",
            "exact_lake_version": lake_version["returncode"] == 0 and lake_version["stdout"].strip() ==
                "Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)",
            "valid_theorem_accepted": valid["returncode"] == 0 and
                "does not depend on any axioms" in valid["stdout"],
            "false_theorem_rejected": invalid["returncode"] != 0 and
                "type mismatch" in (invalid["stdout"] + invalid["stderr"]).lower(),
        }
        report = {"test": "public Lean/Lake command-line interfaces", "workspace": str(root),
                  "runner": str(args.runner.resolve()) if args.runner else None,
                  "checks": checks, "probes": probes, "passed": all(checks.values())}
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"report": str(args.report), "passed": report["passed"], "checks": checks}, indent=2))
        return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

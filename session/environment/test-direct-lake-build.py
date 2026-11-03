#!/usr/bin/env python3
"""Check Lake's real compiler and native-linker path through a tiny executable."""
import argparse
import json
import os
from pathlib import Path
import shutil
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
        "LEAN_SYSROOT": str(distribution), "LEAN_NUM_THREADS": "1",
    })
    prefix = ([sys.executable, str(args.runner.resolve()), "--workspace", str(root), "--"]
              if args.runner else [])
    work = Path(tempfile.mkdtemp(prefix="lake-smoke-", dir=root / "session/tools"))
    (work / "lakefile.toml").write_text(
        'name = "launcher_smoke"\ndefaultTargets = ["smoke"]\n'
        '[[lean_exe]]\nname = "smoke"\nroot = "Main"\n')
    (work / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (work / "Main.lean").write_text(
        "theorem launcher_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n\n"
        "def main : IO Unit := IO.println (toString (6 * 7))\n")
    probes = []

    def run(command):
        start = time.monotonic()
        result = subprocess.run(prefix + command, cwd=work, env=env,
                                text=True, capture_output=True, timeout=300)
        value = {"command": prefix + command, "returncode": result.returncode,
                 "stdout": result.stdout, "stderr": result.stderr,
                 "elapsed_seconds": time.monotonic() - start}
        probes.append(value)
        return value

    version = run(["lake", "env", "lean", "--version"])
    build = run(["lake", "-v", "build", "smoke"])
    execute = run([str(work / ".lake/build/bin/smoke")]) if build["returncode"] == 0 else None
    checks = {
        "lake_uses_exact_lean": version["returncode"] == 0 and
            "commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in version["stdout"],
        "lake_builds_executable": build["returncode"] == 0,
        "compiled_executable_runs": execute is not None and execute["returncode"] == 0 and
            execute["stdout"] == "42\n",
    }
    report = {"test": "Lake builds and executes a Lean program", "workspace": str(root),
              "runner": str(args.runner.resolve()) if args.runner else None,
              "temporary_project": str(work), "checks": checks, "probes": probes,
              "passed": all(checks.values())}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    if report["passed"]:
        shutil.rmtree(work)
    print(json.dumps({"report": str(args.report), "passed": report["passed"], "checks": checks}, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

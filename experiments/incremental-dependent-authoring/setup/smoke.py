#!/usr/bin/env python3
"""Exercise the unchanged attempt wrapper with unrelated setup-only checks.

The frozen handoff must already have an allowed development environment.
Archives are moved to an external setup evidence directory after checking.
No attempt source contains a solution or a claim about the measured task.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--handoff", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--entry", action="append", required=True)
    args = parser.parse_args()
    root = args.handoff.resolve()
    args.evidence.mkdir(parents=True, exist_ok=False)
    imports = "".join(f"import {name}\n" for name in args.entry)
    records = []
    for stem, body, expected in (
        ("SetupTrue", "example : True := True.intro\n", "lean-passed"),
        ("SetupFalse", "example : False := True.intro\n", "lean-failed"),
    ):
        source = root / "attempts" / (stem + ".lean")
        if source.exists():
            raise ValueError(f"Refusing to replace setup attempt: {source}")
        source.write_text(imports + body)
        started = time.monotonic()
        result = subprocess.run(
            ["direnv", "exec", ".", "python3", "check_attempt.py", str(source.relative_to(root))],
            cwd=root, capture_output=True)
        (args.evidence / f"{stem}.invocation.stdout.log").write_bytes(result.stdout)
        (args.evidence / f"{stem}.invocation.stderr.log").write_bytes(result.stderr)
        archive = root / "attempts/checks" / stem
        record = json.loads((archive / "result.json").read_text())
        if record["status"] != expected:
            raise ValueError(f"Unexpected {stem} outcome: {record}")
        if record.get("public_inputs_before") != "verified" or record.get("public_inputs_after") != "verified":
            raise ValueError(f"Missing public-input verification: {stem}")
        records.append({"name": stem, "expected": expected, "exit": result.returncode,
                        "elapsed_seconds": time.monotonic() - started,
                        "result_sha256": sha256((archive / "result.json").read_bytes()).hexdigest()})
        archive.chmod(0o755)
        shutil.move(str(archive), str(args.evidence / stem))
        (args.evidence / stem).chmod(0o555)
        shutil.move(str(source), str(args.evidence / source.name))
    checks = root / "attempts/checks"
    if checks.exists() and not list(checks.iterdir()):
        checks.rmdir()
    (args.evidence / "summary.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Record exact compiler identity and isolated Init-only kernel checks."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys


PROVENANCE = Path(__file__).resolve().parent
WORKSPACE = PROVENANCE.parents[3]
REPOSITORY = WORKSPACE / "work/conaled-ch01-review"
ADAPTER = WORKSPACE / "work/fdsa-control/tooling/pinned_toolchain.py"
OVERLAY = WORKSPACE / "bootstrap/lean-4.35.0-host"
EXPECTED_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main() -> None:
    record = {"started_at": now(), "candidate": "07e480f6ec9958d4975bb90151005b84f2907614",
              "adapter": str(ADAPTER), "adapter_sha256": digest(ADAPTER), "commands": [],
              "scope": "Environment identity and Init-only theorem smoke; no dependency cache, project build, or project proof audit."}
    output = PROVENANCE / "launcher-smoke.json"

    def save() -> None:
        output.write_text(json.dumps(record, indent=2) + "\n")

    def run(name: str, args: list[str], cwd: Path = REPOSITORY) -> str:
        command = [sys.executable, str(ADAPTER), "--", *args]
        if args == ["--describe"]:
            command = [sys.executable, str(ADAPTER), "--describe"]
        started = now()
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=60)
        item = {"name": name, "command": command, "cwd": str(cwd), "started_at": started,
                "finished_at": now(), "exit_code": result.returncode,
                "stdout": result.stdout, "stderr": result.stderr}
        record["commands"].append(item)
        save()
        print(json.dumps({"name": name, "exit_code": result.returncode,
                          "stdout": result.stdout if name != "describe" else "retained in launcher-environment.json",
                          "stderr": result.stderr}), flush=True)
        if result.returncode:
            raise RuntimeError(f"{name} failed with exit {result.returncode}")
        return result.stdout.strip()

    try:
        description = json.loads(run("describe", ["--describe"]))
        (PROVENANCE / "launcher-environment.json").write_text(json.dumps(description, indent=2) + "\n")
        run("qemu-version", [str(WORKSPACE / "bootstrap/qemu-user/bin/qemu-x86_64-static"), "--version"])
        bare_version = run("bare-lean-version", ["lean", "--version"])
        assert "version 4.35.0" in bare_version
        assert run("bare-lean-githash", ["lean", "--githash"]) == EXPECTED_COMMIT
        assert run("bare-lean-prefix", ["lean", "--print-prefix"]) == str(OVERLAY)
        lake_version = run("lake-version", ["lake", "--version"])
        assert "5.0.0-src+eb6cafb" in lake_version and "4.35.0" in lake_version
        assert run("lake-child-lean-version", ["lake", "env", "lean", "--version"]) == bare_version
        assert run("lake-child-lean-githash", ["lake", "env", "lean", "--githash"]) == EXPECTED_COMMIT
        assert run("lake-child-lean-prefix", ["lake", "env", "lean", "--print-prefix"]) == str(OVERLAY)
        child = json.loads(run("lake-child-path", ["lake", "env", sys.executable, "-c",
            "import json,os,shutil; print(json.dumps({'lean':shutil.which('lean'),'lake':shutil.which('lake'),"
            "'LEAN_SYSROOT':os.environ.get('LEAN_SYSROOT'),'LEAN':os.environ.get('LEAN'),"
            "'LEAN_GITHASH':os.environ.get('LEAN_GITHASH'),'LEAN_NUM_THREADS':os.environ.get('LEAN_NUM_THREADS')}))"]))
        assert child["lean"] == str(OVERLAY / "bin/lean")
        assert child["lake"] == str(OVERLAY / "bin/lake")
        assert child["LEAN_GITHASH"] in (None, EXPECTED_COMMIT)
        smoke = PROVENANCE / "smoke"
        smoke.mkdir(exist_ok=True)
        source = smoke / "QemuKernelSmoke.lean"
        source.write_text("""import Init

namespace FdsaEnvironmentSmoke

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem successor_addition (n : Nat) : n + 1 = Nat.succ n := by
  rfl

#print axioms zero_add
#print axioms successor_addition

end FdsaEnvironmentSmoke
""")
        record["proof_source"] = {"path": str(source), "sha256": digest(source)}
        artifacts = []
        for name, prefix in [("bare-proof", []), ("lake-child-proof", ["lake", "env"])]:
            destination = smoke / name / "QemuKernelSmoke.olean"
            destination.parent.mkdir(exist_ok=True)
            stdout = run(name, [*prefix, "lean", "--root", str(smoke), "-o", str(destination), str(source)])
            assert stdout.count("does not depend on any axioms") == 2
            assert destination.is_file() and destination.stat().st_size > 0
            artifacts.append({"route": name, "path": str(destination), "sha256": digest(destination),
                              "size": destination.stat().st_size})
        record["proof_artifacts"] = artifacts
        record["result"] = "passed"
    except BaseException as error:
        record["result"] = "failed"
        record["error"] = repr(error)
        raise
    finally:
        record["finished_at"] = now()
        save()
        print(json.dumps({"result": record.get("result"), "error": record.get("error")}), flush=True)


if __name__ == "__main__":
    main()

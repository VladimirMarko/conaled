#!/usr/bin/env python3
"""Preserve this failed run's existing evidence; never repair or build outputs."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

root = Path(__file__).resolve().parents[2]
repo = root / "conaled-ch01-review"
out = root / "fdsa-control/provenance/chapter01-enospc-20261102"
assert not out.exists(), "Refuse to replace captured evidence"
expected = "1aabd512284fe86254278ac631eda061d311050b"
head = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
status = subprocess.check_output(["git", "-C", str(repo), "status", "--porcelain=v1"], text=True)
assert head == expected and status == "", "Candidate source identity changed"

writers = []
for proc in Path("/proc").iterdir():
    if not proc.name.isdigit():
        continue
    try:
        cwd = os.readlink(proc / "cwd")
        if not cwd.startswith(str(root)):
            continue
        exe = Path(os.readlink(proc / "exe")).name
        args = proc.joinpath("cmdline").read_bytes().decode(errors="replace").split("\0")
        if exe in {"lean", "lake"} or any(a.endswith("/scripts/check.py") or a == "scripts/check.py" for a in args):
            writers.append({"pid": int(proc.name), "exe": exe, "cwd": cwd, "args": args})
    except OSError:
        pass
assert not writers, "Task-local compiler/checker still active"

log = root / "fdsa-control/reviews/chapter01-incremental.log"
raw = log.read_bytes()
text = raw.decode(errors="replace")
modules = sorted(set(re.findall(r"^✖\s+\[[^\]]+\]\s+(?:Building|Built|Ran)\s+([\w.]+)", text, re.M)))
assert "no space left on device" in text and modules
files = set()
families = {}
for module in modules:
    stem = Path(*module.split("."))
    members = []
    source = repo / stem.with_suffix(".lean")
    if source.is_file():
        files.add(source)
    for prefix in (repo / ".lake/build/lib/lean", repo / ".lake/build/ir"):
        path = prefix / stem
        for member in sorted(path.parent.glob(path.name + ".*")):
            if member.is_file() and not member.is_symlink():
                files.add(member)
                members.append(str(member.relative_to(repo)))
    families[module] = members
for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "flake.nix", "flake.lock", "check.sh", "scripts/check.py", "scripts/lake_integrity.py"):
    files.add(repo / name)
verification = repo / ".lake/verification.json"
assert not verification.exists(), "Unexpected success record needs separate investigation"

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

out.mkdir(parents=True)
identities = []
for source in sorted(files):
    rel = source.relative_to(repo)
    target = out / "candidate-files" / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    before = digest(source)
    shutil.copy2(source, target)
    assert digest(target) == before == digest(source), "Evidence changed during capture"
    identities.append({"path": str(rel), "bytes": source.stat().st_size, "sha256": before})
(out / "chapter01-incremental-attempt3-enospc.log").write_bytes(raw)
assert log.read_bytes() == raw, "Failed log changed during capture"
filesystem = os.statvfs(root)
record = {
    "captured_utc": datetime.now(timezone.utc).isoformat(),
    "exit_observed_utc": "2026-11-02T15:44:10Z",
    "task": "FDSA-001",
    "candidate": head,
    "source_status": status,
    "command": "env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD",
    "parent_execution_session": 80227,
    "parent_exit_code": 120,
    "recorded_lean_version": "Lean 4.35.0 eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
    "recorded_lake_version": "Lake 5.0.0-src+eb6cafb",
    "log": {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(), "ends_with_newline": raw.endswith(b"\n"), "truncated": True},
    "task_local_compiler_checker_processes": writers,
    "verification_record_present": False,
    "failed_modules_reported_in_surviving_log": modules,
    "surviving_artifact_family_files": families,
    "captured_files": identities,
    "available_bytes_at_capture": filesystem.f_bavail * filesystem.f_frsize,
    "free_bytes_at_capture": filesystem.f_bfree * filesystem.f_frsize,
    "classification": "Explicit disk exhaustion during output generation; unsuccessful validation with truncated log. No demonstrated match to the documented GraphEmission stale-artifact recurrence. Surviving output soundness and errors lost from the truncated tail are not established.",
    "preservation_boundary": "Copied existing source/configuration and surviving failed-module output/trace/sidecar families before any guard or manual artifact invalidation. Missing evidence is not reconstructed. No build, project hash helper, output repair or source change performed.",
    "acceptance": "none"
}
(out / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"evidence_directory": str(out), "candidate": head, "failed_modules": len(modules), "captured_files": len(identities), "captured_bytes": sum(x["bytes"] for x in identities) + len(raw), "log_sha256": record["log"]["sha256"], "acceptance": "none"}))

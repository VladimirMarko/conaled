#!/usr/bin/env python3
"""Record an ordinary, unchanged candidate check independently of its tool handle."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CONTROL = ROOT / "fdsa-control"
CHECKOUT = ROOT / "conaled-ch01-review"
CANDIDATE = "07e480f6ec9958d4975bb90151005b84f2907614"
METADATA = CONTROL / "provenance/chapter01-repair-guarded-attempt3.json"
LOG = CONTROL / "reviews/chapter01-repair-incremental-attempt3.log"
RECORD_COPY = CONTROL / "provenance/chapter01-repair-attempt3-verification.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=CHECKOUT, text=True).strip()


def save(data):
    temporary = METADATA.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(METADATA)


def process_identity(pid):
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
        fields = stat[stat.rfind(")") + 2:].split()
        return {"pid": pid, "start_ticks": fields[19], "state": fields[0],
                "process_group": os.getpgid(pid), "session": os.getsid(pid)}
    except (OSError, IndexError):
        return {"pid": pid, "identity_unavailable": True}


def main():
    if METADATA.exists() or LOG.exists() or RECORD_COPY.exists():
        raise RuntimeError("Attempt3 evidence already exists; refuse to overwrite or repeat.")
    head = git("rev-parse", "HEAD")
    status = git("status", "--porcelain=v1", "--untracked-files=all")
    if head != CANDIDATE or status:
        raise RuntimeError("Expected unchanged clean Chapter 1 review candidate.")
    checkpoint = json.loads((CONTROL / "checkpoints.json").read_text())["checkpoints"][-1]
    if (checkpoint["checkpoint"] != "conaled-fdsa-0054-chapter01-session-recovery"
            or not checkpoint.get("library_file_id")
            or checkpoint["local_metadata_applied"] is not True):
        raise RuntimeError("Checkpoint 0054 successful receipt is required before this attempt.")
    os.chdir(CHECKOUT)
    command = ["env", "LEAN_NUM_THREADS=1", "./check.sh", "--candidate", "HEAD"]
    data = {
        "candidate": head, "review_base": "7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd",
        "started_utc": now(), "checkout": str(CHECKOUT), "initial_status": status,
        "command": command, "LEAN_NUM_THREADS": "1", "result": "starting",
        "log": str(LOG), "wrapper": process_identity(os.getpid()),
        "available_bytes_at_start": shutil.disk_usage(CHECKOUT).free,
        "prior_attempt_outcome": "Attempts1 and2 both have unknown terminal outcomes; both INC02 evidence sets remain preserved without modification.",
        "recovery_disposition": "reviews/chapter01-session2-recovery-standards.md",
        "recovery_disposition_sha256": hashlib.sha256(
            (CONTROL / "reviews/chapter01-session2-recovery-standards.md").read_bytes()).hexdigest(),
        "launcher_mode": "External pinned-Nix launch in a separate session; checker command and verification policy unchanged.",
        "scope": "Full unchanged ordinary guarded candidate check: source/coverage/compiler identity, both integrity passes, complete integrated build and exhaustive proof audit. Both retained final review axes and immediate verify-candidate remain required."
    }
    save(data)
    with LOG.open("x", buffering=1) as output:
        child = subprocess.Popen(command, cwd=CHECKOUT, stdout=output, stderr=subprocess.STDOUT)
        data.update(result="running", checker=process_identity(child.pid))
        save(data)
        print(json.dumps({"started_utc": data["started_utc"], "candidate": head,
                          "wrapper": data["wrapper"], "checker": data["checker"],
                          "log": str(LOG)}), flush=True)
        exit_code = child.wait()
    # Preserve the actual child exit before secondary identity/hash/copy work.
    data.update(result="checker_exited", checker_exited_utc=now(), exit_code=exit_code)
    save(data)
    data.update(completed_utc=now(), exit_code=exit_code,
                result="passed" if exit_code == 0 else "failed",
                final_head=git("rev-parse", "HEAD"),
                final_status=git("status", "--porcelain=v1", "--untracked-files=all"),
                log_size_bytes=LOG.stat().st_size,
                log_sha256=hashlib.file_digest(LOG.open("rb"), "sha256").hexdigest(),
                available_bytes_at_completion=shutil.disk_usage(CHECKOUT).free)
    record = CHECKOUT / ".lake/verification.json"
    data["verification_record_present"] = record.exists()
    if record.exists():
        shutil.copyfile(record, RECORD_COPY)
        data["verification_record_copy"] = str(RECORD_COPY)
        data["verification_record_sha256"] = hashlib.file_digest(RECORD_COPY.open("rb"), "sha256").hexdigest()
    save(data)
    print(json.dumps({k: data[k] for k in ("result", "exit_code", "completed_utc", "final_head", "final_status", "log_size_bytes", "log_sha256", "verification_record_present")}), flush=True)
    return exit_code if exit_code >= 0 else 128 - exit_code


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Retain a command's actual outcome and closed log in durable task records.

This recorder does not alter a project command or its acceptance policy. A
missing result.json means that the terminal outcome is unknown, regardless of
an old start/progress record. It never retries an existing named invocation.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


CONTROL = Path(__file__).resolve().parents[1]


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def save(path: Path, data: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def git(cwd: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(cwd), *args], text=True).strip()


def execute(directory: Path) -> int:
    request = json.loads((directory / "request.json").read_text())
    cwd = Path(request["cwd"])
    log = directory / "full.log"
    if log.exists() or (directory / "result.json").exists():
        raise RuntimeError("This invocation has already started; do not repeat it.")
    head = git(cwd, "rev-parse", "HEAD")
    status = git(cwd, "status", "--porcelain=v1", "--untracked-files=all")
    if head != request["candidate"] or status:
        raise RuntimeError("Expected unchanged, clean candidate checkout.")
    start = dict(request, started_utc=now(), initial_head=head,
                 initial_status=status, recorder_pid=os.getpid(),
                 available_bytes_at_start=shutil.disk_usage(cwd).free)
    save(directory / "start.json", start)
    started = time.monotonic()
    progress_errors = []
    with log.open("xb") as output:
        child = subprocess.Popen(request["command"], cwd=cwd,
                                 stdin=subprocess.DEVNULL, stdout=output,
                                 stderr=subprocess.STDOUT, close_fds=True)
        while True:
            try:
                save(directory / "progress.json", {
                    "observed_utc": now(), "state": "waiting_for_owned_child",
                    "child_pid": child.pid, "elapsed_seconds": time.monotonic() - started,
                    "log_size_bytes": log.stat().st_size,
                    "warning": "A historical progress record does not establish current liveness."
                })
            except Exception as error:
                # Progress is optional. A failed observation must not abandon
                # the owned child or prevent recording its actual exit.
                if len(progress_errors) < 5:
                    progress_errors.append({"observed_utc": now(), "error": repr(error)})
            try:
                exit_code = child.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                pass
    # Preserve the observed exit before fallible secondary bookkeeping.
    result = {"candidate": head, "command": request["command"],
              "started_utc": start["started_utc"], "completed_utc": now(),
              "exit_code": exit_code, "elapsed_seconds": time.monotonic() - started,
              "state": "command_exited", "log": str(log),
              "progress_bookkeeping_errors": progress_errors}
    save(directory / "result.json", result)
    try:
        result.update(final_head=git(cwd, "rev-parse", "HEAD"),
                      final_status=git(cwd, "status", "--porcelain=v1", "--untracked-files=all"),
                      log_size_bytes=log.stat().st_size, log_sha256=digest(log),
                      available_bytes_at_completion=shutil.disk_usage(cwd).free)
        record = cwd / ".lake/verification.json"
        result["verification_record_present"] = record.exists()
        if record.exists():
            copy = directory / "verification.json"
            shutil.copyfile(record, copy)
            result["verification_record_sha256"] = digest(copy)
        result["state"] = "passed" if exit_code == 0 else "failed"
    except Exception as error:
        result["bookkeeping_error"] = repr(error)
    save(directory / "result.json", result)
    return exit_code if exit_code >= 0 else 128 - exit_code


def main() -> int:
    if sys.argv[1:2] == ["--worker"]:
        return execute(Path(sys.argv[2]))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    parser.add_argument("--cwd", required=True, type=Path)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.name.replace("-", "").replace("_", "").isalnum():
        parser.error("Name must contain only letters, digits, hyphens and underscores.")
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("A complete command after -- is required.")
    directory = CONTROL / "provenance" / args.name
    directory.mkdir(exist_ok=False)
    request = {"requested_utc": now(), "cwd": str(args.cwd.resolve()),
               "candidate": args.candidate, "command": command,
               "scope": "Process recording only; command and acceptance policy unchanged."}
    save(directory / "request.json", request)
    # Stay in the execution session. This host does not retain a detached
    # subprocess after its initiating command returns. The caller may yield
    # the live session, but must not mistake that yield for command completion.
    save(directory / "launch.json", {"launched_utc": now(), "recorder_pid": os.getpid(),
                                      "terminal_outcome": "pending",
                                      "mode": "foreground recorder in retained execution session"})
    print(json.dumps({"directory": str(directory), "recorder_pid": os.getpid()}), flush=True)
    return execute(directory)


if __name__ == "__main__":
    sys.exit(main())

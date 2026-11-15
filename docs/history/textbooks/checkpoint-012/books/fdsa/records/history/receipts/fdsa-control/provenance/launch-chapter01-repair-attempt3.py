#!/usr/bin/env python3
"""Launch the unchanged pinned gate once, without retaining a tool-session pipe.

Preparation only until the retained recovery disposition is read and checkpoint
0054 has a successful receipt. This does not change conaled or its checker.
"""
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CONTROL = ROOT / "fdsa-control"
INTENT = CONTROL / "provenance/chapter01-repair-attempt3-launch.json"
OUTPUT = CONTROL / "reviews/chapter01-repair-attempt3-launcher.log"
RECORDER = CONTROL / "provenance/run-chapter01-repair-attempt3.py"


def now():
    return datetime.now(timezone.utc).isoformat()


def save(data):
    temporary = INTENT.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(INTENT)


def main():
    if sys.argv[1:] != ["--launch"]:
        raise RuntimeError("Explicit --launch is required after recovery review and checkpoint save.")
    for path in (INTENT, OUTPUT,
                 CONTROL / "provenance/chapter01-repair-guarded-attempt3.json",
                 CONTROL / "reviews/chapter01-repair-incremental-attempt3.log",
                 CONTROL / "provenance/chapter01-repair-attempt3-verification.json"):
        if path.exists():
            raise RuntimeError(f"Attempt3 evidence already exists: {path}; refuse to repeat.")
    receipt = json.loads((CONTROL / "checkpoints.json").read_text())["checkpoints"][-1]
    if (receipt["checkpoint"] != "conaled-fdsa-0054-chapter01-session-recovery"
            or receipt["local_metadata_applied"] is not True
            or not receipt.get("library_file_id")):
        raise RuntimeError("Checkpoint0054 must be saved successfully before launch.")
    if not (CONTROL / "reviews/chapter01-session2-recovery-standards.md").is_file():
        raise RuntimeError("The retained recovery report is required before launch.")
    command = [
        "/root/.nix-profile/bin/nix", "--extra-experimental-features", "nix-command flakes",
        "--option", "build-users-group", "", "develop", "--command", "python3", str(RECORDER)
    ]
    data = {
        "requested_utc": now(), "result": "launch_requested", "command": command,
        "cwd": str(ROOT / "conaled"), "output": str(OUTPUT),
        "checkpoint": receipt["checkpoint"], "checkpoint_sha256": receipt["sha256"],
        "checkpoint_library_file_id": receipt["library_file_id"],
        "separate_session": True,
        "scope": "Process lifecycle only. No checker, candidate, pin, mode, guard, audit, or cache-policy change."
    }
    # An exclusive intent survives a lost launch response and prevents blind retries.
    with INTENT.open("x") as stream:
        json.dump(data, stream, indent=2)
        stream.write("\n")
    try:
        with OUTPUT.open("xb") as output:
            child = subprocess.Popen(
                command, cwd=ROOT / "conaled", stdin=subprocess.DEVNULL,
                stdout=output, stderr=subprocess.STDOUT,
                start_new_session=True, close_fds=True
            )
        data.update(result="process_spawned", launcher_process={
            "pid": child.pid, "identity_pending": True
        })
        save(data)
        stat = Path(f"/proc/{child.pid}/stat").read_text()
        fields = stat[stat.rfind(")") + 2:].split()
        data.update(result="launched", launched_utc=now(), launcher_process={
            "pid": child.pid, "start_ticks": fields[19], "state": fields[0],
            "process_group": os.getpgid(child.pid), "session": os.getsid(child.pid)
        })
    except BaseException as error:
        data.update(result="launch_error_or_identity_unavailable", observed_utc=now(),
                    error=repr(error))
        save(data)
        raise
    save(data)
    print(json.dumps({"result": data["result"], "launcher_process": data["launcher_process"],
                      "metadata": str(INTENT), "output": str(OUTPUT)}), flush=True)


if __name__ == "__main__":
    main()

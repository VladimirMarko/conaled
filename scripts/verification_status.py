"""Operational observations for candidate validation; never acceptance evidence."""

import fcntl
import json
import math
import os
from pathlib import Path
import sys
import tempfile
import time


PHASES = {"preparing", "preflight", "checking-artifacts", "building", "auditing",
          "recording", "verifying-receipt", "complete"}
OUTCOMES = {"running", "passed", "failed", "interrupted", "unknown"}


def read(path):
    try:
        value = json.loads(path.read_text())
        return value if isinstance(value, dict) else None
    except (OSError, ValueError):
        return None


def publish(path, record):
    """Atomically replace the current observation in an already owned directory."""
    record = dict(record)
    record["elapsed_seconds"] = max(0, time.monotonic() - record["started_monotonic"])
    record["updated_at"] = time.time()
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as out:
            temporary = Path(out.name)
            json.dump(record, out)
            out.write("\n")
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def phase(name):
    """Publish a best-effort phase observation for the invoking wrapper's run."""
    path = os.environ.get("CONALED_STATUS_FILE")
    run_id = os.environ.get("CONALED_RUN_ID")
    if not path or not run_id:
        return
    try:
        record = read(Path(path))
        if record is None or record.get("run_id") != run_id or record.get("outcome") != "running":
            return
        if name not in PHASES:
            raise ValueError("Unknown verification phase")
        publish(Path(path), dict(record, phase=name))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Status observation unavailable: {error}", file=sys.stderr)


def finite_nonnegative(value):
    try:
        return type(value) in (int, float) and value >= 0 and math.isfinite(value)
    except OverflowError:
        return False


def observe(state):
    """Read under the workspace lock when idle; report conservative live observations."""
    result = {"format": 1, "candidate": None, "phase": None, "elapsed_seconds": None,
              "outcome": "unknown"}
    if not state.exists():
        return dict(result, outcome="not-started")
    lock = None
    busy = False
    try:
        try:
            lock = (state / "acceptance.lock").open("rb")
        except OSError:
            return dict(result, detail="Workspace lock unavailable")
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            busy = True
        record = read(state / "acceptance-status.json")
        marker = read(state / "acceptance-running.json")
        marker_exists = (state / "acceptance-running.json").exists()
        valid = (record is not None and record.get("format") == 1
                 and isinstance(record.get("candidate"), str)
                 and isinstance(record.get("run_id"), str)
                 and isinstance(record.get("phase"), str) and record["phase"] in PHASES
                 and isinstance(record.get("outcome"), str) and record["outcome"] in OUTCOMES
                 and all(finite_nonnegative(record.get(k))
                         for k in ("elapsed_seconds", "started_monotonic")))
        if busy:
            result["outcome"] = "running"
            if marker:
                result["candidate"] = marker.get("candidate")
            if valid and marker and marker.get("run_id") == record["run_id"]:
                result.update(candidate=record["candidate"], phase=record["phase"],
                              elapsed_seconds=max(0, time.monotonic() - record["started_monotonic"]))
            return result
        if not valid:
            return dict(result, detail="No usable status observation")
        result.update(candidate=record["candidate"], phase=record["phase"],
                      elapsed_seconds=record["elapsed_seconds"], operation=record.get("operation"))
        if marker_exists:
            if marker and marker.get("run_id") == record["run_id"] and record["outcome"] == "interrupted":
                result["outcome"] = "interrupted"
            else:
                result.update(outcome="unknown", detail="Unresolved run marker; completion is unknown")
        elif record["outcome"] == "running":
            result.update(outcome="unknown", detail="Run is no longer locked but has no completion observation")
        else:
            result["outcome"] = record["outcome"]
        return result
    finally:
        if lock is not None:
            lock.close()

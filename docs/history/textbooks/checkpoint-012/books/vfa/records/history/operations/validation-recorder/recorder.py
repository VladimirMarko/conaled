#!/usr/bin/env python3
"""Record one explicitly requested local command; do not infer acceptance."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time


class RecorderInterrupted(Exception):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f"recorder received signal {signum}")


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def sync_directory(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_json(path, value):
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as output:
            json.dump(value, output, indent=2, allow_nan=False)
            output.write("\n")
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
        sync_directory(path.parent)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def new_log(path):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_APPEND, 0o600)
    return os.fdopen(fd, "wb", buffering=0)


def append_record(output, value):
    remaining = memoryview((json.dumps(value, allow_nan=False) + "\n").encode())
    while remaining:
        written = output.write(remaining)
        if not written:
            raise OSError("log write made no progress")
        remaining = remaining[written:]
    os.fsync(output.fileno())


def report_error(errors_log, error):
    """Best effort only: exhausted/broken storage can also defeat this report."""
    if errors_log is not None:
        try:
            append_record(errors_log, error)
        except OSError as exc:
            error = {**error, "error_log_failure": repr(exc)}
    try:
        print(json.dumps(error), file=sys.stderr, flush=True)
    except OSError:
        pass


def positive_seconds(text):
    value = float(text)
    if not math.isfinite(value) or not 0 < value <= 60:
        raise argparse.ArgumentTypeError("seconds must be finite, positive and at most 60")
    return value


def stop_owned_child(child, grace):
    """Signal only a still-unreaped child whose own session/group we created.

    This process is the only waiter. After poll returns None, even an exiting
    child retains its PID until we reap it, so its PID/group cannot be reused
    between the identity checks and killpg. Never signal after reaping it.
    """
    cleanup = {"signals": [], "errors": [], "child_returncode": None}
    for sig in (signal.SIGTERM, signal.SIGKILL):
        if child.poll() is not None:
            cleanup["child_returncode"] = child.wait()
            return cleanup
        try:
            if os.getpgid(child.pid) != child.pid or os.getsid(child.pid) != child.pid:
                cleanup["errors"].append("owned child no longer has its recorded group/session")
                return cleanup
            os.killpg(child.pid, sig)
            cleanup["signals"].append({"signal": sig.name, "sent_utc": utc_now()})
            cleanup["child_returncode"] = child.wait(timeout=grace)
            return cleanup
        except subprocess.TimeoutExpired:
            continue
        except OSError as exc:
            cleanup["errors"].append(repr(exc))
            if child.poll() is not None:
                cleanup["child_returncode"] = child.wait()
            return cleanup
    cleanup["errors"].append("child did not exit within the bounded cleanup waits")
    return cleanup


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cwd", required=True, type=Path)
    parser.add_argument("--attempt-dir", required=True, type=Path)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--mode", required=True)
    parser.add_argument("--env", action="append", default=[], metavar="KEY=VALUE")
    parser.add_argument("--heartbeat-seconds", type=positive_seconds, default=30.0)
    parser.add_argument("--cleanup-grace-seconds", type=positive_seconds, default=5.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    if not args.command:
        parser.error("an explicit command argument vector is required after --")
    if not args.cwd.is_absolute() or not args.cwd.is_dir():
        parser.error("--cwd must be an existing absolute directory")
    if not args.attempt_dir.is_absolute() or not args.attempt_dir.parent.is_dir():
        parser.error("--attempt-dir must be absolute with an existing parent")
    args.environment_changes = {}
    for entry in args.env:
        key, separator, value = entry.partition("=")
        if not separator or not key or "\0" in entry or key in args.environment_changes:
            parser.error("--env requires distinct nonempty KEY=VALUE entries without NUL")
        args.environment_changes[key] = value
    return args


def record(args):
    pending_signal = None

    def receive_signal(signum, _frame):
        # Do not raise asynchronously during Popen: first retain the returned
        # child handle, then perform cleanup at an ordinary control boundary.
        nonlocal pending_signal
        if pending_signal is None:
            pending_signal = signum

    def check_interruption():
        if pending_signal is not None:
            raise RecorderInterrupted(pending_signal)

    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, receive_signal)
    started = time.monotonic()
    state = {
        "schema": 1, "state": "starting", "started_utc": utc_now(),
        "recorder_pid": os.getpid(), "child": None, "child_returncode": None,
        "child_status": "no_child_handle",
        "recorder_outcome": None, "recorder_exit_code": None,
        "interrupt_signal": None,
        "descendant_quiescence_verified": False, "errors": [], "cleanup": None,
    }
    child = None
    child_log = heartbeat_log = errors_log = None
    attempt_created = False
    try:
        check_interruption()
        # mkdir is the no-overwrite boundary, including an existing symlink.
        args.attempt_dir.mkdir(mode=0o700)
        attempt_created = True
        sync_directory(args.attempt_dir.parent)
        child_log = new_log(args.attempt_dir / "child.log")
        heartbeat_log = new_log(args.attempt_dir / "heartbeat.log")
        errors_log = new_log(args.attempt_dir / "errors.log")
        source = Path(__file__).resolve()
        atomic_json(args.attempt_dir / "launch.json", {
            "schema": 1, "started_utc": state["started_utc"],
            "requested": {
                "command": args.command, "cwd": str(args.cwd),
                "attempt_dir": str(args.attempt_dir), "candidate": args.candidate,
                "mode": args.mode, "environment_changes": args.environment_changes,
                "heartbeat_seconds": args.heartbeat_seconds,
                "cleanup_grace_seconds": args.cleanup_grace_seconds,
            },
            "recorder": {
                "pid": os.getpid(), "process_group": os.getpgrp(),
                "session": os.getsid(0), "source_path": str(source),
                "invocation": sys.argv,
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "python_executable": sys.executable,
                "python_executable_resolved": str(Path(sys.executable).resolve()),
                "python_version": sys.version, "python_implementation": sys.implementation.name,
            },
        })
        atomic_json(args.attempt_dir / "run.json", state)
        environment = os.environ.copy()
        environment.update(args.environment_changes)
        check_interruption()
        if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
            raise RuntimeError("SIGCHLD must use its default disposition so actual child waits remain available")
        child = subprocess.Popen(
            args.command, cwd=args.cwd, env=environment, stdin=subprocess.DEVNULL,
            stdout=child_log, stderr=subprocess.STDOUT, start_new_session=True, shell=False,
        )
        state["child"] = {
            "pid": child.pid, "process_group": child.pid, "session": child.pid,
        }
        state["state"] = "running"
        state["child_status"] = "unreaped"
        atomic_json(args.attempt_dir / "run.json", state)
        sequence = 0
        next_heartbeat = 0.0
        while True:
            check_interruption()
            polled = child.poll()
            now = time.monotonic()
            if now >= next_heartbeat or polled is not None:
                sequence += 1
                append_record(heartbeat_log, {
                    "schema": 1, "recorded_utc": utc_now(), "sequence": sequence,
                    "elapsed_seconds": now - started, "child_poll_returncode": polled,
                })
                next_heartbeat = now + args.heartbeat_seconds
            if polled is not None:
                # The authoritative raw value is obtained from wait, even if poll reaped it.
                state["child_returncode"] = child.wait()
                state["child_status"] = "reaped"
                break
            time.sleep(min(0.25, max(0.0, next_heartbeat - time.monotonic())))
        for output in (child_log, heartbeat_log, errors_log):
            os.fsync(output.fileno())
        check_interruption()
        raw = state["child_returncode"]
        state["recorder_exit_code"] = raw if raw >= 0 else 128 - raw
        state["recorder_outcome"] = "completed"
    except BaseException as exc:
        error = {"recorded_utc": utc_now(), "type": type(exc).__name__, "detail": str(exc)}
        state["errors"].append(error)
        report_error(errors_log, error)
        interrupted = isinstance(exc, RecorderInterrupted)
        state["recorder_outcome"] = "interrupted" if interrupted else "failed"
        state["recorder_exit_code"] = 128 + exc.signum if interrupted else 125
        if child is not None:
            state["cleanup"] = stop_owned_child(child, args.cleanup_grace_seconds)
            state["child_returncode"] = state["cleanup"]["child_returncode"]
            state["child_status"] = "reaped" if state["child_returncode"] is not None else "unresolved"
    finally:
        for output in (child_log, heartbeat_log, errors_log):
            if output is not None:
                try:
                    output.close()
                except OSError as exc:
                    error = {"recorded_utc": utc_now(), "close_failure": repr(exc)}
                    state["errors"].append(error)
                    state["recorder_outcome"] = "failed"
                    state["recorder_exit_code"] = 125
                    report_error(None, error)
    state["state"] = "finished"
    state["interrupt_signal"] = pending_signal
    if pending_signal is not None and state["recorder_outcome"] == "completed":
        state["recorder_outcome"] = "interrupted"
        state["recorder_exit_code"] = 128 + pending_signal
    state["finished_utc"] = utc_now()
    state["elapsed_seconds"] = time.monotonic() - started
    if attempt_created:
        try:
            atomic_json(args.attempt_dir / "run.json", state)
        except OSError as exc:
            error = {"recorded_utc": utc_now(), "final_state_write_failure": repr(exc)}
            state["errors"].append(error)
            state["recorder_outcome"] = "failed"
            state["recorder_exit_code"] = 125
            report_error(None, error)
            # One bounded best-effort update, including if the replace succeeded
            # but its directory sync failed. Broken storage may defeat this too.
            try:
                atomic_json(args.attempt_dir / "run.json", state)
            except OSError as retry_error:
                report_error(None, {"final_failure_record_unavailable": repr(retry_error)})
            return 125
    return state["recorder_exit_code"]


if __name__ == "__main__":
    raise SystemExit(record(parse_arguments()))

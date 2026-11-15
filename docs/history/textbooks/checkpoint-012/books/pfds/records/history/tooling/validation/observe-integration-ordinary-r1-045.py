#!/usr/bin/env python3
"""Display progress from the unchanged approved controller; no gate substitution.

This is execution-service observation metadata for one uniquely named retry.
It changes no child environment, resource limit, checker input or evidence.
The controller continues to own its stock checker and both scheduling locks.
An absent terminal receipt remains incomplete. Never reuse recorded PIDs.
"""
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import signal
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
RUN_ID = "integration-3cf-ordinary-r1-045"
DIRECTORY = ROOT / "session/validation"
RECEIPT = DIRECTORY / (RUN_ID + "-observer.json")
LOG = DIRECTORY / (RUN_ID + ".log")
COMMAND = [sys.executable, "-u", str(DIRECTORY / "run-native-validation.py"),
           "full", RUN_ID, "--scope", "integration"]


def now():
    return datetime.now(timezone.utc).isoformat()


def save(record, *, create=False):
    with RECEIPT.open("x" if create else "w") as stream:
        json.dump(record, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())


def main():
    record = {"kind": "read-only-log-progress-relay", "started_at": now(),
              "run_id": RUN_ID, "command": COMMAND, "cwd": str(ROOT),
              "pty": False, "controller_start_new_session": True,
              "child_environment": "inherited without modification",
              "resource_limits_changed": False, "status": "starting",
              "terminal_result_observed": False, "acceptance": False}
    save(record, create=True)
    child = None
    cancellation_signal = None
    cancellation_sent = False

    def request_cancellation(signum):
        nonlocal cancellation_signal, cancellation_sent
        if cancellation_signal is None:
            cancellation_signal = signum
        if child is not None and not cancellation_sent and child.poll() is None:
            cancellation_sent = True
            child.send_signal(cancellation_signal)

    def forward(signum, _frame):
        request_cancellation(signum)

    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, forward)
    try:
        child = subprocess.Popen(COMMAND, cwd=ROOT, start_new_session=True)
        if cancellation_signal is not None:
            request_cancellation(cancellation_signal)
        record.update(status="observing", controller_pid_this_invocation_only=child.pid)
        save(record)
        while True:
            progress = []
            if LOG.is_file():
                progress = [line for line in LOG.read_text(errors="replace").splitlines()
                            if line.strip()]
            print(f"Observer {now()}: " + (progress[-1][-500:] if progress else "waiting for checker output"),
                  flush=True)
            try:
                result = child.wait(timeout=20)
                break
            except subprocess.TimeoutExpired:
                pass
    finally:
        if child is not None and child.poll() is None:
            request_cancellation(signal.SIGTERM)  # Controller owns checker cleanup.
            child.wait()
    record.update(status="finished", ended_at=now(), terminal_result_observed=True,
                  controller_exit_code=result, cancellation_signal=cancellation_signal,
                  cancellation_sent=cancellation_sent)
    save(record)
    print(f"Controller actually returned {result}; observer receipt: {RECEIPT}", flush=True)
    return 128 - result if result < 0 else result


if __name__ == "__main__":
    raise SystemExit(main())

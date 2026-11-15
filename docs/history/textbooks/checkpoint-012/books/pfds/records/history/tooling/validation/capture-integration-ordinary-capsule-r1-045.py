#!/usr/bin/env python3
"""Unexecuted, fixed ordinary-output recovery capsule; never acceptance.

The four PINNED values intentionally start as None. Actual successful evidence
and reviewed binding-only edits are required before this command can proceed.
Invoke this file without arguments from any directory; paths derive from it.

Only root/the execution owner may create the separate terminal witness, AFTER
the actual regression tool session returns. Its exact schema is:
  {"schema": 1, "kind": "regression-driver-outer-terminal-observation",
   "run_id": REGRESSION_RUN, "candidate": CANDIDATE,
   "argv": ["python3", "-u", str(REGRESSION_DRIVER)], "cwd": str(ROOT),
   "driver_source_sha256": <actual reviewed driver SHA256>,
   "regression_record": {"path": <ROOT-relative regression JSON>,
                         "sha256": <actual completed regression JSON SHA256>},
   "observation_source": "execution-service terminal return",
   "execution_session_id": <actual positive integer tool-session ID>,
   "observed_at": <timezone-aware ISO timestamp>,
   "terminal_result_observed": true, "observed_exit_code": 0,
   "acceptance": false}
The outer argv above and cwd ROOT are required literally. A completed inner
JSON or a progress line is not an outer terminal observation. This script only
reads that witness; it cannot create one. Witness metadata remains trusted root
bookkeeping, not an independently authenticated claim about a tool service.

Both scheduler locks remain held through preflight, private-copy inspection,
owned-child cleanup, archive transport verification and final evidence. Real
hash work uses the unchanged stock adapter under the approved kit environment.
No donor output is repaired, removed, linked, renamed or written. The optional
archive contains no fresh outputs, dependencies, runtime, verification record
or approval. Its completed transport is not a new stock gate or a fresh baseline.
"""

from contextlib import ExitStack
from datetime import datetime, timezone
from pathlib import Path
import fcntl
import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import time


sys.dont_write_bytecode = True
SELF = Path(__file__).resolve()
ROOT = SELF.parents[2]
DIRECTORY = ROOT / "session/validation"
DONOR = ROOT / "validation-pfds-integration"
STATE = ROOT / "native-state"
CANDIDATE = "3cf3de4fbc24c1a144353ae64b13b72f5ead54a5"
RUN_ID = "integration-3cf-ordinary-capsule-r1-045"
ORDINARY_RUN = "integration-3cf-ordinary-r3-045"
REGRESSION_RUN = "integration-3cf-stock-regressions-r1-045"
REGRESSION_DRIVER = DIRECTORY / "run-integration-regressions-r1-045.py"
REGRESSION_RECORD = DIRECTORY / (REGRESSION_RUN + ".json")
TERMINAL_RECEIPT = DIRECTORY / (REGRESSION_RUN + "-terminal.json")
RUNNER = DIRECTORY / "run-native-validation.py"
RUNNER_SHA256 = "4965f8b3eae19955cf43e2a46403fafd374cc5a27994f00507df0fae827fd55e"
PINNED = {
    "ordinary_record_sha256": None,
    "regression_driver_sha256": None,
    "regression_record_sha256": None,
    "terminal_receipt_sha256": None,
}
STAGE = ROOT / (RUN_ID + "-stage")
OUTPUT = ROOT / "checkpoints/conaled-pfds-ordinary-capsule-r1-045.tar.gz"
PARTIAL = OUTPUT.with_name(OUTPUT.name + ".partial")
RECORD = DIRECTORY / (RUN_ID + ".json")
CANCEL_FILE = DIRECTORY / (RUN_ID + ".cancel")
BATCH_BYTES = 64 * 1024 * 1024
HEADROOM = 512 * 1024 * 1024
METADATA_ALLOWANCE = 32 * 1024 * 1024
ARCHIVE_LIMIT = 512 * 1024 * 1024
HASH_COMMAND_CAP = 3600
TERM_GRACE = 10
CONFIG = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "flake.nix", "flake.lock",
          "scripts/lake_integrity.py", "scripts/lake-output-hashes.lean", "scripts/check.py")
STAGES = (
    ("proof-audit-build", ["lake", "--no-cache", "--rehash", "build", "+ProofAudit"]),
    ("checker", ["python3", "scripts/test-check.py"]),
    ("roots", ["python3", "scripts/test-proof-audit-roots.py"]),
    ("negative-audit", ["lake", "env", "python3", "scripts/test-proof-audit.py"]),
)
PROBES = tuple((f"elan-{when}-{kind}", argv) for when in ("before", "after")
               for kind, argv in (("version", ["elan", "--version"]),
                                  ("which-lean", ["elan", "which", "lean"])))
EXPECTED_COMMANDS = PROBES[:2] + STAGES + PROBES[2:]
FINAL_CHECKS = {"frozen_inputs_and_driver", "ordinary_evidence_and_live_verification",
                "elan_and_environment", "proof_audit_artifacts", "retained_command_logs"}
HASH_WORKER = """import importlib.util, json, os, pathlib, sys
root = pathlib.Path(sys.argv[1])
spec = importlib.util.spec_from_file_location('fixed_capsule_guard', root / 'scripts/lake_integrity.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
guard.validate_layout(root)
bad, count = guard.inspect_outputs(root, json.loads(sys.argv[2]), os.environ.copy())
print(json.dumps({'inconsistencies': bad, 'hashed_artifacts': count}), flush=True)
raise SystemExit(1 if bad else 0)
"""

README = f"""# Optional ordinary project-output capsule

Candidate: {CANDIDATE}. Restore a separate mandatory source/history/session
checkpoint containing that exact commit and the originating validation evidence
first. This archive cannot restore sources, dependencies or the runtime.

Verify the externally recorded archive SHA256. Inspect/extract into a NEW empty
directory, rejecting duplicate members, links, nonregular members, absolute paths
and parent traversal. Verify every member's size and SHA256. SHA256SUMS lists all
other files, including manifest.json; it excludes itself. manifest.json's files
table excludes both itself and SHA256SUMS to avoid self-reference.

Create a NEW clean checkout at the exact candidate. Recreate the supplied unified
Lean 4.35.0 kit/profile and clean pinned dependencies using the mandatory checkpoint
runbook. Match source/configuration and runtime identities in manifest.json.
Require a private EMPTY project-build destination and no competing writers.
Hold the established full/focused scheduler locks during restoration/inspection.

Restore only listed whole groups from candidates/{CANDIDATE}/, retaining their
relative .lake/build paths. Copy required artifacts and retained optional hash
sidecars first, with each original trace last. Never merge candidate namespaces,
overwrite existing groups, copy .lake/verification.json or rewrite trace bytes.
Historical paths inside traces are provenance, not an instruction to recreate
or edit them. Run unchanged scripts/lake_integrity.py inspect_outputs on the
restored private groups under the approved kit environment, without repair.

Release the restoration locks before the approved validation controller CLI
acquires them. Run a NEW stock ordinary full candidate check on the restored
candidate. Stock Lake rehashes inputs and decides what can be reused; no universal
cache hit after relocation is promised. Preserve its actual exhaustive audit and
new verification evidence. Any outstanding mandatory fresh baseline, regressions,
independent reviews and immediate final verification remain required.

Capture validates fixed private trace/artifact agreement with the unchanged real
Lake hash adapter and verifies archive transport. Neither establishes derivation
from claimed source under hostile substitution or excludes every external race.
No source, dependency/runtime cache, fresh output, verification record or approval
is included. acceptance=false; approval_copied=false. Donor outputs are retained.
""".encode()


class Refusal(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Refusal(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def timestamp(value):
    result = datetime.fromisoformat(value)
    require(result.tzinfo is not None, "Evidence timestamp lacks a timezone")
    return result


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def stat_fields(value):
    return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)


def file_state(path):
    require(path.resolve(strict=True) == path, f"Linked file or parent refused: {path}")
    value = path.lstat()
    require(stat.S_ISREG(value.st_mode), f"Expected regular file: {path}")
    return stat_fields(value)


def identity(path):
    before = file_state(path)
    result = {"path": str(path), "bytes": before[2], "sha256": digest(path)}
    require(file_state(path) == before, f"File changed while hashing: {path}")
    return result


def selected_identity(path, expected):
    actual = identity(path)
    require(actual["sha256"] == expected["sha256"] and actual["bytes"] == expected["bytes"],
            f"Retained evidence or artifact changed: {path}")
    return actual


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"Cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def space_observation():
    value = os.statvfs(ROOT)
    effective_uid = os.geteuid()
    return {"observed_at": now(), "available_bytes": value.f_bavail * value.f_frsize,
            "free_bytes_including_reserved": value.f_bfree * value.f_frsize,
            "effective_uid": effective_uid,
            "admission_free_bytes": (value.f_bfree if effective_uid == 0 else value.f_bavail) * value.f_frsize,
            "admission_basis": "f_bfree (effective UID 0)" if effective_uid == 0
                               else "f_bavail (effective UID != 0)"}


class Cancellation:
    def __init__(self):
        self.data = None

    def signal(self, signum, _frame):
        if self.data is None:
            self.data = {"source": "signal", "signal": signum, "requested_at": now()}

    def poll(self):
        if self.data is not None:
            return
        details = {"source": "fixed request file", "path": str(CANCEL_FILE.relative_to(ROOT))}
        try:
            fd = os.open(CANCEL_FILE, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        except FileNotFoundError:
            return
        except OSError as error:
            details["read_error"] = str(error)
        else:
            try:
                metadata = os.fstat(fd)
                require(stat.S_ISREG(metadata.st_mode), "Cancellation request is not regular")
                raw = os.read(fd, 8193)
                details.update(reason_text=raw[:8192].decode("utf-8", errors="replace"),
                               truncated=len(raw) > 8192 or metadata.st_size > len(raw),
                               captured_prefix_sha256=hashlib.sha256(raw[:8192]).hexdigest())
            except (OSError, Refusal) as error:
                details["read_error"] = str(error)
            finally:
                os.close(fd)
        if self.data is None:
            self.data = {**details, "requested_at": now()}

    def check(self):
        self.poll()
        require(self.data is None, "Capsule cancellation requested")


def prerequisites(runner):
    """Read actual separately produced evidence; never create a success witness."""
    full = runner.full_evidence(ROOT, ORDINARY_RUN, "integration")
    require(full["record_sha256"] == PINNED["ordinary_record_sha256"]
            and full["record"]["verification_mode"] == "incremental",
            "Ordinary-r3 evidence does not match its reviewed successful binding")
    for path, key in ((REGRESSION_DRIVER, "regression_driver_sha256"),
                      (REGRESSION_RECORD, "regression_record_sha256"),
                      (TERMINAL_RECEIPT, "terminal_receipt_sha256")):
        require(identity(path)["sha256"] == PINNED[key], f"Pinned evidence changed: {path}")
    regression = json.loads(REGRESSION_RECORD.read_bytes())
    require(regression.get("schema") == 1 and regression.get("run_id") == REGRESSION_RUN
            and regression.get("candidate") == CANDIDATE
            and regression.get("candidate_scope") == "integration"
            and regression.get("checkout") == "validation-pfds-integration"
            and regression.get("runtime") == "unified-native-kit"
            and regression.get("ordinary_full_run") == ORDINARY_RUN
            and regression.get("status") == "finished" and regression.get("result") == "passed"
            and type(regression.get("driver_exit_code")) is int and regression["driver_exit_code"] == 0
            and regression.get("acceptance") is False and regression.get("failures") == []
            and regression.get("all_stages_passed") is True
            and regression.get("all_required_command_terminals_observed") is True,
            "Regression record is not the required genuine complete success")
    binding = regression["ordinary_binding"]
    require(binding == {"record": f"session/validation/{ORDINARY_RUN}.json",
                        "record_sha256": full["record_sha256"],
                        "log_sha256": full["record"]["log_sha256"],
                        "verification_sha256": hashlib.sha256(full["verification"]).hexdigest(),
                        "verification_mode": "incremental"}, "Regression ordinary binding differs")
    require(regression["inputs_before"] == regression["inputs_after"] == full["record"]["final_inputs"],
            "Regression and ordinary input identities differ")
    require(regression.get("final_checks") == {key: True for key in FINAL_CHECKS}
            and regression["cancellation"]["requested_at"] is None,
            "Regression final checks or cancellation state differ")
    require(Path(regression["driver_source"]["path"]) == REGRESSION_DRIVER,
            "Regression source path differs")
    selected_identity(REGRESSION_DRIVER, regression["driver_source"])
    commands = regression["commands"]
    require(len(commands) == len(EXPECTED_COMMANDS), "Regression command coverage differs")
    for item, (name, argv) in zip(commands, EXPECTED_COMMANDS):
        require(item.get("name") == name and item.get("argv") == argv
                and item.get("cwd") == str(DONOR) and item.get("status") == "finished"
                and type(item.get("command_exit_code")) is int and item["command_exit_code"] == 0
                and item.get("terminal_result_observed") is True
                and item.get("group_quiescence_observed") is True and item.get("passed") is True
                and item.get("timed_out") is False and item.get("cancellation_requested") is False
                and not item.get("cleanup_errors"), f"Actual regression command did not pass: {name}")
        log = DIRECTORY / (REGRESSION_RUN + "-" + name + ".log")
        require(item["log"] == str(log.relative_to(ROOT)), "Regression log path differs")
        selected_identity(log, item["log_identity"])
    for when in ("before", "after"):
        path = DIRECTORY / (REGRESSION_RUN + f"-verification-{when}.json")
        selected_identity(path, regression[f"live_verification_{when}"])
        require(path.read_bytes() == full["verification"], "Retained regression verification differs")
    require(bool(regression["proof_audit_artifacts_after"])
            and regression["proof_audit_artifacts_after_build"] == regression["proof_audit_artifacts_after"],
            "Regression ProofAudit artifact generations differ")
    for relative, expected in regression["proof_audit_artifacts_after"].items():
        path = DONOR / relative
        require(path.is_relative_to(DONOR / ".lake/build"), "Unexpected ProofAudit artifact path")
        selected_identity(path, expected)
    witness = json.loads(TERMINAL_RECEIPT.read_bytes())
    keys = {"schema", "kind", "run_id", "candidate", "argv", "cwd", "driver_source_sha256",
            "regression_record", "observation_source", "execution_session_id", "observed_at",
            "terminal_result_observed", "observed_exit_code", "acceptance"}
    require(set(witness) == keys and witness["schema"] == 1
            and witness["kind"] == "regression-driver-outer-terminal-observation"
            and witness["run_id"] == REGRESSION_RUN and witness["candidate"] == CANDIDATE
            and witness["argv"] == ["python3", "-u", str(REGRESSION_DRIVER)]
            and witness["cwd"] == str(ROOT)
            and witness["driver_source_sha256"] == PINNED["regression_driver_sha256"]
            and witness["regression_record"] == {"path": str(REGRESSION_RECORD.relative_to(ROOT)),
                                                 "sha256": PINNED["regression_record_sha256"]}
            and witness["observation_source"] == "execution-service terminal return"
            and type(witness["execution_session_id"]) is int and witness["execution_session_id"] > 0
            and witness["terminal_result_observed"] is True
            and type(witness["observed_exit_code"]) is int and witness["observed_exit_code"] == 0
            and witness["acceptance"] is False, "Missing or mismatched actual outer terminal witness")
    require(timestamp(full["record"]["ended_at"]) <= timestamp(regression["created_at"])
            <= timestamp(regression["ended_at"]) <= timestamp(witness["observed_at"])
            <= timestamp(now()), "Originating evidence chronology differs")
    live = DONOR / ".lake/verification.json"
    file_state(live)
    require(live.read_bytes() == full["verification"], "Live ordinary verification differs")
    return full, regression, witness


class Capture:
    def __init__(self, runner, cancellation):
        self.runner, self.cancellation = runner, cancellation
        self.env = None
        self.record = {"schema": 1, "kind": "optional ordinary project-output capsule",
                       "run_id": RUN_ID, "candidate": CANDIDATE,
                       "checkout": "validation-pfds-integration", "started_at": now(),
                       "status": "preflight", "acceptance": False, "approval_copied": False,
                       "capture_source": identity(SELF), "evidence_pins": dict(PINNED),
                       "stage": str(STAGE), "partial_archive": str(PARTIAL),
                       "limits": {"batch_bytes": BATCH_BYTES, "headroom_bytes": HEADROOM,
                                  "metadata_allowance_bytes": METADATA_ALLOWANCE,
                                  "archive_ceiling_bytes": ARCHIVE_LIMIT},
                       "capacity_note": "UID-aware observed capacity; no future sufficiency guarantee",
                       "files": {}, "groups": [], "skipped": {}, "hash_commands": [],
                       "space_checks": [], "donor_retirement": False}

    def save(self, *, create=False):
        self.record["cancellation"] = self.cancellation.data
        self.runner.save_record(RECORD, self.record, create=create)

    def require_space(self, extra, phase):
        self.cancellation.check()
        observation = space_observation()
        observation.update(phase=phase, required_bytes=HEADROOM + METADATA_ALLOWANCE + extra)
        self.record["space_checks"].append(observation)
        require(observation["admission_free_bytes"] >= observation["required_bytes"],
                f"Insufficient observed capacity for {phase}; preserve partial state")

    @staticmethod
    def group_exists(pgid):
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            return False
        return True

    def progress(self, command, started):
        log = ROOT / command["log"]
        with log.open("rb") as stream:
            stream.seek(max(0, os.fstat(stream.fileno()).st_size - 4096))
            lines = stream.read().decode("utf-8", errors="replace").splitlines()
        last = next((line.strip() for line in reversed(lines) if line.strip()), "waiting for stock hash output")
        print(f"{now()} capsule hash {command['batch']} {command['status']} "
              f"{time.monotonic() - started:.1f}s: {last[-500:]}", flush=True)

    def settle(self, child, command, started):
        command["status"] = "cleanup_pending"
        began = command.setdefault("cleanup_started_monotonic", time.monotonic())
        signals = command.setdefault("cleanup_signals", [])
        sent = {event["signal"] for event in signals}
        next_display = 0
        while True:
            self.cancellation.poll()
            try:
                present = self.group_exists(child.pid)
            except OSError:
                present = True
            sig = signal.SIGTERM if time.monotonic() - began < TERM_GRACE else signal.SIGKILL
            if present and int(sig) not in sent:
                sent.add(int(sig))
                event = {"signal": int(sig), "at": now(), "owned_pgid": child.pid}
                try:
                    os.killpg(child.pid, sig)
                    event["result"] = "sent"
                except ProcessLookupError:
                    event["result"] = "group_absent"
                except OSError as error:
                    event["result"] = str(error)
                signals.append(event)
            if not command["terminal_result_observed"]:
                try:
                    command["exit_code"] = child.wait(timeout=0.2)
                    command["terminal_result_observed"] = True
                except subprocess.TimeoutExpired:
                    pass
                except OSError as error:
                    command["wait_error"] = str(error)
            try:
                absent = not self.group_exists(child.pid)
            except OSError:
                absent = False
            if command["terminal_result_observed"] and absent:
                command.update(group_quiescence_observed=True, cleanup_finished_at=now())
                return
            if time.monotonic() >= next_display:
                try:
                    self.save()
                    self.progress(command, started)
                except Exception as error:
                    command["cleanup_recording_error"] = str(error)
                next_display = time.monotonic() + 20
            # killpg(0) cannot distinguish a residual zombie. Keep both locks
            # and incomplete evidence until actual group absence is observed.
            time.sleep(0.2)

    def inspect_batch(self, groups):
        index = len(self.record["hash_commands"]) + 1
        names = [group["module"] for group in groups]
        log = DIRECTORY / (RUN_ID + f"-hash-{index:04d}.log")
        command = {"batch": index, "modules": names,
                   "argv": [sys.executable, "-B", "-c", HASH_WORKER, str(STAGE), json.dumps(names)],
                   "cwd": str(STAGE), "environment": self.record["hash_environment"],
                   "log": str(log.relative_to(ROOT)), "started_at": now(), "status": "starting",
                   "wall_limit_seconds": HASH_COMMAND_CAP, "exit_code": None,
                   "terminal_result_observed": False, "group_quiescence_observed": False,
                   "timed_out": False}
        self.record["hash_commands"].append(command)
        self.save()
        child, failure = None, None
        started = time.monotonic()
        try:
            with log.open("xb", buffering=0) as stream:
                try:
                    self.cancellation.check()
                    child = subprocess.Popen(command["argv"], cwd=STAGE, env=self.env,
                                             stdout=stream, stderr=subprocess.STDOUT,
                                             start_new_session=True, close_fds=True)
                    command.update(status="running", owned_pgid_this_invocation_only=child.pid)
                    self.save()
                    next_display = started
                    while True:
                        self.cancellation.check()
                        remaining = HASH_COMMAND_CAP - (time.monotonic() - started)
                        if remaining <= 0:
                            command["timed_out"] = True
                            raise Refusal("Whole hash-command wall cap reached")
                        if time.monotonic() >= next_display:
                            self.progress(command, started)
                            next_display = time.monotonic() + 20
                        try:
                            code = child.wait(timeout=min(1, remaining))
                        except subprocess.TimeoutExpired:
                            continue
                        command.update(exit_code=code, terminal_result_observed=True)
                        require(code == 0, f"Stock private-copy inspection actually returned {code}")
                        require(not self.group_exists(child.pid), "Hash descendants outlived their leader")
                        command["group_quiescence_observed"] = True
                        self.cancellation.check()
                        break
                except (Exception, KeyboardInterrupt) as error:
                    failure = error
                    command["failure"] = f"{type(error).__name__}: {error}"
                finally:
                    if child is not None and not command["group_quiescence_observed"]:
                        self.settle(child, command, started)
                    stream.flush()
                    os.fsync(stream.fileno())
        except (Exception, KeyboardInterrupt) as error:
            failure = failure or error
            command.setdefault("failure", f"{type(error).__name__}: {error}")
            if child is not None and not command["group_quiescence_observed"]:
                self.settle(child, command, started)
        command.update(status="finished", ended_at=now(), elapsed_seconds=time.monotonic() - started)
        if log.is_file():
            command["log_identity"] = identity(log)
        self.save()
        require(failure is None and command["exit_code"] == 0
                and command["terminal_result_observed"] and command["group_quiescence_observed"],
                command.get("failure", "Hash command did not finish successfully"))
        result = json.loads(log.read_bytes())
        require(result.get("inconsistencies") == {}
                and type(result.get("hashed_artifacts")) is int
                and result["hashed_artifacts"] == sum(group["required_artifact_count"] for group in groups),
                "Real stock inspection result differs from the complete staged groups")
        command["stock_result"] = result
        self.save()


def source_digest_fixed(source, expected, cancellation):
    cancellation.check()
    require(file_state(source) == expected, f"Source changed before bounded rehash: {source}")
    value = hashlib.sha256()
    with source.open("rb") as incoming:
        require(stat_fields(os.fstat(incoming.fileno())) == expected,
                f"Opened source identity differs before bounded rehash: {source}")
        remaining = expected[2]
        while remaining:
            cancellation.check()
            block = incoming.read(min(1024 * 1024, remaining))
            require(bool(block), f"Source shortened during bounded rehash: {source}")
            value.update(block)
            remaining -= len(block)
        cancellation.check()
        require(incoming.read(1) == b"", f"Source grew during bounded rehash: {source}")
        require(stat_fields(os.fstat(incoming.fileno())) == expected,
                f"Opened source changed during bounded rehash: {source}")
    require(file_state(source) == expected, f"Source path changed during bounded rehash: {source}")
    return value.hexdigest()


def copy_fixed(source, destination, expected, cancellation):
    require(file_state(source) == expected, f"Source changed since sizing: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    value = hashlib.sha256()
    with source.open("rb") as incoming, destination.open("xb") as outgoing:
        require(stat_fields(os.fstat(incoming.fileno())) == expected,
                f"Opened source identity differs: {source}")
        remaining = expected[2]
        while remaining:
            cancellation.check()
            block = incoming.read(min(1024 * 1024, remaining))
            require(bool(block), f"Source shortened while copying: {source}")
            outgoing.write(block)
            value.update(block)
            remaining -= len(block)
        require(incoming.read(1) == b"", f"Source grew while copying: {source}")
        outgoing.flush()
        os.fsync(outgoing.fileno())
    require(source_digest_fixed(source, expected, cancellation) == value.hexdigest(),
            f"Source content changed during copying: {source}")
    return {"path": str(source.relative_to(DONOR)), "bytes": expected[2], "sha256": value.hexdigest()}


def capture_locked(runner, cancellation):
    existing = [path for path in DIRECTORY.glob(RUN_ID + "*") if path != CANCEL_FILE]
    require(not existing, "Capsule evidence namespace already exists; preserve the earlier attempt")
    for path in (STAGE, OUTPUT, PARTIAL):
        require(not path.exists() and not path.is_symlink(), f"Exclusive capsule path exists: {path}")
    capture = Capture(runner, cancellation)
    record = capture.record
    capture.save(create=True)
    before = full = None
    try:
        cancellation.check()
        for path in (DONOR, DONOR / ".lake", DONOR / ".lake/build"):
            require(path.is_dir() and path.resolve(strict=True) == path, "Donor/build must be real private directories")
        full, regression, witness = prerequisites(runner)
        before = runner.snapshot(ROOT, DONOR, False, "integration")
        runner.require_frozen(before, CANDIDATE)
        require(before == full["record"]["final_inputs"], "Current inputs differ from genuine originating gates")
        record["inputs_before"] = before
        record["originating_evidence"] = {
            "ordinary_run": ORDINARY_RUN, "ordinary_record_sha256": full["record_sha256"],
            "ordinary_log_sha256": full["record"]["log_sha256"],
            "ordinary_verification_sha256": hashlib.sha256(full["verification"]).hexdigest(),
            "regression_run": REGRESSION_RUN, "regression_record_sha256": PINNED["regression_record_sha256"],
            "regression_driver_sha256": PINNED["regression_driver_sha256"],
            "terminal_receipt": str(TERMINAL_RECEIPT.relative_to(ROOT)),
            "terminal_receipt_sha256": PINNED["terminal_receipt_sha256"],
            "outer_terminal_observed_at": witness["observed_at"],
        }
        kit = runner.unified_kit(ROOT)
        kit.check_project(DONOR)
        capture.env = kit.environment(STATE, 1)
        require(capture.env.get("LEAN") is None and capture.env.get("LEAN_PATH") is None,
                "Kit retained an outer compiler/search-path override")
        keys = set(before["direct_environment"]["environment"]) | {
            "PYTHONPATH", "PYTHONHOME", "PYTHONOPTIMIZE", "PYTHONDONTWRITEBYTECODE"}
        record["hash_environment"] = {key: capture.env.get(key) for key in sorted(keys)}
        require({key: capture.env.get(key) for key in before["direct_environment"]["environment"]}
                == before["direct_environment"]["environment"], "Current kit environment selection differs")
        record["hash_python"] = identity(Path(sys.executable).resolve())
        capture.require_space(0, "initial staging")
        STAGE.mkdir()
        OUTPUT.parent.mkdir(exist_ok=True)
        require(OUTPUT.parent.resolve(strict=True) == OUTPUT.parent, "Archive directory is linked")
        config_hashes = {}
        for relative in CONFIG:
            source = DONOR / relative
            require(identity(source)["sha256"] == before["source_inputs"][relative], "Configuration source changed")
            target = STAGE / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open("xb") as stream:
                stream.write(source.read_bytes())
            require(digest(target) == before["source_inputs"][relative], "Private configuration copy differs")
            config_hashes[relative] = digest(target)
        record["configuration_sha256"] = config_hashes
        guard = load_module("capsule_fixed_guard", STAGE / "scripts/lake_integrity.py")
        guard.validate_layout(STAGE)
        record["status"] = "capturing"
        capture.save()
        pending, pending_bytes, metadata_bytes = [], 0, 0

        with PARTIAL.open("xb") as raw_archive:
            with tarfile.open(fileobj=raw_archive, mode="w:gz", compresslevel=3) as archive:
                def add_bytes(name, data):
                    nonlocal metadata_bytes
                    require(name not in record["files"], "Duplicate capsule member")
                    metadata_bytes += len(data)
                    require(metadata_bytes <= METADATA_ALLOWANCE, "Capsule metadata allowance exceeded")
                    member = tarfile.TarInfo(name)
                    member.size, member.mode = len(data), 0o644
                    archive.addfile(member, io.BytesIO(data))
                    record["files"][name] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

                def flush():
                    nonlocal pending_bytes
                    if not pending:
                        return
                    require(pending_bytes <= BATCH_BYTES, "Private batch exceeds the fixed ceiling")
                    capture.require_space(pending_bytes, "stock inspection and compression")
                    capture.inspect_batch(pending)
                    for group in pending:
                        for item in group["files"]:
                            cancellation.check()
                            path = STAGE / item["path"]
                            selected_identity(path, item)
                            name = f"candidates/{CANDIDATE}/" + item["path"]
                            require(name not in record["files"], "Duplicate artifact member")
                            member = tarfile.TarInfo(name)
                            member.size, member.mode = item["bytes"], 0o644
                            with path.open("rb") as stream:
                                archive.addfile(member, stream)
                            record["files"][name] = {"bytes": item["bytes"], "sha256": item["sha256"]}
                        record["groups"].append(group)
                    archive.fileobj.flush()
                    raw_archive.flush()
                    os.fsync(raw_archive.fileno())
                    require(PARTIAL.stat().st_size <= ARCHIVE_LIMIT, "Compressed archive ceiling reached")
                    capture.save()
                    # Only this invocation's private staged copies are removed.
                    shutil.rmtree(STAGE / ".lake/build")
                    pending.clear()
                    pending_bytes = 0

                add_bytes("README.md", README)
                library = DONOR / ".lake/build/lib/lean"
                for trace in sorted(library.rglob("*.trace")):
                    cancellation.check()
                    relative = trace.relative_to(library).with_suffix("")
                    module, lean = ".".join(relative.parts), str(relative.with_suffix(".lean"))
                    if lean not in before["source_inputs"]:
                        record["skipped"][module] = "No corresponding tracked source module"
                        continue
                    trace_state = file_state(trace)
                    trace_bytes = trace.read_bytes()
                    require(file_state(trace) == trace_state, "Trace changed while reading")
                    try:
                        described = guard.expected_artifacts(DONOR, module)
                    except ValueError as error:
                        if str(error) in {"missing " + ext for ext in (*guard.LIB_EXTENSIONS, *guard.IR_EXTENSIONS)}:
                            record["skipped"][module] = "Incomplete source group: " + str(error)
                            continue
                        raise
                    artifacts = [path for path, _ in described]
                    paths = []
                    for artifact in artifacts:
                        paths.append(artifact)
                        sidecar = artifact.with_name(artifact.name + ".hash")
                        if sidecar.exists() or sidecar.is_symlink():
                            paths.append(sidecar)
                    sized = [(path, file_state(path)) for path in paths]
                    size = len(trace_bytes) + sum(value[2] for _, value in sized)
                    if size > BATCH_BYTES:
                        record["skipped"][module] = "Whole group exceeds 64 MiB staging ceiling"
                        continue
                    if pending and pending_bytes + size > BATCH_BYTES:
                        flush()
                    capture.require_space(2 * size + pending_bytes, "whole-group staging")
                    files = [copy_fixed(path, STAGE / path.relative_to(DONOR), value, cancellation)
                             for path, value in sized]
                    require(file_state(trace) == trace_state and trace.read_bytes() == trace_bytes,
                            "Source trace changed during whole-group copy")
                    target_trace = STAGE / trace.relative_to(DONOR)
                    target_trace.parent.mkdir(parents=True, exist_ok=True)
                    with target_trace.open("xb") as stream:
                        stream.write(trace_bytes)
                        stream.flush()
                        os.fsync(stream.fileno())
                    files.append({"path": str(trace.relative_to(DONOR)), "bytes": len(trace_bytes),
                                  "sha256": hashlib.sha256(trace_bytes).hexdigest()})
                    require([str(path.relative_to(STAGE)) for path, _ in guard.expected_artifacts(STAGE, module)]
                            == [str(path.relative_to(DONOR)) for path in artifacts],
                            "Fixed staged trace describes a different artifact set")
                    require(identity(DONOR / lean)["sha256"] == before["source_inputs"][lean],
                            "Selected module source changed")
                    pending.append({"module": module, "source": lean,
                                    "source_sha256": before["source_inputs"][lean],
                                    "required_artifact_count": len(artifacts), "files": files, "trace_last": True})
                    pending_bytes += size
                flush()
                require(record["groups"], "No complete ordinary groups were captured")
                record["artifact_capture_ended_at"] = now()
                capture.require_space(0, "final metadata")
                manifest = {"schema": 1, "kind": "optional ordinary project-output recovery",
                            "candidate": CANDIDATE, "tree": before["project"]["tree"],
                            "captured_at": now(), "capture_source": record["capture_source"],
                            "capture_interval": {"started_at": record["started_at"],
                                                 "artifact_capture_ended_at": record["artifact_capture_ended_at"]},
                            "capture_inputs": before, "originating_evidence": record["originating_evidence"],
                            "configuration_sha256": config_hashes, "groups": record["groups"],
                            "skipped": record["skipped"], "hash_commands": record["hash_commands"],
                            "limits": record["limits"], "files": dict(record["files"]),
                            "receipt": str(RECORD.relative_to(ROOT)),
                            "acceptance": False, "approval_copied": False,
                            "self_exclusion": "files excludes manifest.json and SHA256SUMS; SHA256SUMS excludes itself"}
                add_bytes("manifest.json", (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode())
                sums = "".join(value["sha256"] + "  " + name + "\n"
                               for name, value in sorted(record["files"].items()))
                add_bytes("SHA256SUMS", sums.encode())
            raw_archive.flush()
            os.fsync(raw_archive.fileno())
        require(PARTIAL.stat().st_size <= ARCHIVE_LIMIT, "Completed archive exceeds the fixed ceiling")
        record["status"] = "transport_verifying"
        capture.save()
        seen = set()
        with tarfile.open(PARTIAL, "r:gz") as archive:
            for member in archive:
                cancellation.check()
                name = member.name
                require(member.isfile() and name not in seen and name in record["files"]
                        and not Path(name).is_absolute() and ".." not in Path(name).parts,
                        "Unexpected, duplicate or unsafe capsule member")
                expected = record["files"][name]
                require(member.size == expected["bytes"], "Capsule member size differs")
                value = hashlib.sha256()
                with archive.extractfile(member) as stream:
                    for block in iter(lambda: stream.read(1024 * 1024), b""):
                        cancellation.check()
                        value.update(block)
                require(value.hexdigest() == expected["sha256"], "Capsule member bytes differ")
                seen.add(name)
        require(seen == set(record["files"]), "Capsule transport omitted an intended member")
        after = runner.snapshot(ROOT, DONOR, False, "integration")
        runner.require_frozen(after, CANDIDATE)
        record["inputs_after"] = after
        require(after == before, "Source, dependencies, runtime or controller changed during capture")
        require(prerequisites(runner) == (full, regression, witness), "Originating evidence changed during capture")
        require(identity(SELF) == record["capture_source"], "Capture source changed")
        for command in record["hash_commands"]:
            selected_identity(ROOT / command["log"], command["log_identity"])
        capture.require_space(0, "archive publication")
        archive_identity = identity(PARTIAL)
        cancellation.check()
        # Atomic no-replace publication of this completed archive only. The
        # temporary second name never refers to a donor or project artifact.
        os.link(PARTIAL, OUTPUT, follow_symlinks=False)
        PARTIAL.unlink()
        directory_fd = os.open(OUTPUT.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        require(identity(OUTPUT)["sha256"] == archive_identity["sha256"], "Published archive changed")
        shutil.rmtree(STAGE)  # This invocation's private staging directory only.
        cancellation.check()
        record.update(status="completed", ended_at=now(), archive=str(OUTPUT),
                      archive_bytes=archive_identity["bytes"], archive_sha256=archive_identity["sha256"],
                      module_count=len(record["groups"]), inputs_unchanged=True,
                      originating_evidence_unchanged=True,
                      transport="Every unique intended regular member, size and SHA256 verified by streaming",
                      space_after=space_observation())
        capture.save()
        return 0  # No fallible announcement after recording completion.
    except (Exception, KeyboardInterrupt) as error:
        record.update(status="failed; preserve stage and partial/published archive", ended_at=now(),
                      failure=f"{type(error).__name__}: {error}",
                      stage_preserved=STAGE.exists(), partial_archive_preserved=PARTIAL.exists(),
                      published_archive_preserved=OUTPUT.exists())
        if before is not None:
            try:
                after = runner.snapshot(ROOT, DONOR, False, "integration")
                record.update(inputs_after=after, inputs_unchanged=after == before)
                runner.require_frozen(after, CANDIDATE)
            except Exception as final_error:
                record["postcheck_error"] = f"{type(final_error).__name__}: {final_error}"
        capture.save()
        return 1


def main():
    require(len(sys.argv) == 1, "This fixed capsule command accepts no arguments")
    missing = [key for key, value in PINNED.items()
               if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None]
    require(not missing, "Unbound genuine evidence; reviewed binding-only edits still required: " + ", ".join(missing))
    cancellation = Cancellation()
    handlers = {}
    try:
        for signum in (signal.SIGINT, signal.SIGTERM):
            handlers[signum] = signal.signal(signum, cancellation.signal)
        with ExitStack() as locks:
            for name in ("full-build.lock", "focused-build.lock"):
                path = ROOT / "active-validation" / name
                require(path.is_file() and not path.is_symlink(), "Missing established scheduler lock")
                lock = locks.enter_context(path.open("r+b"))
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    raise Refusal("Validation lock is held; capsule work was not launched") from None
            require(identity(RUNNER)["sha256"] == RUNNER_SHA256, "Approved controller source changed")
            runner = load_module("capsule_approved_runner", RUNNER)
            return capture_locked(runner, cancellation)
    finally:
        for signum, handler in handlers.items():
            signal.signal(signum, handler)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Exception, KeyboardInterrupt) as error:
        print(f"Capsule refused or could not finalize: {type(error).__name__}: {error}",
              file=sys.stderr, flush=True)
        raise SystemExit(1)

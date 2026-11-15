#!/usr/bin/env python3
"""One-use regression evidence for the fixed common integration candidate.

Run this file without arguments only after the actual ordinary full run passes.
It retains both scheduling locks through preflight, sequential commands, owned
group cleanup, final identity checks and evidence recording. It does not invoke
the validation controller CLI, install anything, copy fresh outputs or grant
acceptance. The separate genuine fresh baseline and formal reviews remain due.

Each direct command has a new session/process group and a 3600-second wall cap.
Stock 45/15/60-second inner limits and the checker's jobs=2 fixtures are unchanged.
After cancellation/failure, SIGTERM and then SIGKILL are each sent at most once
to this invocation's current owned group, including after its leader exits.
If that group remains observable, cleanup waits with both locks held; it does
not infer quiescence from a dead leader or an unavailable process listing.
Recorded PIDs are diagnostic only and must never be used by a later invocation.
The fixed RUN_ID.cancel file is an optional cancellation request; its contents
are inert reason text. It is checked before commands and during owned waits.
"""

from contextlib import ExitStack
from datetime import datetime, timezone
from pathlib import Path
import fcntl
import hashlib
import importlib.util
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import time


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / "session/validation"
CHECKOUT = ROOT / "validation-pfds-integration"
STATE = ROOT / "native-state"
PROFILE = STATE / "profile"
CANDIDATE = "3cf3de4fbc24c1a144353ae64b13b72f5ead54a5"
RUN_ID = "integration-3cf-stock-regressions-r1-045"
ORDINARY_RUN = "integration-3cf-ordinary-r2-045"
RUNNER_PATH = DIRECTORY / "run-native-validation.py"
RUNNER_SHA256 = "4965f8b3eae19955cf43e2a46403fafd374cc5a27994f00507df0fae827fd55e"
ELAN_RECEIPT = ROOT / "session/environment/unified-elan-setup-045.json"
ELAN_RECEIPT_SHA256 = "ed4203d932713ffed62b61c5b0d9a4a7772e2d6b93e7940114dd712f47aba627"
ELAN_DIRECTORY = ROOT / "toolchains/elan-4.2.4"
ELAN_BINARY_SHA256 = "e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5"
ELAN_SELECTION = "pfds-unified-4.35.0"
ELAN_HOME = STATE / "elan-check-tests"
ELAN_LINK = ELAN_HOME / "toolchains" / ELAN_SELECTION
ELAN_VERSION = "elan 4.2.4 (227caca13 2026-08-25)"
RECORD_PATH = DIRECTORY / (RUN_ID + ".json")
CANCEL_PATH = DIRECTORY / (RUN_ID + ".cancel")
COMMAND_CAP = 3600
TERM_GRACE = 10
DISPLAY_INTERVAL = 20
STAGES = (
    ("proof-audit-build", ["lake", "--no-cache", "--rehash", "build", "+ProofAudit"], "proof"),
    ("checker", ["python3", "scripts/test-check.py"], "checker"),
    ("roots", ["python3", "scripts/test-proof-audit-roots.py"], "base"),
    ("negative-audit", ["lake", "env", "python3", "scripts/test-proof-audit.py"], "base"),
)
PROBES = tuple((f"elan-{when}-{kind}", argv, "checker")
               for when in ("before", "after")
               for kind, argv in (("version", ["elan", "--version"]),
                                  ("which-lean", ["elan", "which", "lean"])))
COMMANDS = PROBES[:2] + STAGES + PROBES[2:]
AUDIT_CASES = ("unused-external-axiom", "private-transitive-axiom",
               "private-admission", "source-unsafe")


class Refusal(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Refusal(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def file_identity(path):
    require(path.is_file(), f"Missing regular file: {path}")
    before = path.stat()
    result = {"path": str(path), "resolved": str(path.resolve(strict=True)),
              "bytes": before.st_size, "sha256": digest(path)}
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns),
            f"File changed while hashing: {path}")
    return result


def import_file(name, path):
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


def private_layout():
    for path in (CHECKOUT, CHECKOUT / ".lake", CHECKOUT / ".lake/build"):
        require(path.is_dir() and not path.is_symlink()
                and path.resolve(strict=True) == path,
                f"Expected a real private integration directory: {path}")
    packages = CHECKOUT / ".lake/packages"
    require(packages.is_symlink() and packages.resolve(strict=True).is_relative_to(ROOT),
            "Integration package link must remain inside the pinned workspace store")
    return {"checkout": str(CHECKOUT), "build": str(CHECKOUT / ".lake/build"),
            "packages_link": os.readlink(packages),
            "packages_resolved": str(packages.resolve(strict=True))}


class Cancellation:
    def __init__(self):
        self.signum = None
        self.requested_at = None
        self.source = None
        self.file_request = None

    def request(self, signum, _frame):
        # No exception or I/O in the handler: Popen ownership assignment completes
        # even if a signal arrives between process creation and its return.
        if self.requested_at is None:
            self.source = "signal"
            self.signum = signum
            self.requested_at = now()

    def poll_file(self):
        if self.requested_at is not None:
            return
        details = {"path": str(CANCEL_PATH.relative_to(ROOT))}
        try:
            fd = os.open(CANCEL_PATH, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        except FileNotFoundError:
            return
        except OSError as error:
            details["read_error"] = str(error)
        else:
            try:
                metadata = os.fstat(fd)
                require(stat.S_ISREG(metadata.st_mode), "Cancellation path is not a regular file")
                raw = os.read(fd, 8193)
                captured = raw[:8192]
                details.update(reason_text=captured.decode("utf-8", errors="replace"),
                               bytes_at_read=metadata.st_size,
                               text_truncated=len(raw) > len(captured) or metadata.st_size > len(captured),
                               captured_prefix_sha256=hashlib.sha256(captured).hexdigest())
            except (OSError, Refusal) as error:
                details["read_error"] = str(error)
            finally:
                os.close(fd)
        # Any existing but unreadable/irregular request also fails closed. No
        # request contents are evaluated or inserted into a command or a path.
        if self.requested_at is None:
            self.source = "fixed cancellation file"
            self.requested_at = now()
            self.file_request = details

    def check(self):
        self.poll_file()
        require(self.requested_at is None, f"Cancellation requested: {self.source}")

    def description(self):
        return {"source": self.source, "signal": self.signum,
                "requested_at": self.requested_at, "file_request": self.file_request}


class Evidence:
    def __init__(self, runner, cancellation):
        self.runner = runner
        self.cancellation = cancellation
        self.envs = {}
        self.environment_keys = ()
        self.record = {
            "schema": 1, "run_id": RUN_ID, "candidate_scope": "integration",
            "candidate": CANDIDATE, "checkout": "validation-pfds-integration",
            "runtime": "unified-native-kit", "acceptance": False,
            "purpose": "Ordinary-output preparation and unchanged stock regression evidence only",
            "ordinary_full_run": ORDINARY_RUN, "created_at": now(),
            "owner_pid_this_invocation_only": os.getpid(), "status": "preflight",
            "driver_source": file_identity(Path(__file__).resolve()),
            "controller_source": file_identity(RUNNER_PATH),
            "locks": ["active-validation/full-build.lock", "active-validation/focused-build.lock"],
            "lock_policy": "exclusive nonblocking; held through cleanup and final evidence",
            "whole_command_wall_limit_seconds": COMMAND_CAP,
            "stock_limits_unchanged": {"checker_seconds": [45, 15], "roots_seconds": 60,
                                       "checker_internal_jobs": 2,
                                       "negative_audit_internal_timeout": None},
            "cleanup_policy": "one TERM, one KILL after 10 s; wait for owned group absence before unlocking",
            "cancellation_request_file": str(CANCEL_PATH.relative_to(ROOT)),
            "failures": [], "commands": [], "all_stages_passed": False,
        }
        for name, argv, environment in COMMANDS:
            self.record["commands"].append({
                "name": name, "argv": argv, "cwd": str(CHECKOUT),
                "environment_name": environment, "status": "not_run",
                "log": str(self.log_path(name).relative_to(ROOT)),
                "command_exit_code": None, "terminal_result_observed": False,
                "group_quiescence_observed": False, "passed": False,
            })

    def log_path(self, name):
        return DIRECTORY / (RUN_ID + "-" + name + ".log")

    def command(self, name):
        return next(value for value in self.record["commands"] if value["name"] == name)

    def save(self, *, create=False):
        self.runner.save_record(RECORD_PATH, self.record, create=create)

    def fail(self, error):
        message = f"{type(error).__name__}: {error}"
        if message not in self.record["failures"]:
            self.record["failures"].append(message)

    def selected_environment(self, env):
        # No complete environment dump: only reviewed compiler/cache/search selectors.
        return {key: env.get(key) for key in self.environment_keys}

    def cleanup_note(self, command, message):
        notes = command.setdefault("cleanup_errors", [])
        if message not in notes:
            notes.append(message)

    def cleanup_save(self, command):
        self.record["cancellation"] = self.cancellation.description()
        try:
            self.save()
        except Exception as error:
            self.cleanup_note(command, f"Evidence write failed during cleanup: {error}")

    def display(self, command, started):
        path = self.log_path(command["name"])
        with path.open("rb") as stream:
            stream.seek(max(0, os.fstat(stream.fileno()).st_size - 8192))
            lines = stream.read().decode("utf-8", errors="replace").splitlines()
        last = next((line.strip() for line in reversed(lines) if line.strip()), "waiting for output")
        print(f"{now()} {command['name']} {command['status']} "
              f"{time.monotonic() - started:.1f}s: {last[-500:]}", flush=True)

    @staticmethod
    def group_exists(pgid):
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            return False
        # PermissionError and other errors are not evidence of group absence.
        return True

    def settle_owned_group(self, child, command, started):
        """Keep ownership until real wait and group absence, even after leader exit."""
        command["status"] = "cleanup_pending"
        command.setdefault("cleanup_started_at", now())
        command.setdefault("cleanup_signals", [])
        began = command.setdefault("cleanup_started_monotonic", time.monotonic())
        sent = {event["signal"] for event in command["cleanup_signals"]}
        next_display = time.monotonic()
        self.cleanup_save(command)
        while True:
            self.cancellation.poll_file()
            try:
                present = self.group_exists(child.pid)
            except OSError as error:
                present = True
                self.cleanup_note(command, f"Cannot establish owned group absence: {error}")
            elapsed = time.monotonic() - began
            sig = signal.SIGKILL if elapsed >= TERM_GRACE else signal.SIGTERM
            if present and sig not in sent:
                # Attempt each signal once. Never replay a historical PID or
                # condition this on child.poll(): descendants may outlive it.
                sent.add(sig)
                event = {"signal": int(sig), "at": now(), "pgid": child.pid}
                try:
                    os.killpg(child.pid, sig)
                    event["result"] = "sent"
                except ProcessLookupError:
                    event["result"] = "group_absent"
                except OSError as error:
                    event["result"] = f"error: {error}"
                    self.cleanup_note(command, f"Owned group signal failed: {error}")
                command["cleanup_signals"].append(event)
                self.cleanup_save(command)
            if not command["terminal_result_observed"]:
                try:
                    command["command_exit_code"] = child.wait(timeout=0.2)
                    command["terminal_result_observed"] = True
                except subprocess.TimeoutExpired:
                    pass
                except OSError as error:
                    self.cleanup_note(command, f"Owned child wait failed: {error}")
            try:
                absent = not self.group_exists(child.pid)
            except OSError as error:
                absent = False
                self.cleanup_note(command, f"Cannot establish owned group absence: {error}")
            if command["terminal_result_observed"] and absent:
                command.update(group_quiescence_observed=True, cleanup_finished_at=now())
                return
            if time.monotonic() >= next_display:
                self.cleanup_save(command)
                try:
                    self.display(command, started)
                except Exception as error:
                    self.cleanup_note(command, f"Progress display failed during cleanup: {error}")
                next_display = time.monotonic() + DISPLAY_INTERVAL
            # A lingering zombie cannot be distinguished here without process
            # enumeration. Retain locks and incomplete evidence rather than
            # misreporting a clean terminal result or overlapping another run.
            time.sleep(0.2)

    def run_command(self, name):
        command = self.command(name)
        require(command["status"] == "not_run", f"Command cannot be repeated: {name}")
        self.cancellation.check()
        command["space_before"] = space_observation()
        require(command["space_before"]["admission_free_bytes"] > 0,
                "No available filesystem space; command refused")
        env = self.envs[command["environment_name"]]
        command["environment"] = self.selected_environment(env)
        command["whole_command_wall_limit_seconds"] = COMMAND_CAP
        command["timed_out"] = False
        command["cancellation_requested"] = False
        command["status"] = "starting"
        command["started_at"] = now()
        self.record["status"] = "running"
        self.save()
        child = None
        error = None
        started = time.monotonic()
        try:
            with self.log_path(name).open("xb", buffering=0) as log:
                try:
                    # The installed handler only records a request, including
                    # during Popen. Child assignment and the cleanup owner are
                    # protected before the first command can be started.
                    self.cancellation.check()
                    child = subprocess.Popen(command["argv"], cwd=CHECKOUT, env=env,
                                             stdout=log, stderr=subprocess.STDOUT,
                                             start_new_session=True, close_fds=True)
                    command.update(status="running", owned_pgid_this_invocation_only=child.pid,
                                   child_pid_this_invocation_only=child.pid)
                    self.save()
                    next_display = started
                    while True:
                        self.cancellation.poll_file()
                        if self.cancellation.requested_at is not None:
                            command["cancellation_requested"] = True
                            raise Refusal(f"Cancellation requested: {self.cancellation.source}")
                        remaining = COMMAND_CAP - (time.monotonic() - started)
                        if remaining <= 0:
                            command["timed_out"] = True
                            raise Refusal(f"Whole-command wall cap of {COMMAND_CAP}s reached")
                        if time.monotonic() >= next_display:
                            self.display(command, started)
                            next_display = time.monotonic() + DISPLAY_INTERVAL
                        try:
                            code = child.wait(timeout=min(1, remaining))
                        except subprocess.TimeoutExpired:
                            continue
                        command.update(command_exit_code=code, terminal_result_observed=True)
                        require(code == 0, f"Command actually returned {code}")
                        require(not self.group_exists(child.pid),
                                "Owned descendants remained after the command leader returned")
                        command["group_quiescence_observed"] = True
                        self.cancellation.check()
                        break
                except (Exception, KeyboardInterrupt) as caught:
                    error = caught
                    command["failure"] = f"{type(caught).__name__}: {caught}"
                finally:
                    if child is not None and not command["group_quiescence_observed"]:
                        self.settle_owned_group(child, command, started)
                    log.flush()
                    os.fsync(log.fileno())
        except (Exception, KeyboardInterrupt) as caught:
            error = error or caught
            command.setdefault("failure", f"{type(caught).__name__}: {caught}")
            # Normally the inner finally already settled the group. This also
            # covers failures after creation but outside normal log handling.
            if child is not None and not command["group_quiescence_observed"]:
                self.settle_owned_group(child, command, started)
        command.update(status="finished", ended_at=now(),
                       elapsed_seconds=time.monotonic() - started)
        if self.log_path(name).is_file():
            command["log_identity"] = file_identity(self.log_path(name))
        command["passed"] = (error is None and command["command_exit_code"] == 0
                             and command["terminal_result_observed"]
                             and command["group_quiescence_observed"]
                             and not command.get("cleanup_errors")
                             and not command["timed_out"]
                             and self.cancellation.requested_at is None)
        self.save()
        require(command["passed"], command.get("failure", f"Command did not pass: {name}"))
        return self.log_path(name).read_bytes()

    def retain_live_verification(self, when):
        live = CHECKOUT / ".lake/verification.json"
        require(live.is_file() and not live.is_symlink(), "Missing or linked live stock verification")
        raw = live.read_bytes()
        retained = DIRECTORY / (RUN_ID + f"-verification-{when}.json")
        with retained.open("xb") as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        self.record[f"live_verification_{when}"] = file_identity(retained)
        return raw


def executable_selections(envs):
    result = {}
    for label in ("base", "checker"):
        result[label] = {}
        for name in (("lean", "lake", "python3") if label == "base"
                     else ("lean", "lake", "python3", "elan")):
            path = shutil.which(name, path=envs[label]["PATH"])
            require(path is not None, f"Missing {name} in {label} environment")
            result[label][name] = file_identity(Path(path))
    for label in ("base", "checker"):
        for name in ("lean", "lake"):
            require(Path(result[label][name]["path"]) == PROFILE / "bin" / name,
                    f"Unexpected {label} {name} selection")
    require(Path(result["checker"]["elan"]["path"]) == ELAN_DIRECTORY / "elan",
            "Checker PATH does not select the genuine current Elan")
    return result


def elan_identity():
    require(digest(ELAN_RECEIPT) == ELAN_RECEIPT_SHA256, "Current Elan setup receipt changed")
    receipt = json.loads(ELAN_RECEIPT.read_bytes())
    require(receipt["binary_sha256"] == ELAN_BINARY_SHA256
            and receipt["selection"] == ELAN_SELECTION
            and Path(receipt["elan_home"]) == ELAN_HOME
            and Path(receipt["profile"]) == PROFILE,
            "Elan receipt does not describe this exact current selection")
    entry = ELAN_DIRECTORY / "elan"
    binary = ELAN_DIRECTORY / "elan-init"
    require(entry.is_symlink() and entry.resolve(strict=True) == binary.resolve(strict=True),
            "Elan entrypoint must select the genuine supplied binary")
    binary_input = file_identity(binary)
    require(binary_input["sha256"] == ELAN_BINARY_SHA256, "Genuine Elan binary identity differs")
    for name in ("lean", "lake"):
        path = ELAN_DIRECTORY / name
        require(not path.exists() and not path.is_symlink(), "Elan directory shadows a kit executable")
    require(ELAN_LINK.is_symlink() and ELAN_LINK.resolve(strict=True) == PROFILE.resolve(strict=True),
            "Elan custom toolchain no longer selects the current kit profile")
    return {"receipt": file_identity(ELAN_RECEIPT), "binary": binary_input,
            "entry_link": os.readlink(entry), "toolchain_link": os.readlink(ELAN_LINK),
            "toolchain_resolved": str(ELAN_LINK.resolve(strict=True)),
            "selected_lean": file_identity(ELAN_LINK / "bin/lean")}


def probe_elan(evidence, when):
    version = evidence.run_command(f"elan-{when}-version").decode("utf-8").strip()
    require(version == ELAN_VERSION, "Real Elan --version output differs from the setup receipt")
    selected = evidence.run_command(f"elan-{when}-which-lean").decode("utf-8").strip()
    require(selected == str(ELAN_LINK / "bin/lean"), "Real Elan selected an unexpected Lean path")
    require(Path(selected).resolve(strict=True) == (PROFILE / "bin/lean").resolve(strict=True),
            "Real Elan selected Lean outside the current profile")
    return {"version": version, "which_lean": selected,
            "selected_lean": file_identity(Path(selected))}


def proof_audit_artifacts():
    # Read the unchanged trace adapter. Do not call its compiler-backed guard or
    # manufacture Lake identities. SHA-256 retention here is not a substitute
    # for the stock guard's native artifact hashes or a new full candidate gate.
    integrity = import_file("pfds_regression_lake_integrity", CHECKOUT / "scripts/lake_integrity.py")
    integrity.validate_layout(CHECKOUT)
    trace = integrity.artifact_path(CHECKOUT, "ProofAudit", "trace")
    described = integrity.expected_artifacts(CHECKOUT, "ProofAudit")
    require(any(path.name == "ProofAudit.olean" for path, _ in described),
            "ProofAudit trace lacks its normal import artifact")
    files = [(trace, "Lake trace", None)]
    files.extend((path, "trace-described artifact", descriptor) for path, descriptor in described)
    files.extend((path.with_name(path.name + ".hash"), "present Lake hash sidecar", None)
                 for path, _, _ in list(files)
                 if path.with_name(path.name + ".hash").exists()
                 or path.with_name(path.name + ".hash").is_symlink())
    result = {}
    for path, kind, descriptor in files:
        require(path.resolve(strict=True) == path and path.is_relative_to(CHECKOUT / ".lake/build"),
                "ProofAudit output is not a real private ordinary-build file")
        result[str(path.relative_to(CHECKOUT))] = {
            **file_identity(path), "kind": kind, "trace_native_hash": descriptor,
        }
    return result


def summarize_stage(name, raw):
    text = raw.decode("utf-8", errors="replace")
    if name == "checker":
        match = re.search(r"^Ran (\d+) tests? in ([0-9.]+)s$", text, re.MULTILINE)
        require(match is not None and int(match.group(1)) == 19
                and re.search(r"^OK$", text, re.MULTILINE) is not None,
                "Successful checker exit lacks the unchanged 19-test success summary")
        return {"reported_test_count": int(match.group(1)), "reported_result": "OK",
                "reported_seconds": match.group(2)}
    if name == "roots":
        match = re.search(r"^PASS: exact root equality \((\d+) roots; private, generated, and local declarations\)$",
                          text, re.MULTILINE)
        require(match is not None and int(match.group(1)) > 0,
                "Successful roots exit lacks its actual exact-equality summary")
        return {"reported_root_count": int(match.group(1)), "reported_exact_equality": True,
                "count_is_roots_not_tests": True}
    if name == "negative-audit":
        reported = re.findall(r"^PASS: (.+)$", text, re.MULTILINE)
        require(reported == list(AUDIT_CASES), "Successful audit suite lacks its four actual case results")
        return {"reported_pass_cases": reported}
    return {"actual_Lake_exit_required": 0,
            "output_provenance": "normal project build and its actual trace; no fresh-output copying"}


def run_locked(runner, cancellation):
    require(sys.flags.optimize == 0, "Run the driver without Python optimization")
    require(DIRECTORY.is_dir() and DIRECTORY.resolve(strict=True) == DIRECTORY,
            "Evidence directory must be a real directory")
    existing = [path for path in DIRECTORY.glob(RUN_ID + "*") if path != CANCEL_PATH]
    require(not existing, "Fixed one-use evidence namespace already exists")
    evidence = Evidence(runner, cancellation)
    evidence.save(create=True)
    record = evidence.record
    baseline = None
    full = None
    kit = None
    after_build = None
    try:
        cancellation.check()
        record["space_before"] = space_observation()
        require(record["space_before"]["admission_free_bytes"] > 0, "No available space for this run")
        record["layout_before"] = private_layout()
        full = runner.full_evidence(ROOT, ORDINARY_RUN, "integration")
        require(full["record"]["verification_mode"] == "incremental",
                "Prerequisite full run must be the actual ordinary incremental run")
        record["ordinary_binding"] = {
            "record": f"session/validation/{ORDINARY_RUN}.json",
            "record_sha256": full["record_sha256"],
            "log_sha256": full["record"]["log_sha256"],
            "verification_sha256": hashlib.sha256(full["verification"]).hexdigest(),
            "verification_mode": "incremental",
        }
        baseline = runner.snapshot(ROOT, CHECKOUT, False, "integration")
        record["inputs_before"] = baseline
        runner.require_frozen(baseline, CANDIDATE)
        require(baseline == full["record"]["final_inputs"],
                "Current integration inputs differ from the successful ordinary full run")
        require(evidence.retain_live_verification("before") == full["verification"],
                "Live stock verification differs from retained ordinary success")
        kit = runner.unified_kit(ROOT)
        kit.check_project(CHECKOUT)
        base = kit.environment(STATE, 1)
        require(base.get("LEAN") is None and base.get("LEAN_PATH") is None,
                "Kit environment retained an outer compiler or search-path override")
        require(base.get("PYTHONOPTIMIZE") in (None, "", "0"),
                "Python optimization would disable unchanged roots-suite assertions")
        proof = dict(base)
        proof["LAKE_ARTIFACT_CACHE"] = "false"
        checker = dict(base)
        checker.update(ELAN_HOME=str(ELAN_HOME), ELAN_TOOLCHAIN=ELAN_SELECTION,
                       PATH=str(ELAN_DIRECTORY) + os.pathsep + base["PATH"])
        evidence.envs = {"base": base, "proof": proof, "checker": checker}
        evidence.environment_keys = sorted(set(kit.runtime.SELECTORS) | {
            "PATH", "LEAN_NUM_THREADS", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME",
            "XDG_CONFIG_HOME", "XDG_STATE_HOME", "TMPDIR", "ELAN_HOME",
            "LAKE_ARTIFACT_CACHE", "LAKE_RESTORE_ARTIFACTS", "LAKE_CACHE_DIR",
            "PYTHONOPTIMIZE", "PYTHONPATH", "PYTHONHOME", "PYTHONDONTWRITEBYTECODE",
        })
        record["environment_whitelist"] = evidence.environment_keys
        record["environment_provider"] = "approved unified_kit; kit.environment(STATE, 1)"
        record["environment_additions"] = {
            "base": {}, "proof": {"LAKE_ARTIFACT_CACHE": "false"},
            "checker": {key: checker[key] for key in ("ELAN_HOME", "ELAN_TOOLCHAIN", "PATH")},
        }
        record["environments_before"] = {name: evidence.selected_environment(env)
                                         for name, env in evidence.envs.items()}
        record["executables_before"] = executable_selections(evidence.envs)
        record["elan_before"] = elan_identity()
        evidence.save()
        record["elan_probes_before"] = probe_elan(evidence, "before")
        for name, _, _ in STAGES:
            raw = evidence.run_command(name)
            evidence.command(name)["stock_summary"] = summarize_stage(name, raw)
            if name == "proof-audit-build":
                after_build = proof_audit_artifacts()
                record["proof_audit_artifacts_after_build"] = after_build
            evidence.save()
        record["all_stages_passed"] = True
    except (Exception, KeyboardInterrupt) as error:
        evidence.fail(error)

    # Every run_command has synchronously settled its current group before it
    # returns or raises. Final observation therefore runs under the same locks
    # with no earlier command left writing evidence or fixture outputs.
    record["status"] = "final_checks"
    checks = {}

    def final_check(name, operation):
        try:
            operation()
            checks[name] = True
        except (Exception, KeyboardInterrupt) as error:
            checks[name] = False
            evidence.fail(error)

    def check_inputs():
        after = runner.snapshot(ROOT, CHECKOUT, False, "integration")
        record["inputs_after"] = after
        runner.require_frozen(after, CANDIDATE)
        require(after == baseline, "Approved integration inputs changed during the regressions")
        record["layout_after"] = private_layout()
        require(record["layout_after"] == record["layout_before"], "Private layout or package link changed")
        require(file_identity(Path(__file__).resolve()) == record["driver_source"], "Driver source changed")

    def check_full_and_live():
        actual = evidence.retain_live_verification("after")
        final_full = runner.full_evidence(ROOT, ORDINARY_RUN, "integration")
        require(final_full == full and actual == full["verification"],
                "Ordinary full evidence or live stock verification changed")

    def check_elan_and_environment():
        cancellation.check()  # A cancelled run never starts additional probes.
        record["elan_probes_after"] = probe_elan(evidence, "after")
        require(record["elan_probes_after"] == record["elan_probes_before"], "Real Elan selection changed")
        record["elan_after"] = elan_identity()
        require(record["elan_after"] == record["elan_before"], "Genuine Elan inputs changed")
        current_base = kit.environment(STATE, 1)
        require(evidence.selected_environment(current_base) == record["environments_before"]["base"],
                "Selected kit environment changed")
        record["executables_after"] = executable_selections(evidence.envs)
        require(record["executables_after"] == record["executables_before"], "Executable selections changed")

    def check_artifacts():
        record["proof_audit_artifacts_after"] = proof_audit_artifacts()
        require(record["proof_audit_artifacts_after"] == after_build,
                "Normal ProofAudit artifacts or traces changed during the suites")

    def check_logs():
        for command in record["commands"]:
            if "log_identity" in command:
                require(file_identity(evidence.log_path(command["name"])) == command["log_identity"],
                        f"Retained command log changed: {command['name']}")

    if kit is not None and "elan_probes_before" in record:
        final_check("elan_and_environment", check_elan_and_environment)
    if after_build is not None:
        final_check("proof_audit_artifacts", check_artifacts)
    if baseline is not None:
        final_check("frozen_inputs_and_driver", check_inputs)
    if full is not None:
        final_check("ordinary_evidence_and_live_verification", check_full_and_live)
    final_check("retained_command_logs", check_logs)
    record["final_checks"] = checks
    record["space_after"] = space_observation()
    cancellation.poll_file()
    record["cancellation"] = cancellation.description()
    required_checks = {"frozen_inputs_and_driver", "ordinary_evidence_and_live_verification",
                       "elan_and_environment", "proof_audit_artifacts", "retained_command_logs"}
    passed = (record["all_stages_passed"] and not record["failures"]
              and set(checks) == required_checks and all(checks.values())
              and cancellation.requested_at is None
              and all(command["passed"] for command in record["commands"]))
    for command in record["commands"]:
        if command["status"] == "not_run":
            command["not_run_reason"] = "Stopped after an earlier failed precondition, command or cancellation"
    record.update(status="finished", ended_at=now(), result="passed" if passed else "failed",
                  driver_exit_code=0 if passed else 1,
                  all_required_command_terminals_observed=all(
                      command["terminal_result_observed"] for command in record["commands"]))
    evidence.save()
    return record["driver_exit_code"]


def main():
    require(len(sys.argv) == 1, "This fixed one-use driver accepts no arguments")
    cancellation = Cancellation()
    handlers = {}
    try:
        for signum in (signal.SIGINT, signal.SIGTERM):
            handlers[signum] = signal.signal(signum, cancellation.request)
        with ExitStack() as locks:
            for name in ("full-build.lock", "focused-build.lock"):
                path = ROOT / "active-validation" / name
                require(path.is_file() and not path.is_symlink(), f"Missing established scheduler lock: {path}")
                lock = locks.enter_context(path.open("r+b"))
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    raise Refusal("Validation lock is held; no regression command was launched") from None
            require(digest(RUNNER_PATH) == RUNNER_SHA256, "Approved validation controller changed")
            runner = import_file("pfds_regression_approved_runner", RUNNER_PATH)
            return run_locked(runner, cancellation)
    finally:
        for signum, handler in handlers.items():
            signal.signal(signum, handler)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Exception, KeyboardInterrupt) as error:
        print(f"Regression driver refused or could not finalize: {type(error).__name__}: {error}",
              file=sys.stderr, flush=True)
        raise SystemExit(1)

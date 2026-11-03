#!/usr/bin/env python3
"""Record the unchanged session validation gates through the native launcher.

  python3 session/validation/run-native-validation.py full RUN_ID [--fresh]
  python3 session/validation/run-native-validation.py focus RUN_ID [--focus-candidate EXACT_SHA]
  python3 session/validation/run-native-validation.py verify RUN_ID --full-record FULL_RUN_ID

Run IDs are new lowercase/digit/hyphen names. Evidence is written alongside
this script. The workspace comes from the script location, so checkpoint
restoration needs no path edit. This runner never records candidate acceptance.
"""

from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import signal
import subprocess
import sys


FULL_HEAD = "901f734161920a76f3b399a575805b9a1d31e971"
FOCUS_HEAD = "3cf3de4fbc24c1a144353ae64b13b72f5ead54a5"
MANIFEST_SHA256 = "dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b"
TARGETS = [
    "Applications.Resources.Potential",
    "Applications.Resources.SignedPotential",
    "Applications.Resources.BinaryCounter",
    "Applications.Resources.SymmetricCosts",
    "Applications.Resources.RandomAccess.End",
    "Applications.Resources.FIFOContracts",
    "Examples.PotentialAccounting",
    "Examples.FIFOContracts",
    "Examples.RandomAccessEndCosts",
    "Examples.SignedPotential",
    "Examples.PotentialTransport",
]
CONTROL_FILES = ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
                 "flake.nix", "flake.lock"]
IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", re.MULTILINE)


class RunnerError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise RunnerError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    return sha(path.read_bytes())


def git(checkout, *args):
    return subprocess.check_output(["git", *args], cwd=checkout, text=True).strip()


def git_identity(checkout):
    require(Path(git(checkout, "rev-parse", "--show-toplevel")).resolve()
            == checkout.resolve(), f"Expected a Git checkout: {checkout}")
    return {
        "head": git(checkout, "rev-parse", "HEAD"),
        "tree": git(checkout, "rev-parse", "HEAD^{tree}"),
        "porcelain": git(checkout, "status", "--porcelain", "--untracked-files=all"),
    }


def source_inputs(checkout, focused):
    if not focused:
        paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=checkout)
        names = [name for name in paths.decode().split("\0") if name]
    else:
        names = set(CONTROL_FILES)
        pending = list(TARGETS)
        visited = set()
        while pending:
            module = pending.pop()
            if module in visited:
                continue
            visited.add(module)
            name = module.replace(".", "/") + ".lean"
            path = checkout / name
            if not path.is_file():
                require(module not in TARGETS and not module.startswith(
                    ("SquareKit.", "Applications.", "Examples.")),
                    f"Missing focused local source: {module}")
                continue
            names.add(name)
            for match in IMPORT.finditer(path.read_text()):
                pending.extend(match.group(1).split("--", 1)[0].split())
    return {name: file_sha(checkout / name) for name in sorted(names)}


def snapshot(root, checkout, focused):
    project = git_identity(checkout)
    manifest_path = checkout / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    require(file_sha(manifest_path) == MANIFEST_SHA256, "Manifest pin differs from the recorded candidates")
    dependencies = {}
    for package in manifest["packages"]:
        require(package["type"] == "git", "Dependencies must retain their Git pins")
        path = (checkout / manifest["packagesDir"] / package["name"]).resolve()
        require(path.is_relative_to(root), "Dependency checkout is outside this workspace")
        identity = git_identity(path)
        identity.update(expected=package["rev"], checkout=str(path.relative_to(root)))
        dependencies[package["name"]] = identity
    launcher = root / "session/environment/run-native-toolchain.py"
    description = subprocess.check_output(
        [sys.executable, str(launcher), "--workspace", str(root), "--describe"],
        cwd=root, text=True, timeout=60)
    controllers = [Path(__file__).resolve(), launcher,
                   root / "session/environment/native-own-exe.c",
                   root / "session/requirements/REQUEST-direct-toolchain-041.md",
                   root / "session/requirements/REQUEST-native-toolchain-042.md"]
    return {
        "project": project,
        "source_inputs": source_inputs(checkout, focused),
        "manifest_sha256": file_sha(manifest_path),
        "dependencies": dependencies,
        "direct_environment": json.loads(description),
        "controller_inputs": {str(path.relative_to(root)): file_sha(path)
                              for path in controllers},
    }


def require_frozen(inputs, expected):
    require(inputs["project"]["head"] == expected, "Candidate is not the exact expected HEAD")
    require(not inputs["project"]["porcelain"], "Candidate checkout is not clean")
    for name, dependency in inputs["dependencies"].items():
        require(dependency["head"] == dependency["expected"], f"Dependency pin differs: {name}")
        require(not dependency["porcelain"], f"Dependency checkout is not clean: {name}")


def validate_stock_record(raw, inputs, mode):
    record = json.loads(raw)
    require(record.get("format") == 1 and record.get("result") == "passed"
            and record.get("candidate") == FULL_HEAD
            and mode in ("incremental", "fresh") and record.get("mode") == mode,
            "Stock verification record has the wrong result, candidate, or mode")
    expected_dependencies = {name: dependency["head"]
                             for name, dependency in inputs["dependencies"].items()}
    require(record.get("dependencies") == expected_dependencies,
            "Stock verification dependencies differ from the captured inputs")
    compiler = record.get("compiler", "")
    require(isinstance(compiler, str) and re.search(r"\bversion 4\.35\.0(?:,|\s|$)", compiler),
            "Stock verification compiler differs from Lean 4.35.0")
    return record


def full_evidence(root, run_id):
    directory = root / "session/validation"
    path = directory / (run_id + ".json")
    raw = path.read_bytes()
    record = json.loads(raw)
    require(record.get("mode") == "full" and record.get("status") == "finished"
            and record.get("exit_code") == 0,
            "Full evidence is not a successful finished run")
    verification_mode = record.get("verification_mode")
    require(verification_mode in ("incremental", "fresh"),
            "Full evidence has no supported stock verification mode")
    expected_command = ["./check.sh", "--candidate", "HEAD"]
    if verification_mode == "fresh":
        expected_command.extend(["--fresh", "--jobs", "1"])
    require(record.get("schema") == 1 and record.get("runtime") == "native"
            and record.get("run_id") == run_id
            and record.get("candidate") == FULL_HEAD
            and record.get("checkout") == "import-correction-r3"
            and record.get("command") == expected_command
            and record.get("command_exit_code") == 0
            and record.get("terminal_result_observed") is True
            and record.get("inputs_unchanged") is True
            and record.get("head_after") == FULL_HEAD
            and record.get("clean_after") is True
            and record.get("verification_record_exists") is True
            and record.get("acceptance") is False,
            "Full evidence lacks the required successful stock-gate evidence")
    require(record["queued_inputs"] == record["inputs"] == record["final_inputs"],
            "Full evidence contains inconsistent input snapshots")
    require_frozen(record["final_inputs"], FULL_HEAD)
    log = directory / (run_id + ".log")
    saved = directory / (run_id + ".verification.json")
    require(record.get("log") == str(log.relative_to(root))
            and record.get("log_sha256") == file_sha(log), "Full log evidence differs")
    verification = saved.read_bytes()
    require(record.get("verification_evidence") == str(saved.relative_to(root))
            and record.get("verification_sha256") == sha(verification),
            "Saved verification evidence differs")
    validate_stock_record(verification, record["final_inputs"], verification_mode)
    return {"record": record, "record_sha256": sha(raw), "verification": verification}


def save_record(path, record, *, create=False):
    data = json.dumps(record, indent=2, sort_keys=True).encode() + b"\n"
    if create:
        with path.open("xb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    else:
        temporary = path.with_name(path.name + f".tmp-{os.getpid()}")
        try:
            with temporary.open("xb") as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def stop_owned_child(child):
    if child.poll() is None:
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            return child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
    return child.wait(timeout=5)


def run_locked(root, args):
    focused = args.mode == "focus"
    checkout_name = "signed-potential" if focused else "import-correction-r3"
    checkout = root / checkout_name
    expected = (args.focus_candidate or FOCUS_HEAD) if focused else FULL_HEAD
    full = full_evidence(root, args.full_record) if args.mode == "verify" else None
    queued_at = now()
    before = snapshot(root, checkout, focused)
    require_frozen(before, expected)
    live_verification = checkout / ".lake/verification.json"
    if full is not None:
        require(before == full["record"]["final_inputs"],
                "Current inputs differ from the successful full run")
        require(live_verification.read_bytes() == full["verification"],
                "Live verification record differs from retained full evidence")
    command = (["lake", "build", *TARGETS] if focused else
               ["./check.sh", "--verify-candidate" if full else "--candidate", "HEAD"])
    verification_mode = (None if focused else full["record"]["verification_mode"]
                         if full is not None else "fresh" if args.fresh else "incremental")
    if args.mode == "full" and args.fresh:
        command.extend(["--fresh", "--jobs", "1"])
    launcher = root / "session/environment/run-native-toolchain.py"
    argv = [sys.executable, str(launcher), "--workspace", str(root), "--", *command]
    directory = root / "session/validation"
    record_path = directory / (args.run_id + ".json")
    log_path = directory / (args.run_id + ".log")
    record = {
        "schema": 1, "mode": args.mode, "run_id": args.run_id, "runtime": "native",
        "verification_mode": verification_mode,
        "scope": "Focused development only" if focused else "Stock candidate gate evidence only",
        "acceptance": False, "candidate": expected, "checkout": checkout_name,
        "requested_focus_candidate": args.focus_candidate if focused else None,
        "command": command, "argv": argv, "targets": TARGETS if focused else None,
        "queued_at": queued_at, "owner_pid": os.getpid(), "status": "queued",
        "queued_inputs": before, "log": str(log_path.relative_to(root)),
        "terminal_result_observed": False,
    }
    if full is not None:
        record.update(full_check=f"session/validation/{args.full_record}.json",
                      full_check_sha256=full["record_sha256"],
                      verification_sha256=sha(full["verification"]))
    save_record(record_path, record, create=True)
    child = None
    failure = None
    command_result = None
    old_handlers = {}

    def interrupted(signum, _frame):
        raise KeyboardInterrupt(f"Received signal {signum}")

    try:
        with log_path.open("xb") as log:
            inputs = snapshot(root, checkout, focused)
            record["inputs"] = inputs
            require(inputs == before, "Inputs changed before command start")
            record.update(status="running", started_at=now())
            save_record(record_path, record)
            for signum in (signal.SIGINT, signal.SIGTERM):
                old_handlers[signum] = signal.signal(signum, interrupted)
            child = subprocess.Popen(argv, cwd=checkout, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            record["child_pid"] = child.pid
            save_record(record_path, record)
            print(f"Running {args.mode}; log: {log_path}", flush=True)
            command_result = child.wait()
            record["terminal_result_observed"] = True
    except (Exception, KeyboardInterrupt) as error:
        failure = f"{type(error).__name__}: {error}"
        if child is not None:
            try:
                command_result = stop_owned_child(child)
                record["terminal_result_observed"] = True
            except Exception as stop_error:
                record["child_stop_error"] = str(stop_error)
    finally:
        for signum, handler in old_handlers.items():
            signal.signal(signum, handler)

    try:
        after = snapshot(root, checkout, focused)
        record.update(final_inputs=after, inputs_unchanged=(after == before),
                      head_after=after["project"]["head"],
                      clean_after=not after["project"]["porcelain"])
        require_frozen(after, expected)
        require(record["inputs_unchanged"], "Inputs changed during the command")
        if command_result == 0 and failure is None and not focused:
            actual = live_verification.read_bytes()
            validate_stock_record(actual, after, verification_mode)
            if full is not None:
                final_full = full_evidence(root, args.full_record)
                require(final_full == full and actual == full["verification"],
                        "Verification or full-run evidence changed during verification")
                record["verification_and_full_evidence_unchanged"] = True
            else:
                saved = directory / (args.run_id + ".verification.json")
                with saved.open("xb") as stream:
                    stream.write(actual)
                    stream.flush()
                    os.fsync(stream.fileno())
                record.update(verification_evidence=str(saved.relative_to(root)),
                              verification_sha256=sha(actual))
    except Exception as error:
        record.setdefault("inputs_unchanged", False)
        record["postcheck_error"] = f"{type(error).__name__}: {error}"
        failure = failure or record["postcheck_error"]
    if not focused:
        record["verification_record_exists"] = live_verification.is_file()
    if log_path.is_file():
        record["log_sha256"] = file_sha(log_path)
    if command_result is None:
        exit_code = 1
    elif command_result < 0:
        exit_code = 128 - command_result
    else:
        exit_code = command_result
    if failure is not None and exit_code == 0:
        exit_code = 2
    record.update(status="finished", ended_at=now(), command_exit_code=command_result,
                  exit_code=exit_code)
    if failure is not None:
        record["failure"] = failure
    save_record(record_path, record)
    print(f"Recorded {args.mode}: exit {exit_code}; {record_path}", flush=True)
    return exit_code


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("full", "focus", "verify"))
    parser.add_argument("run_id")
    parser.add_argument("--full-record", help="successful full run ID required by verify")
    parser.add_argument("--focus-candidate", help="focus only: exact 40-digit commit for a corrected candidate")
    parser.add_argument("--fresh", action="store_true",
                        help="full only: stock fresh check with --jobs 1; required after tooling changes")
    args = parser.parse_args()
    for name in (args.run_id, args.full_record):
        if name is not None and not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name):
            parser.error("Run IDs must contain lowercase letters, digits, and single hyphens")
    if (args.mode == "verify") != (args.full_record is not None):
        parser.error("Only verify requires --full-record RUN_ID")
    if args.focus_candidate is not None and (args.mode != "focus" or
            not re.fullmatch(r"[0-9a-f]{40}", args.focus_candidate)):
        parser.error("--focus-candidate requires focus and an exact lowercase 40-digit commit")
    if args.fresh and args.mode != "full":
        parser.error("--fresh applies only to full; verify uses its saved record's mode")
    root = Path(__file__).resolve().parents[2]
    directory = root / "session/validation"
    for suffix in (".json", ".log", ".verification.json"):
        path = directory / (args.run_id + suffix)
        if path.exists() or path.is_symlink():
            parser.error(f"Evidence path already exists: {path}")
    lock_dir = root / "active-validation"
    lock_dir.mkdir(exist_ok=True)
    lock_name = "focused-build.lock" if args.mode == "focus" else "full-build.lock"
    try:
        with (lock_dir / lock_name).open("a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise RunnerError("Validation lock is already held") from None
            return run_locked(root, args)
    except (RunnerError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"Validation refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())


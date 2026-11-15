#!/usr/bin/env python3
"""Check a committed candidate in a persistent, exclusively owned worktree."""

import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

from verification_status import observe, publish, read


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def common_dir(root):
    return Path(git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()


def require_clean(workspace):
    if git(workspace, "status", "--porcelain", "--untracked-files=all"):
        raise RuntimeError(f"Managed worktree has edits; preserve and resolve them first: {workspace}")


def stop_group(child):
    """Bound cleanup even when a verifier or its descendants ignore SIGTERM."""
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 2
    while time.monotonic() < deadline:
        child.poll()
        try:
            os.killpg(child.pid, 0)
        except ProcessLookupError:
            break
        time.sleep(.02)
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.wait(timeout=2)


def run(command, workspace, lock_fd, env=None):
    signals = (signal.SIGTERM, signal.SIGINT)
    previous = {sig: signal.getsignal(sig) for sig in signals}
    # Deliver pending interruption only after we own the spawned process group.
    mask = signal.pthread_sigmask(signal.SIG_BLOCK, signals)
    child = None

    def interrupted(signum, _frame):
        raise InterruptedError(f"Interrupted by signal {signum}; inspect the managed run before recovery")

    try:
        for signum in signals:
            signal.signal(signum, interrupted)
        child = subprocess.Popen(command, cwd=workspace, env=env, pass_fds=(lock_fd,), start_new_session=True,
                                 preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, mask))
        signal.pthread_sigmask(signal.SIG_SETMASK, mask)
        code = child.wait()
        if code < 0:
            stop_group(child)
        return code
    except BaseException:
        signal.pthread_sigmask(signal.SIG_BLOCK, signals)
        if child is not None:
            stop_group(child)
        raise
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, mask)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("revision", nargs="?", help="commit to check; resolved once before acquiring the workspace")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--verify", action="store_true", help="verify the current receipt without checkout/build")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--clean", action="store_true", help="rebuild project with Lake and retain outputs")
    modes.add_argument("--fresh", action="store_true", help="independent direct-Lean reference check")
    parser.add_argument("--jobs", type=int, help="fresh-mode compiler concurrency")
    parser.add_argument("--status", action="store_true", help="read current operational status as JSON without mutation")
    args = parser.parse_args()
    if args.status and (args.revision is not None or args.verify or args.clean or args.fresh or args.jobs is not None):
        parser.error("--status accepts only --repo")
    if not args.status and args.revision is None:
        parser.error("a candidate revision is required")
    if args.verify and (args.clean or args.fresh or args.jobs is not None):
        parser.error("--verify does not accept --clean, --fresh or --jobs")
    if args.jobs is not None and (not args.fresh or args.jobs < 1):
        parser.error("--jobs requires --fresh and a positive count")
    if any(key.startswith("GIT_") and key != "GIT_PAGER" for key in os.environ):
        raise RuntimeError("Unset inherited GIT_* overrides before candidate validation")
    repo = args.repo.resolve()
    common = common_dir(repo)
    if args.status:
        print(json.dumps(observe(common / "conaled"), sort_keys=True))
        return 0
    revision = git(repo, "rev-parse", "--verify", "--end-of-options", args.revision + "^{commit}")
    state = common / "conaled"
    state.mkdir(exist_ok=True)
    workspace = state / "acceptance"
    owner_path = state / "acceptance-owner.json"
    running = state / "acceptance-running.json"
    owner = {"format": 1, "repository": str(common), "workspace": str(workspace)}
    with (state / "acceptance.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("The persistent acceptance workspace is busy; retry after its current run") from None
        if running.exists():
            raise RuntimeError(f"An interrupted run needs inspection before reuse: {running}")
        if workspace.exists() or owner_path.exists():
            if not owner_path.is_file() or json.loads(owner_path.read_text()) != owner:
                raise RuntimeError(f"Refusing an unowned workspace: {workspace}")
            if workspace.is_symlink() or common_dir(workspace) != common:
                raise RuntimeError("Managed worktree repository differs from its owner record")
            require_clean(workspace)
        elif args.verify:
            raise RuntimeError("No managed candidate exists to verify")
        if args.clean and ((workspace / ".lake").is_symlink()
                           or (workspace / ".lake/build").is_symlink()):
            raise RuntimeError("Clean build requires real .lake and .lake/build directories")
        if args.verify:
            if git(workspace, "rev-parse", "HEAD") != revision:
                raise RuntimeError("Requested candidate is not the managed worktree's HEAD")
        # A crash leaves a marker; later invocations never silently advance a
        # checkout whose previous process or artifact publication is uncertain.
        run_id = uuid.uuid4().hex
        status_path = state / "acceptance-status.json"
        observation = {"format": 1, "run_id": run_id, "candidate": revision,
                       "operation": "verify" if args.verify else "check",
                       "phase": "preparing", "outcome": "running",
                       "started_at": time.time(), "started_monotonic": time.monotonic()}
        running.write_text(json.dumps({**owner, "candidate": revision, "pid": os.getpid(),
                                       "run_id": run_id}) + "\n")
        publish(status_path, observation)
        try:
            if not workspace.exists():
                subprocess.run(["git", "-C", str(repo), "worktree", "add", "--detach", str(workspace), revision], check=True)
                owner_path.write_text(json.dumps(owner) + "\n")
            elif not args.verify:
                (workspace / ".lake/verification.json").unlink(missing_ok=True)
                subprocess.run(["git", "-C", str(workspace), "checkout", "--detach", revision], check=True)
            if not (workspace / ".envrc").is_file():
                raise RuntimeError("Candidate must supply its tracked .envrc development environment")
            if ".envrc" not in git(workspace, "ls-files", ".envrc").splitlines():
                raise RuntimeError("Candidate .envrc is not tracked")
            packages = workspace / ".lake/packages"
            if not packages.exists() and not packages.is_symlink():
                donor = (repo / ".lake/packages").resolve()
                if not donor.is_dir():
                    raise RuntimeError("Prepare the pinned dependency cache in the caller checkout first")
                packages.parent.mkdir(exist_ok=True)
                packages.symlink_to(donor, target_is_directory=True)
            print(f"Acceptance workspace: {workspace}\nCandidate: {revision}", flush=True)
            # The candidate's environment, not the calling branch's flake, selects
            # supporting executables. check.sh still verifies Lean/dependency pins.
            subprocess.run(["direnv", "allow", str(workspace)], check=True)
            command = ["direnv", "exec", str(workspace), "./check.sh",
                       "--verify-candidate" if args.verify else "--candidate", revision]
            if args.fresh:
                command.append("--fresh")
            if args.clean:
                command.append("--clean")
            if args.jobs is not None:
                command += ["--jobs", str(args.jobs)]
            env = {**os.environ, "CONALED_STATUS_FILE": str(status_path), "CONALED_RUN_ID": run_id}
            code = run(command, workspace, lock.fileno(), env)
            if code < 0:
                raise RuntimeError("Verifier terminated by signal; inspect the interrupted run marker")
            latest = read(status_path) or observation
            publish(status_path, dict(latest, outcome="passed" if code == 0 else "failed",
                                      phase="complete" if code == 0 else latest["phase"]))
            running.unlink()
            return code
        except BaseException as error:
            if not args.verify:
                (workspace / ".lake/verification.json").unlink(missing_ok=True)
            latest = read(status_path) or observation
            outcome = "interrupted" if isinstance(error, (InterruptedError, KeyboardInterrupt)) else "unknown"
            publish(status_path, dict(latest, outcome=outcome))
            raise



if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Candidate validation failed: {error}", file=sys.stderr)
        sys.exit(1)

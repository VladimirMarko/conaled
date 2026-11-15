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


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def common_dir(root):
    return Path(git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()


def require_clean(workspace):
    if git(workspace, "status", "--porcelain", "--untracked-files=all"):
        raise RuntimeError(f"Managed worktree has edits; preserve and resolve them first: {workspace}")


def run(command, workspace, lock_fd):
    child = subprocess.Popen(command, cwd=workspace, pass_fds=(lock_fd,), start_new_session=True)
    previous = {}

    def interrupted(signum, _frame):
        os.killpg(child.pid, signal.SIGTERM)
        raise InterruptedError(f"Interrupted by signal {signum}; inspect the managed run before recovery")

    for signum in (signal.SIGTERM, signal.SIGINT):
        previous[signum] = signal.signal(signum, interrupted)
    try:
        return child.wait()
    except BaseException:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
        child.wait()
        raise
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("revision", help="commit to check; resolved once before acquiring the workspace")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--verify", action="store_true", help="verify the current receipt without checkout/build")
    parser.add_argument("--fresh", action="store_true", help="explicit cache-independent project check")
    parser.add_argument("--jobs", type=int, help="fresh-mode compiler concurrency")
    args = parser.parse_args()
    if args.verify and (args.fresh or args.jobs is not None):
        parser.error("--verify does not accept --fresh or --jobs")
    if args.jobs is not None and (not args.fresh or args.jobs < 1):
        parser.error("--jobs requires --fresh and a positive count")
    if any(key.startswith("GIT_") and key != "GIT_PAGER" for key in os.environ):
        raise RuntimeError("Unset inherited GIT_* overrides before candidate validation")
    repo = args.repo.resolve()
    revision = git(repo, "rev-parse", "--verify", "--end-of-options", args.revision + "^{commit}")
    common = common_dir(repo)
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
        if args.verify:
            if git(workspace, "rev-parse", "HEAD") != revision:
                raise RuntimeError("Requested candidate is not the managed worktree's HEAD")
        # A crash leaves a marker; later invocations never silently advance a
        # checkout whose previous process or artifact publication is uncertain.
        running.write_text(json.dumps({**owner, "candidate": revision, "pid": os.getpid()}) + "\n")
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
        if args.jobs is not None:
            command += ["--jobs", str(args.jobs)]
        code = run(command, workspace, lock.fileno())
        if code < 0:
            raise RuntimeError("Verifier terminated by signal; inspect the interrupted run marker")
        running.unlink()
        return code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Candidate validation failed: {error}", file=sys.stderr)
        sys.exit(1)

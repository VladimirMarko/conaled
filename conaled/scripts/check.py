#!/usr/bin/env python3
"""Verify project coverage and sources, build with Lake, and run the axiom audit."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

from lake_integrity import guard_outputs


ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^import\s+([^\n]+)", re.MULTILINE)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|partial|native_decide)\b|debug\s*\.\s*skipKernelTC")


def executable_source(text: str) -> str:
    """Remove Lean strings and nested comments before the source-level guard."""
    output: list[str] = []
    index = 0
    depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif string:
            if text[index] == "\\":
                index += 2
            elif text[index] == '"':
                string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text.startswith("/-", index):
            depth = 1
            output.append(" ")
            index += 2
        elif text[index] == '"':
            string = True
            output.append(" ")
            index += 1
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def compile_modules(modules, dependencies, order, lean, env, output, jobs):
    """Build ready modules with bounded concurrency; never release failed imports."""
    def compile_one(name):
        source = modules[name].relative_to(ROOT)
        target = output / source.with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        result = subprocess.run([lean, "-o", str(target), str(source)],
                                cwd=ROOT, env=env, capture_output=True, text=True)
        return result, time.monotonic() - started

    pending = set(order)
    completed = set()
    active = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or active:
            for name in order:
                if len(active) >= jobs:
                    break
                if name in pending and set(dependencies[name]) <= completed:
                    pending.remove(name)
                    active[pool.submit(compile_one, name)] = name
            if not active:
                raise RuntimeError("No buildable modules remain: " + ", ".join(sorted(pending)))
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            failed = []
            for future in finished:
                name = active.pop(future)
                result, elapsed = future.result()
                print(f"[{len(completed) + 1}/{len(order)}] {name} ({elapsed:.2f}s)", flush=True)
                print(result.stdout, end="", flush=True)
                print(result.stderr, end="", file=sys.stderr, flush=True)
                if result.returncode:
                    failed.append(f"{name} (exit {result.returncode})")
                else:
                    completed.add(name)
            if failed:
                # Already-running independent jobs finish before the temporary
                # output directory is removed. Dependents and audit never start.
                raise RuntimeError("Compilation failed: " + ", ".join(failed))


def positive_jobs(value):
    try:
        jobs = int(value)
    except ValueError:
        raise argparse.ArgumentTypeError("jobs must be a positive integer") from None
    if jobs < 1:
        raise argparse.ArgumentTypeError("jobs must be a positive integer")
    return jobs


def git_output(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def clean_commit(root):
    if Path(git_output(root, "rev-parse", "--show-toplevel")).resolve() != root.resolve():
        raise RuntimeError(f"Expected a Git checkout at {root}")
    commit = git_output(root, "rev-parse", "HEAD")
    if git_output(root, "status", "--porcelain", "--untracked-files=all"):
        raise RuntimeError(f"Candidate validation requires a clean checkout: {root}")
    return commit


def candidate_identity(revision):
    candidate = git_output(ROOT, "rev-parse", "--verify", "--end-of-options", revision + "^{commit}")
    if clean_commit(ROOT) != candidate:
        raise RuntimeError("Candidate must be the checked-out HEAD commit")
    # An ignored Lean file could otherwise enter the public inventory while
    # remaining absent from the commit named by the record.
    sources = list(ROOT.glob("*.lean"))
    for directory in ("SquareKit", "Applications", "Examples"):
        sources.extend((ROOT / directory).rglob("*.lean"))
    tracked = set(subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT).decode().rstrip("\0").split("\0"))
    if any(str(p.relative_to(ROOT)) not in tracked for p in sources):
        raise RuntimeError("Candidate validation requires every integrated Lean source to be tracked")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise RuntimeError("Candidate records currently require Git-pinned dependencies")
        checkout = ROOT / manifest["packagesDir"] / package["name"]
        revision = clean_commit(checkout)
        if revision != package["rev"]:
            raise RuntimeError(f"Dependency revision differs from manifest: {package['name']}")
        dependencies[package["name"]] = revision
    return {"candidate": candidate, "dependencies": dependencies}


def compiler_version(fresh, env):
    command = [env.get("LEAN", "lean"), "--version"] if fresh else ["lake", "env", "lean", "--version"]
    version = subprocess.check_output(command, cwd=ROOT, env=env, text=True).strip()
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    actual = re.search(r"\bversion ([^,\s]+)", version)
    if actual is None or actual.group(1) != toolchain.rsplit(":v", 1)[-1]:
        raise RuntimeError(f"Expected {toolchain}, got {version}.")
    return version


def read_record(path):
    try:
        record = json.loads(path.read_text())
        if (record["format"] != 1 or record["result"] != "passed"
                or record["mode"] not in ("fresh", "incremental")
                or not isinstance(record["candidate"], str)
                or not isinstance(record["dependencies"], dict)
                or not isinstance(record["compiler"], str)
                or not isinstance(record["completed_at"], str)):
            raise ValueError("invalid fields")
        return record
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise RuntimeError(f"No usable verification record at {path}: {error}") from error


def save_record(path, record):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as output:
        temporary = Path(output.name)
        try:
            json.dump(record, output, indent=2)
            output.write("\n")
            output.close()
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    candidates = parser.add_mutually_exclusive_group()
    candidates.add_argument("--candidate", metavar="REV",
                            help="validate a clean HEAD candidate and save its success record")
    candidates.add_argument("--verify-candidate", metavar="REV",
                            help="check an existing candidate record without compiling")
    parser.add_argument("--fresh", action="store_true",
                        help="recompile every project module in private temporary outputs")
    parser.add_argument("--jobs", "-j", type=positive_jobs,
                        default=None,
                        help="fresh mode only: maximum concurrent compilers (default: up to 4)")
    args = parser.parse_args()
    if args.verify_candidate and (args.fresh or args.jobs is not None):
        parser.error("--verify-candidate uses the recorded mode; omit --fresh and --jobs")
    if not args.fresh and args.jobs is not None:
        parser.error("--jobs requires --fresh; incremental compilation uses Lake's scheduler")
    if not args.fresh and not args.verify_candidate and "LEAN" in os.environ:
        parser.error("LEAN override requires --fresh; incremental compilation uses Lake's pinned compiler")
    args.jobs = args.jobs or min(4, os.cpu_count() or 1)
    started = time.monotonic()
    record_path = ROOT / ".lake/verification.json"
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    if args.verify_candidate:
        record = read_record(record_path)
        if record["mode"] == "incremental" and "LEAN" in env:
            raise RuntimeError("LEAN override is incompatible with an incremental record")
        identity = candidate_identity(args.verify_candidate)
        identity["compiler"] = compiler_version(record["mode"] == "fresh", env)
        if any(record[key] != value for key, value in identity.items()):
            raise RuntimeError("Verification record does not match current candidate inputs")
        print(f"Verification record matches {identity['candidate']} ({record['mode']}).")
        return 0
    # A failed new attempt must not leave an older success looking current.
    record_path.unlink(missing_ok=True)
    identity = candidate_identity(args.candidate) if args.candidate else None
    sources = list(ROOT.glob("*.lean"))
    for directory in ("SquareKit", "Applications", "Examples"):
        sources.extend((ROOT / directory).rglob("*.lean"))
    modules = {
        ".".join(path.relative_to(ROOT).with_suffix("").parts): path
        for path in sources
    }
    dependencies: dict[str, list[str]] = {}
    for name, path in modules.items():
        source_text = path.read_text(encoding="utf-8")
        forbidden = FORBIDDEN.search(executable_source(source_text))
        if forbidden:
            raise RuntimeError(f"Forbidden source construct in {name}: {forbidden.group(0)}")
        imports = [
            item
            for match in IMPORT.finditer(source_text)
            for item in match.group(1).split("--", 1)[0].split()
        ]
        dependencies[name] = [item for item in imports if item in modules]
        for item in imports:
            if item.startswith(("SquareKit.", "Applications.", "Examples.")) and item not in modules:
                raise RuntimeError(f"Missing local source imported by {name}: {item}")

    order: list[str] = []
    visiting: set[str] = set()
    finished: set[str] = set()

    def visit(name: str) -> None:
        if name in finished:
            return
        if name in visiting:
            raise RuntimeError(f"Local import cycle at {name}")
        visiting.add(name)
        for dependency in sorted(dependencies[name]):
            visit(dependency)
        visiting.remove(name)
        finished.add(name)
        order.append(name)

    visit("SquareApplications")
    omitted = set(modules) - finished - {"ProofAudit"}
    if omitted:
        raise RuntimeError("Public entrypoint omits source modules: " + ", ".join(sorted(omitted)))
    visit("ProofAudit")

    dependency_paths = sorted((ROOT / ".lake" / "packages").glob("*/.lake/build/lib/lean"))
    mathlib = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib"
    if not mathlib.is_dir():
        raise RuntimeError("Mathlib build cache is missing. Run `lake exe cache get` first.")
    lean = env.get("LEAN", "lean")
    version = compiler_version(args.fresh, env)
    print(version, flush=True)
    if identity is not None:
        identity["compiler"] = version
    print("Source guard passed: no admissions, source axioms, unsafe/partial definitions, native_decide, or skipped kernel checking.", flush=True)
    print(f"Source/coverage/version checks: {time.monotonic() - started:.2f}s", flush=True)
    if not args.fresh:
        # Disable artifact-cache restore/write even if inherited from the caller.
        # Existing dependency build outputs remain trusted and reusable.
        env["LAKE_ARTIFACT_CACHE"] = "false"
        targets = [n for n in order if n != "ProofAudit"]
        guard_outputs(ROOT, targets, env, repair=True)
        print(f"Building {len(order) - 1} project modules with Lake (incremental).", flush=True)
        build_started = time.monotonic()
        # Explicit module targets avoid library/default-target ambiguity and build
        # every inventoried module, including imports used only by the audit.
        subprocess.run(["lake", "--no-cache", "--rehash", "build", *["+" + n for n in targets]],
                       cwd=ROOT, env=env, check=True)
        print(f"Incremental compilation: {time.monotonic() - build_started:.2f}s", flush=True)
        guard_outputs(ROOT, targets, env, repair=False)
        audit_started = time.monotonic()
        # Run the audit even when Lake reuses all project artifacts. Do not write
        # an olean behind Lake's back or use a cached audit's old success message.
        subprocess.run(["lake", "env", "lean", str(modules["ProofAudit"].relative_to(ROOT))],
                       cwd=ROOT, env=env, check=True)
        print(f"Proof audit: {time.monotonic() - audit_started:.2f}s", flush=True)
    else:
        print(f"Rechecking {len(order)} local modules from source with {args.jobs} workers.", flush=True)
        (ROOT / ".lake").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="fresh-check-", dir=ROOT / ".lake") as directory:
            output = Path(directory)
            env["LEAN_PATH"] = os.pathsep.join([str(output), *(str(p) for p in dependency_paths)])
            build_started = time.monotonic()
            compile_modules(modules, dependencies, [n for n in order if n != "ProofAudit"],
                            lean, env, output, args.jobs)
            print(f"Fresh compilation: {time.monotonic() - build_started:.2f}s", flush=True)
            audit_started = time.monotonic()
            source = modules["ProofAudit"].relative_to(ROOT)
            subprocess.run([lean, "-o", str(output / "ProofAudit.olean"), str(source)],
                           cwd=ROOT, env=env, check=True)
            print(f"Proof audit: {time.monotonic() - audit_started:.2f}s", flush=True)
    if identity is not None:
        after = candidate_identity(identity["candidate"])
        after["compiler"] = compiler_version(args.fresh, env)
        if after != identity:
            raise RuntimeError("Candidate inputs changed during verification")
        save_record(record_path, {
            "format": 1, "result": "passed", **identity,
            "mode": "fresh" if args.fresh else "incremental",
            "completed_at": datetime.now(timezone.utc).isoformat(),
        })
        print(f"Candidate {identity['candidate']} recorded in {record_path.relative_to(ROOT)}.")
    print(f"PASS: all {len(order)} modules checked; exhaustive axiom audit passed. "
          f"Total: {time.monotonic() - started:.2f}s", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError, OSError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)

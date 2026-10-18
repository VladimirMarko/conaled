#!/usr/bin/env python3
"""Recheck every project Lean module, then its exhaustive transitive axiom audit."""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", "-j", type=positive_jobs,
                        default=min(4, os.cpu_count() or 1),
                        help="maximum concurrent project compilers (default: up to 4); use 1 for serial")
    args = parser.parse_args()
    started = time.monotonic()
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
    env = os.environ.copy()
    # Fresh checks use only this run's project outputs and dependency caches.
    # Neither source-adjacent oleans nor Lake's incremental project outputs may
    # shadow a freshly compiled module. Caller LEAN_PATH is intentionally replaced.
    lean = env.get("LEAN", "lean")
    version = subprocess.check_output([lean, "--version"], cwd=ROOT, env=env, text=True).strip()
    print(version, flush=True)
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected = toolchain.rsplit(":v", 1)[-1]
    actual = re.search(r"\bversion ([^,\s]+)", version)
    if actual is None or actual.group(1) != expected:
        raise RuntimeError(f"Expected {toolchain}, got {version}.")
    print("Source guard passed: no admissions, source axioms, unsafe/partial definitions, native_decide, or skipped kernel checking.", flush=True)
    print(f"Source/coverage/version checks: {time.monotonic() - started:.2f}s", flush=True)
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
    print(f"PASS: all {len(order)} modules checked; exhaustive axiom audit passed. "
          f"Total: {time.monotonic() - started:.2f}s", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError, OSError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)

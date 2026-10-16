#!/usr/bin/env python3
"""Recheck every project Lean module, then its exhaustive transitive axiom audit."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys


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


def main() -> int:
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
    paths = [str(ROOT), str(ROOT / ".lake/build/lib/lean")]
    paths.extend(str(path) for path in dependency_paths)
    if env.get("LEAN_PATH"):
        paths.append(env["LEAN_PATH"])
    env["LEAN_PATH"] = os.pathsep.join(paths)
    lean = env.get("LEAN", "lean")
    version = subprocess.check_output([lean, "--version"], cwd=ROOT, env=env, text=True).strip()
    print(version, flush=True)
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected = toolchain.rsplit(":v", 1)[-1]
    actual = re.search(r"\bversion ([^,\s]+)", version)
    if actual is None or actual.group(1) != expected:
        raise RuntimeError(f"Expected {toolchain}, got {version}.")
    print("Source guard passed: no admissions, source axioms, unsafe/partial definitions, native_decide, or skipped kernel checking.", flush=True)
    print(f"Rechecking {len(order)} local modules from source, in dependency order.", flush=True)
    for index, name in enumerate(order, 1):
        source = modules[name].relative_to(ROOT)
        print(f"[{index}/{len(order)}] {source}", flush=True)
        subprocess.run(
            [lean, "-o", str(source.with_suffix(".olean")), str(source)],
            cwd=ROOT, env=env, check=True,
        )
    print(f"PASS: all {len(order)} modules checked; exhaustive axiom audit passed.", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)

#!/usr/bin/env python3
"""Fresh isolated source-closure check using the repository compiler and audit."""
import argparse
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("project_check", ROOT / "scripts/check.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)
parser = argparse.ArgumentParser()
parser.add_argument("--jobs", type=int, default=2)
args = parser.parse_args()
if args.jobs < 1:
    parser.error("--jobs must be positive")
version = subprocess.check_output(["lean", "--version"], text=True).strip()
expected = (ROOT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
if f"version {expected}," not in version:
    raise RuntimeError(f"Expected {expected}, got {version}")
print(version, flush=True)
lean = subprocess.check_output(["elan", "which", "lean"], cwd=ROOT, text=True).strip()
sources = {"Contracts": ROOT / "experiments/host-target/Contracts.lean"}
dependencies = {}
order = []

def visit(name):
    if name in dependencies:
        return
    source = sources[name].read_text()
    forbidden = check.FORBIDDEN.search(check.executable_source(source))
    if forbidden:
        raise RuntimeError(f"Forbidden construct in {name}: {forbidden.group(0)}")
    local = []
    for match in check.IMPORT.finditer(source):
        for imported in match.group(1).split("--", 1)[0].split():
            path = ROOT / (imported.replace(".", "/") + ".lean")
            if path.is_file():
                sources[imported] = path
                local.append(imported)
            elif not (imported == "Lean" or imported.startswith("Lean.")):
                raise RuntimeError(f"Unexpected external dependency: {imported}")
    dependencies[name] = local
    for imported in local:
        visit(imported)
    order.append(name)

visit("Contracts")
with tempfile.TemporaryDirectory(prefix="conaled-host-target-") as directory:
    root = Path(directory)
    # The existing isolated audit checks every current-module safe declaration,
    # including generated/private roots, and traverses their axiom dependencies.
    audit = ROOT / "experiments/relative-graph/ArtifactAudit.lean"
    (root / "ArtifactAudit.lean").write_text(audit.read_text())
    modules = {"ArtifactAudit": root / "ArtifactAudit.lean"}
    for name, source in sources.items():
        target = root / (name.replace(".", "/") + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("import ArtifactAudit\n" + source.read_text() + "\n#audit_graph_module\n")
        modules[name] = target
        dependencies[name].append("ArtifactAudit")
    dependencies["ArtifactAudit"] = []
    output = root / "build"
    output.mkdir()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(output)
    check.ROOT = root
    check.compile_modules(modules, dependencies, ["ArtifactAudit", *order],
                          lean, env, output, args.jobs)
print(f"PASS: {len(modules)} freshly compiled modules; exhaustive per-module audits; {args.jobs} workers.")

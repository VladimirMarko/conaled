#!/usr/bin/env python3
"""Reproduce #593's isolated Lean module-system adoption assessment.

Run through direnv. Only the requested new output directory is written; no Lake
build or project artifacts are used. Failed expectations raise an error.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
FOUNDATION = ("Squares", "Compiler", "SquareCompiler", "FirstOrder", "Dependent", "Verification")
INPUTS = tuple(f"{m}.lean" for m in FOUNDATION) + (
    "check-foundation.sh", "ProofAudit.lean", "scripts/project_sources.py",
    "scripts/lean-source-info.lean", "lean-toolchain")

CLIENT = '''#check Squares.compose_assoc
#check CategoricalCompiler.compile_sound
#check SquareCompiler.compile_commutes
#check FirstOrderCompiler.no_exponential
#check DependentSquares.RelTerm.apply
example : CategoricalCompiler.run CategoricalCompiler.arithmeticMeaning
  (CategoricalCompiler.compile (CategoricalCompiler.rawTarget CategoricalCompiler.Arithmetic)
    CategoricalCompiler.square) ((), 7) = 49 := rfl
example : (DependentSquares.Example.appliedCert.code 8).1.val = 8 := rfl
example : DecidableEq CategoricalCompiler.Ty := inferInstance
example : Repr FirstOrderCompiler.Ty := inferInstance
example : List CategoricalCompiler.Ty := [.base, .prod .unit .base]
#eval CategoricalCompiler.run CategoricalCompiler.arithmeticMeaning
  (CategoricalCompiler.compile (CategoricalCompiler.rawTarget CategoricalCompiler.Arithmetic)
    CategoricalCompiler.square) ((), 7)
#eval (DependentSquares.Example.appliedCert.code 8).1.val
'''
BOUNDARY = '''namespace ModuleTrial
private theorem hiddenBoundary : True := True.intro
scoped notation "trialSquare" => CategoricalCompiler.square
end ModuleTrial
'''
SCAN = '''open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    let origin := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if origin == `Squares || origin == `Compiler || origin == `SquareCompiler ||
       origin == `FirstOrder || origin == `Dependent || origin == `Verification ||
       origin == `Applications.Boundary || origin == `Applications.AuditSlice then
      IO.println s!"COUNTER {origin} {info.isTheorem} {info.isUnsafe}"
      if !info.isUnsafe then IO.println s!"REFERENCE {name}"
      if !name.isInternal && !isPrivateName name then
        IO.println s!"PUBLIC {origin} {name}"
'''


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class Trial:
    def __init__(self, output):
        self.output = output
        self.results = []

    def run(self, label, command, cwd, *, expected=0, diagnostic=None):
        env = dict(os.environ, LEAN_PATH=str(cwd))
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                capture_output=True, timeout=180)
        text = result.stdout + result.stderr
        (self.output / f"{label}.log").write_text(text)
        self.results.append({"label": label, "command": command,
                             "exit": result.returncode, "expected": expected})
        (self.output / "commands.json").write_text(json.dumps(self.results, indent=2) + "\n")
        if expected == 0:
            require(result.returncode == 0, f"{label} failed: {text}")
        else:
            require(result.returncode != 0, f"{label} unexpectedly succeeded")
            require(diagnostic and diagnostic in text, f"{label}: missing {diagnostic!r}: {text}")
        return text

    def compile(self, root, name, *, expected=0, diagnostic=None):
        return self.run(root.name + "-" + name.replace("/", "-") + ("-rejected" if expected else ""),
                        ["lean", "-EhasSorry", "-R", str(root), "-o",
                         str(root / (name + ".olean")), str(root / (name + ".lean"))],
                        root, expected=expected, diagnostic=diagnostic)

    def preflight(self, root, sources):
        manifest = root / "manifest.json"
        manifest.write_text(json.dumps(sources))
        return json.loads(self.run(root.name + "-preflight", ["lean", "--run",
            "scripts/lean-source-info.lean", str(manifest)], root))


def convert(source, *, public=True, exposed=True, meta=False):
    # These selected production sources have plain one-line imports at the top.
    # Verify this shape rather than pretending to implement Lean's parser.
    lines = source.splitlines(keepends=True)
    imports = []
    while lines and lines[0].startswith("import "):
        imports.append(lines.pop(0).strip().removeprefix("import "))
    require(imports, "selected source has no initial plain imports")
    header = "module\n" + "".join(("public " if public else "") + f"import {m}\n" for m in imports)
    if meta:
        header += "".join(f"meta import {m}\n" for m in imports)
    return header + ("@[expose] " if exposed else "") + ("public section\n" if public else "") + "".join(lines)


def prepare(output, variant):
    root = output / variant
    root.mkdir()
    (root / "scripts").mkdir()
    (root / "Applications").mkdir()
    (root / "clients").mkdir()
    for path in INPUTS:
        shutil.copy2(ROOT / path, root / path)
    return root


def audit(trial, root):
    source = (ROOT / "ProofAudit.lean").read_text()
    require(source.count("import SquareApplications\n") == 1, "audit entrypoint changed")
    (root / "ProofAudit.lean").write_text(source.replace("import SquareApplications\n",
        "import Verification\nimport Applications.Boundary\n", 1))
    (root / "Applications/AuditSlice.lean").write_text('''import ProofAudit
private theorem localHidden : True := True.intro
set_option trace.ProofAudit.roots true in
#audit_project_axioms
''' + SCAN)
    sources = [f"{m}.lean" for m in FOUNDATION] + ["Applications/Boundary.lean", "Applications/AuditSlice.lean", "ProofAudit.lean"]
    imports = trial.preflight(root, sources)
    inventory = json.loads(trial.run(root.name + "-inventory", ["python3", "scripts/project_sources.py"], root))
    require(set(inventory) == set(FOUNDATION) | {"Applications.Boundary", "Applications.AuditSlice"}, inventory)
    trial.compile(root, "ProofAudit")
    text = trial.compile(root, "Applications/AuditSlice")
    actual = re.findall(r"\[ProofAudit.roots\] (\S+)", text)
    expected = set(re.findall(r"^REFERENCE (\S+)$", text, re.M))
    require(actual and len(actual) == len(set(actual)) and set(actual) == expected, "audit roots differ from independent scan")
    require("CategoricalCompiler.Term.rec" in expected, "generated recursor missing")
    require(any("hiddenBoundary" in name and "_private" in name for name in expected), "private boundary missing")
    require(any("localHidden" in name and "_private" in name for name in expected), "current private root missing")
    counts = {name: [0, 0, 0] for name in inventory}
    for module, theorem, unsafe in re.findall(r"^COUNTER (\S+) (true|false) (true|false)$", text, re.M):
        count = counts.setdefault(module, [0, 0, 0])
        count[2 if unsafe == "true" else 0] += 1
        if unsafe == "false" and theorem == "true":
            count[1] += 1
    reported = {m: list(map(int, (a, b, c))) for m, a, b, c in re.findall(
        r"  (\S+): (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations", text)}
    require(counts == reported, f"audit counts differ: {counts} != {reported}")
    public = sorted(re.findall(r"^PUBLIC (\S+) (\S+)$", text, re.M))
    # Empty Verification is still in the source inventory, even without roots.
    result = {"roots": len(expected), "counts": counts, "public_names": public,
              "imports": dict(zip(sources, imports, strict=True)), "inventory": inventory}
    (root / "audit-summary.json").write_text(json.dumps(result, indent=2) + "\n")
    (root / "scripts/project_sources.py").rename(root / "scripts/project_sources.saved")
    trial.compile(root, "Applications/AuditSlice", expected=1,
                  diagnostic="Cannot obtain project source inventory")
    (root / "scripts/project_sources.saved").rename(root / "scripts/project_sources.py")
    return result


def negative_controls(trial, output):
    # Separate the failure mechanisms instead of attributing every failed client
    # to declaration visibility. These are actual Compiler source copies.
    for variant, public, exposed in (("naive", False, False), ("public", True, False), ("exposed", True, True)):
        root = output / variant
        root.mkdir()
        shutil.copy2(ROOT / "lean-toolchain", root / "lean-toolchain")
        (root / "Compiler.lean").write_text(convert((ROOT / "Compiler.lean").read_text(), public=public, exposed=exposed))
        if variant == "public":
            trial.compile(root, "Compiler", expected=1, diagnostic="definition is not exposed")
            continue
        trial.compile(root, "Compiler")
        if variant == "naive":
            body = "#check CategoricalCompiler.square\n"
            diagnostic = "Unknown identifier"
        else:
            body = "#eval CategoricalCompiler.distribute ((1, Sum.inl 2) : Nat × Sum Nat Nat)\n"
            diagnostic = "meta"
        (root / "Client.lean").write_text("module\nimport Compiler\n" + body)
        trial.compile(root, "Client", expected=1, diagnostic=diagnostic)
        if variant == "exposed":
            (root / "Wrapper.lean").write_text("module\nimport Compiler\npublic def wrapperValue : Nat := 42\n")
            trial.compile(root, "Wrapper")
            (root / "Transitive.lean").write_text("module\nimport Wrapper\n#check wrapperValue\n#check CategoricalCompiler.square\n")
            trial.compile(root, "Transitive", expected=1, diagnostic="Unknown identifier")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new directory for sources, logs and summary")
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.exists(), "output directory must not already exist")
    output.mkdir(parents=True)
    trial = Trial(output)
    version = trial.run("version", ["lean", "--version"], ROOT).strip()
    expected_version = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    require(f"version {expected_version}" in version, "compiler does not match lean-toolchain")
    hashes = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in INPUTS}
    # Discover closure using exactly the production inventory and Lean parser.
    inventory = json.loads(trial.run("production-inventory", ["python3", "scripts/project_sources.py"], ROOT))
    manifest = output / "production-sources.json"
    manifest.write_text(json.dumps([name.replace(".", "/") + ".lean" for name in inventory] + ["ProofAudit.lean"]))
    headers = json.loads(trial.run("production-preflight", ["lean", "--run", "scripts/lean-source-info.lean", str(manifest)], ROOT))
    graph = dict(zip(inventory + ["ProofAudit"], headers, strict=True))
    closure = set()
    def visit(name):
        if name in closure or name not in graph:
            return
        closure.add(name)
        for dependency in graph[name]:
            visit(dependency)
    visit("Verification")
    require(closure == set(FOUNDATION), f"foundation dependency closure changed: {closure}")
    (output / "production-graph.json").write_text(json.dumps(graph, indent=2) + "\n")
    results = {"closure": sorted(closure), "direct_consumers": {
        name: imports for name, imports in graph.items()
        if name not in closure and any(dep in closure for dep in imports)}}
    for variant in ("legacy", "compatible"):
        root = prepare(output, variant)
        if variant == "compatible":
            for module in FOUNDATION:
                path = root / f"{module}.lean"
                path.write_text(convert(path.read_text(), meta=module == "Verification"))
        # Run the production standalone contract, not a replacement build loop.
        trial.run(variant + "-foundation", ["sh", "check-foundation.sh"], root)
        boundary = "import Verification\n" + BOUNDARY
        if variant == "compatible":
            boundary = convert(boundary)
        (root / "Applications/Boundary.lean").write_text(boundary)
        trial.compile(root, "Applications/Boundary")
        for client in ("Legacy", "Module"):
            header = "import Applications.Boundary\n"
            if client == "Module":
                header = "module\n" + header + "meta import Applications.Boundary\n"
            body = CLIENT + '''open scoped ModuleTrial
example : trialSquare = CategoricalCompiler.square := rfl
'''
            (root / f"clients/{client}.lean").write_text(header + body)
            if variant == "legacy" and client == "Module":
                trial.compile(root, "clients/Module", expected=1, diagnostic="cannot import non-`module`")
            else:
                text = trial.compile(root, f"clients/{client}")
                require("49\n" in text and "8\n" in text, "missing evaluated outputs")
        (root / "clients/Private.lean").write_text("import Applications.Boundary\n#check ModuleTrial.hiddenBoundary\n")
        trial.compile(root, "clients/Private", expected=1, diagnostic="Unknown identifier")
        results[variant] = audit(trial, root)
    # Names are compared for the actual foundation, excluding the synthetic boundary.
    old = {tuple(p) for p in results["legacy"]["public_names"] if p[0] in FOUNDATION}
    new = {tuple(p) for p in results["compatible"]["public_names"] if p[0] in FOUNDATION}
    # Pinned Lean changes generated matcher visibility under this policy. Keep
    # the exact delta visible rather than silently discarding generated names.
    removed = {(module, namespace + ".instReprTy.repr.match_1") for module, namespace in
               (("Compiler", "CategoricalCompiler"), ("FirstOrder", "FirstOrderCompiler"))}
    added = {(module, namespace + ".Val.match_1") for module, namespace in
             (("Compiler", "CategoricalCompiler"), ("FirstOrder", "FirstOrderCompiler"))}
    require(old - new == removed and new - old == added,
            f"unexpected foundation export delta: missing {old-new}; extra {new-old}")
    results["generated_export_delta"] = {"removed": sorted(removed), "added": sorted(added)}
    for variant, prefix in (("legacy", ""), ("compatible", "module\n")):
        root = output / variant
        (root / "clients/AllNames.lean").write_text(prefix + "import Verification\n" +
            "".join(f"#check {name}\n" for _, name in sorted(old if variant == "legacy" else old & new)))
        trial.compile(root, "clients/AllNames")
    for index, (_, name) in enumerate(sorted(removed)):
        root = output / "compatible"
        (root / f"clients/Removed{index}.lean").write_text("module\nimport Verification\n#check " + name + "\n")
        trial.compile(root, f"clients/Removed{index}", expected=1, diagnostic="Unknown constant")
    results["public_foundation_names"] = {"legacy": len(old), "compatible": len(new), "common": len(old & new)}
    negative_controls(trial, output)
    results["version"] = version
    results["input_sha256"] = hashes
    require(hashes == {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in INPUTS}, "inputs changed during trial")
    (output / "summary.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"PASS: foundation contract, client compatibility, preflight, inventory, exact audit roots; {len(old & new)} preserved public foundation names; two generated matcher export changes")
    print(output / "summary.json")


if __name__ == "__main__":
    main()

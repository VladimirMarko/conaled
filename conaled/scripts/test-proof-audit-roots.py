#!/usr/bin/env python3
"""Compare public audit root diagnostics with an independent exhaustive scan.

The fixture uses the real audit implementation with a small import closure.
Run in the development shell; no project build is needed.
"""

from pathlib import Path
import os
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="conaled-audit-roots-") as directory:
        root = Path(directory)
        (root / "Applications").mkdir()
        (root / "Foreign.lean").write_text("axiom unusedForeign : False\n")
        (root / "Applications/AuditProbe.lean").write_text('''import Foreign
import Lean
namespace AuditFixture
inductive Tree where
  | leaf
  | branch (left right : Tree)
deriving Repr
instance : Inhabited Tree := ⟨.leaf⟩
def Tree.size : Tree → Nat
  | .leaf => 1
  | .branch a b => a.size + b.size
private theorem hidden : True := True.intro
end AuditFixture
''')
        (root / "ProofAudit.lean").write_text(
            (ROOT / "ProofAudit.lean").read_text().replace(
                "import SquareApplications", "import Applications.AuditProbe", 1))
        (root / "Applications/LocalAudit.lean").write_text('''import ProofAudit
private theorem localTrue : True := True.intro
def localValue : Nat := 42
set_option trace.ProofAudit.roots true in
#audit_project_axioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    let origin := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if (origin == `Applications.AuditProbe || origin == `Applications.LocalAudit) && !info.isUnsafe then
      IO.println s!"REFERENCE {name}"
''')
        env = os.environ.copy()
        env["LEAN_PATH"] = str(root)
        lean = env.get("LEAN", "lean")
        for name in ("Foreign", "Applications/AuditProbe", "ProofAudit", "Applications/LocalAudit"):
            result = subprocess.run(
                [lean, "-R", str(root), "-o", str(root / (name + ".olean")),
                 str(root / (name + ".lean"))], env=env, cwd=ROOT,
                capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise RuntimeError(f"{name}: {result.stdout}{result.stderr}")
        output = result.stdout + result.stderr
        actual = re.findall(r"\[ProofAudit.roots\] (\S+)", output)
        expected = set(re.findall(r"^REFERENCE (\S+)$", output, re.MULTILINE))
        assert actual, output
        assert len(actual) == len(set(actual)), "duplicate roots"
        assert set(actual) == expected, f"missing {expected - set(actual)}; extra {set(actual) - expected}"
        assert "AuditFixture.Tree.rec" in expected
        assert "AuditFixture.Tree.size" in expected
        assert "localValue" in expected
        assert any("_private" in n and "hidden" in n for n in expected)
        assert any("_private" in n and "localTrue" in n for n in expected)
        assert "unusedForeign" not in expected
        print(f"PASS: exact root equality ({len(expected)} roots; private, generated, and local declarations)")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exercise imported private declarations through the public proof-audit command.

Run in the development shell: python3 scripts/test-proof-audit.py
Fixtures deliberately contain forbidden constructs, outside the project tree.
The real audit is compiled against a small fixture entrypoint, without cached
project artifacts. The full verification command separately checks integration.
"""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def check_case(name: str, source: str, rejection: str | None, *, root_module=False) -> None:
    with tempfile.TemporaryDirectory(prefix=f"conaled-audit-{name}-") as directory:
        root = Path(directory)
        (root / "external").mkdir()
        (root / "scripts").mkdir()
        shutil.copy2(ROOT / "lean-toolchain", root / "lean-toolchain")
        shutil.copy2(ROOT / "scripts/project_sources.py", root / "scripts/project_sources.py")
        (root / "Applications").mkdir()
        (root / "SquareApplications.lean").write_text("def fixtureBaseline : Nat := 0\n")
        shutil.copy2(ROOT / "ProofAudit.lean", root / "ProofAudit.lean")
        # This axiom belongs to an external module. The audit must follow the
        # private project theorem's dependency, not just reject an owned axiom.
        (root / "external/Foreign.lean").write_text("axiom foreignClaim : True\n")
        module = "NewRoot" if root_module else "Applications.AuditProbe"
        probe = root / (module.replace(".", "/") + ".lean")
        probe.write_text("import Foreign\n" + source)
        audit = root / "Audit.lean"
        audit.write_text(
            f"import {module}\nimport ProofAudit\n#audit_project_axioms\n"
        )
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(root), str(root / "external")])
        lean = env.get("LEAN", "lean")
        for path in (root / "SquareApplications.lean", root / "ProofAudit.lean",
                     root / "external/Foreign.lean", probe):
            source_root = root / "external" if path.name == "Foreign.lean" else root
            result = subprocess.run(
                [lean, "-R", str(source_root), "-o", str(path.with_suffix(".olean")), str(path)],
                env=env, cwd=root, capture_output=True, text=True, timeout=60,
            )
            if result.returncode:
                raise RuntimeError(f"{name}: fixture failed to compile\n{result.stdout}{result.stderr}")
        result = subprocess.run(
            [lean, "-R", str(root), str(audit)],
            env=env, cwd=root, capture_output=True, text=True, timeout=60,
        )
        output = result.stdout + result.stderr
        if rejection is None:
            passed = result.returncode == 0 and "Proof audit PASSED" in output
        else:
            passed = result.returncode != 0 and rejection in output
        if not passed:
            raise RuntimeError(f"{name}: unexpected audit result\n{output}")
        print(f"PASS: {name}", flush=True)


def main() -> None:
    check_case("unused-external-axiom", "private theorem harmless : True := True.intro\n", None)
    check_case("root-unused-external-axiom", "private theorem harmless : True := True.intro\n", None,
               root_module=True)
    check_case("root-private-transitive-axiom", "private theorem hidden : True := foreignClaim\n",
               "Forbidden transitive axioms in '_private.NewRoot", root_module=True)
    check_case(
        "private-transitive-axiom",
        "private theorem hidden : True := foreignClaim\n",
        "Forbidden transitive axioms in '_private.Applications.AuditProbe",
    )
    check_case(
        "private-admission",
        "private theorem hidden : True := by sorry\n",
        "sorryAx",
    )
    check_case(
        "source-unsafe",
        "unsafe def unsafeProbe : Nat := 0\n",
        "Proof audit FAILED: unsafe declarations with source ranges",
    )


if __name__ == "__main__":
    main()

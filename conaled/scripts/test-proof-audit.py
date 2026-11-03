#!/usr/bin/env python3
"""Exercise imported private declarations through the public proof-audit command.

Run after `lake build`: lake env python3 scripts/test-proof-audit.py
Fixtures deliberately contain forbidden constructs, outside the project tree.
"""

from pathlib import Path
import os
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def check_case(name: str, source: str, rejection: str | None) -> None:
    with tempfile.TemporaryDirectory(prefix=f"conaled-audit-{name}-") as directory:
        root = Path(directory)
        (root / "Applications").mkdir()
        # Lean resolves a module prefix from one search-path entry. Preserve
        # the real Applications imports beside our additional probe module.
        for path in (ROOT / ".lake/build/lib/lean/Applications").iterdir():
            (root / "Applications" / path.name).symlink_to(path)
        # This axiom belongs to an external module. The audit must follow the
        # private project theorem's dependency, not just reject an owned axiom.
        (root / "Foreign.lean").write_text("axiom foreignClaim : True\n")
        probe = root / "Applications/AuditProbe.lean"
        probe.write_text("import Foreign\n" + source)
        audit = root / "Audit.lean"
        audit.write_text(
            "import Applications.AuditProbe\nimport ProofAudit\n#audit_project_axioms\n"
        )
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(root), env.get("LEAN_PATH", "")])
        lean = env.get("LEAN", "lean")
        for path in (root / "Foreign.lean", probe):
            result = subprocess.run(
                [lean, "-R", str(root), "-o", str(path.with_suffix(".olean")), str(path)],
                env=env, capture_output=True, text=True,
            )
            if result.returncode:
                raise RuntimeError(f"{name}: fixture failed to compile\n{result.stdout}{result.stderr}")
        result = subprocess.run(
            [lean, "-R", str(root), str(audit)],
            env=env, capture_output=True, text=True,
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

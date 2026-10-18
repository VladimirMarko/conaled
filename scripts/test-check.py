#!/usr/bin/env python3
"""Exercise the public fresh-verification command with real Lean fixture projects."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class FreshVerification(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="conaled-check-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "scripts").mkdir()
        (self.root / "Applications").mkdir()
        (self.root / ".lake").mkdir()
        (self.root / ".lake/packages").symlink_to(ROOT / ".lake/packages")
        for name in ("check.sh", "lean-toolchain", "scripts/check.py"):
            shutil.copy2(ROOT / name, self.root / name)
        self.write("SquareApplications", "import Applications.A\nimport Applications.B\n")
        self.write("Applications.A", "def a : Nat := 1\n")
        self.write("Applications.B", "def b : Nat := 2\n")
        self.write("ProofAudit", 'import SquareApplications\nimport Lean\nrun_cmd IO.FS.writeFile "audit-ran" "yes"\n')

    def write(self, module, source):
        (self.root / (module.replace(".", "/") + ".lean")).write_text(source)

    def check(self, *args):
        env = os.environ.copy()
        # Caller search paths must not provide fixture project artifacts.
        env.pop("LEAN_PATH", None)
        return subprocess.run(["./check.sh", *args], cwd=self.root, env=env,
                              capture_output=True, text=True, timeout=45)

    def test_independent_compilation_overlaps_and_audit_waits(self):
        for name, other in (("A", "B"), ("B", "A")):
            self.write("Applications." + name, f'''import Lean
run_cmd do
  IO.FS.writeFile "{name}-started" "yes"
  let mut ready := false
  for _ in [:200] do
    if ← System.FilePath.pathExists "{other}-started" then
      ready := true
      break
    IO.sleep 25
  unless ready do throwError "independent compilation did not overlap"
  IO.FS.writeFile "{name}-done" "yes"
''')
        self.write("SquareApplications", '''import Applications.A
import Applications.B
run_cmd do
  unless (← System.FilePath.pathExists "A-done") && (← System.FilePath.pathExists "B-done") do
    throwError "dependent compiled before imports completed"
  IO.FS.writeFile "entrypoint-done" "yes"
''')
        self.write("ProofAudit", '''import SquareApplications
run_cmd do
  unless ← System.FilePath.pathExists "entrypoint-done" do
    throwError "audit ran before entrypoint completed"
  IO.FS.writeFile "audit-ran" "yes"
''')
        result = self.check("--jobs", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.root / "audit-ran").exists())


    def test_serial_runs_recompile_unchanged_sources_and_ignore_stale_artifacts(self):
        source = self.root / "Applications/A.lean"
        for target in (self.root / "Applications/A.olean",
                       self.root / ".lake/build/lib/lean/Applications/A.olean"):
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["lean", "-o", str(target), str(source)], cwd=self.root,
                           check=True, capture_output=True, text=True)
        stale = (self.root / "Applications/A.olean").read_bytes()
        self.write("Applications.A", '''import Lean
 def a : Nat := 7
run_cmd do
  let path : System.FilePath := "compilation-count"
  let previous ← if ← path.pathExists then IO.FS.readFile path else pure "0"
  let count := previous.toNat!
  IO.FS.writeFile path (toString (count + 1))
''')
        self.write("Applications.B", "import Applications.A\nexample : a = 7 := rfl\n")
        for expected in ("1", "2"):
            result = self.check("--jobs", "1")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual((self.root / "compilation-count").read_text(), expected)
        self.assertEqual((self.root / "Applications/A.olean").read_bytes(), stale)
        self.assertFalse((self.root / "Applications/B.olean").exists())
        self.assertFalse(list((self.root / ".lake").glob("fresh-check-*")))

    def test_failed_import_blocks_dependents_and_audit(self):
        self.write("Applications.A", "#check missingFixtureDeclaration\n")
        self.write("Applications.B", '''import Applications.A
import Lean
run_cmd IO.FS.writeFile "dependent-ran" "yes"
''')
        result = self.check("--jobs", "2")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Applications.A", result.stdout + result.stderr)
        self.assertFalse((self.root / "dependent-ran").exists())
        self.assertFalse((self.root / "audit-ran").exists())
        self.assertFalse(list((self.root / ".lake").glob("fresh-check-*")))

    def test_omitted_source_is_rejected_before_compilation(self):
        self.write("Applications.Omitted", "def omitted : Nat := 0\n")
        result = self.check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Applications.Omitted", result.stderr)
        self.assertFalse((self.root / "audit-ran").exists())

    def test_audit_failure_is_not_reported_as_success(self):
        self.write("ProofAudit", "import SquareApplications\n#check missingAuditDeclaration\n")
        result = self.check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missingAuditDeclaration", result.stdout + result.stderr)
        self.assertNotIn("PASS: all", result.stdout)

    def test_source_guard_rejects_admission(self):
        self.write("Applications.A", "theorem admitted : False := by sorry\n")
        result = self.check()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Forbidden source construct", result.stderr)
        self.assertFalse((self.root / "audit-ran").exists())

    def test_compiler_version_must_match_pin(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        # An explicit executable avoids elan trying to install the fake pin.
        env = os.environ.copy()
        env["LEAN"] = subprocess.check_output(["elan", "which", "lean"], text=True).strip()
        result = subprocess.run(["./check.sh"], cwd=self.root, env=env,
                                capture_output=True, text=True, timeout=15)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Expected leanprover/lean4:v0.0.0", result.stderr)

    def test_invalid_concurrency_is_rejected(self):
        for value in ("0", "-1", "many"):
            result = self.check("--jobs", value)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("positive integer", result.stderr)


if __name__ == "__main__":
    unittest.main()

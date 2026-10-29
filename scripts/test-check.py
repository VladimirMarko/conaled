#!/usr/bin/env python3
"""Exercise incremental and fresh verification with real Lean fixture projects."""

from pathlib import Path
import json
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
        (self.root / "lakefile.toml").write_text('name = "fixture"\n[[lean_lib]]\nname = "SquareApplications"\nglobs = ["SquareApplications", "Applications.+", "ProofAudit"]\n')
        for name in ("check.sh", "lean-toolchain", "scripts/check.py"):
            shutil.copy2(ROOT / name, self.root / name)
        self.write("SquareApplications", "import Applications.A\nimport Applications.B\n")
        self.write("Applications.A", "def a : Nat := 1\n")
        self.write("Applications.B", "def b : Nat := 2\n")
        self.write("ProofAudit", 'import SquareApplications\nimport Lean\nrun_cmd IO.FS.writeFile "audit-ran" "yes"\n')

    def write(self, module, source):
        (self.root / (module.replace(".", "/") + ".lean")).write_text(source)

    def check(self, *args, fresh=True):
        env = os.environ.copy()
        # Caller search paths must not provide fixture project artifacts.
        env.pop("LEAN_PATH", None)
        return subprocess.run(["./check.sh", *(["--fresh"] if fresh else []), *args], cwd=self.root, env=env,
                              capture_output=True, text=True, timeout=45)

    def commit_candidate(self):
        (self.root / ".gitignore").write_text(".lake/\naudit-ran\n")
        subprocess.run(["lake", "update"], cwd=self.root, check=True,
                       capture_output=True)
        for command in (["git", "init"], ["git", "config", "user.name", "Fixture"],
                        ["git", "config", "user.email", "fixture@example.invalid"],
                        ["git", "add", "."], ["git", "commit", "-m", "fixture"]):
            subprocess.run(command, cwd=self.root, check=True, capture_output=True)
        return subprocess.check_output(["git", "rev-parse", "HEAD"],
                                       cwd=self.root, text=True).strip()

    def test_candidate_record_is_bound_to_clean_commit(self):
        candidate = self.commit_candidate()
        result = self.check("--candidate", candidate, fresh=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        record = json.loads((self.root / ".lake/verification.json").read_text())
        self.assertEqual(record["candidate"], candidate)
        self.assertEqual(record["mode"], "incremental")
        result = self.check("--verify-candidate", candidate, fresh=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Building", result.stdout)
        self.write("Applications.A", "def a : Nat := 3\n")
        result = self.check("--verify-candidate", candidate, fresh=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("clean", result.stderr)
        subprocess.run(["git", "restore", "Applications/A.lean"], cwd=self.root, check=True)
        subprocess.run(["git", "-c", "commit.gpgsign=false", "commit", "--allow-empty", "-m", "next"],
                       cwd=self.root, check=True, capture_output=True)
        result = self.check("--verify-candidate", "HEAD", fresh=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("record", result.stderr)

    def test_candidate_rejects_edits_during_audit_and_clears_old_record(self):
        candidate = self.commit_candidate()
        result = self.check("--candidate", candidate)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((self.root / ".lake/verification.json").exists())
        self.write("ProofAudit", '''import SquareApplications
import Lean
run_cmd IO.FS.writeFile "Applications/A.lean" "def a : Nat := 999\\n"
''')
        subprocess.run(["git", "add", "ProofAudit.lean"], cwd=self.root, check=True)
        subprocess.run(["git", "commit", "-m", "mutating fixture"], cwd=self.root,
                       check=True, capture_output=True)
        result = self.check("--candidate", "HEAD")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("clean checkout", result.stderr)
        self.assertNotIn("PASS: all", result.stdout)
        self.assertFalse((self.root / ".lake/verification.json").exists())

    def test_candidate_rejects_untracked_inputs_and_ignored_lean_sources(self):
        candidate = self.commit_candidate()
        (self.root / "notes.txt").write_text("uncommitted")
        result = self.check("--candidate", candidate, fresh=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("clean checkout", result.stderr)
        (self.root / "notes.txt").unlink()
        (self.root / ".git/info/exclude").write_text("Applications/Ignored.lean\n")
        self.write("Applications.Ignored", "def hidden : Nat := 0\n")
        result = self.check("--candidate", candidate, fresh=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("tracked", result.stderr)

    def test_missing_malformed_records_and_failed_development_check(self):
        candidate = self.commit_candidate()
        record = self.root / ".lake/verification.json"
        for contents in (None, "{", "null", '{}'):
            if contents is not None:
                record.write_text(contents)
            result = self.check("--verify-candidate", candidate, fresh=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("No usable verification record", result.stderr)
        result = self.check("--candidate", candidate, fresh=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.write("Applications.A", "theorem admitted : False := by sorry\n")
        result = self.check(fresh=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(record.exists())

    def test_candidate_rejects_dirty_or_wrong_revision_dependency(self):
        self.commit_candidate()
        packages = self.root / ".lake/packages"
        packages.unlink()
        dependency = packages / "fixturedep"
        dependency.mkdir(parents=True)
        (dependency / "source.txt").write_text("original")
        for command in (["git", "init"], ["git", "config", "user.name", "Fixture"],
                        ["git", "config", "user.email", "fixture@example.invalid"],
                        ["git", "add", "."], ["git", "commit", "-m", "dependency"]):
            subprocess.run(command, cwd=dependency, check=True, capture_output=True)
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                           cwd=dependency, text=True).strip()
        manifest_path = self.root / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["packages"] = [{"type": "git", "name": "fixturedep", "rev": revision}]
        manifest_path.write_text(json.dumps(manifest))
        subprocess.run(["git", "add", "lake-manifest.json"], cwd=self.root, check=True)
        subprocess.run(["git", "commit", "-m", "pin fixture dependency"], cwd=self.root,
                       check=True, capture_output=True)
        (dependency / "source.txt").write_text("modified")
        result = self.check("--candidate", "HEAD")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("clean checkout", result.stderr)
        subprocess.run(["git", "add", "."], cwd=dependency, check=True)
        subprocess.run(["git", "commit", "-m", "different revision"], cwd=dependency,
                       check=True, capture_output=True)
        result = self.check("--candidate", "HEAD")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Dependency revision differs", result.stderr)

    def test_incremental_reuses_sources_but_reruns_audit_and_invalidates_imports(self):
        self.write("Applications.A", "def a : Nat := 7\n")
        self.write("Applications.B", "import Applications.A\nexample : a = 7 := rfl\n")
        for module, marker in (("Applications.A", "compilation-count"),
                               ("ProofAudit", "audit-count")):
            path = self.root / (module.replace(".", "/") + ".lean")
            original = path.read_text()
            path.write_text("import Lean\n" + original + f'''run_cmd do
  let path : System.FilePath := "{marker}"
  let previous ← if ← path.pathExists then IO.FS.readFile path else pure "0"
  IO.FS.writeFile path (toString (previous.toNat! + 1))
''')
        for expected in ("1", "2"):
            result = self.check(fresh=False)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual((self.root / "compilation-count").read_text(), "1")
            self.assertEqual((self.root / "audit-count").read_text(), expected)
        self.write("Applications.A", "def a : Nat := 8\n")
        result = self.check(fresh=False)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / "audit-count").read_text(), "2")
        self.assertNotIn("PASS: all", result.stdout)

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
        for fresh in (False, True):
            with self.subTest(fresh=fresh):
                result = self.check(fresh=fresh)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Applications.Omitted", result.stderr)
                self.assertFalse((self.root / "audit-ran").exists())

    def test_audit_failure_is_not_reported_as_success(self):
        self.write("ProofAudit", "import SquareApplications\n#check missingAuditDeclaration\n")
        for fresh in (False, True):
            with self.subTest(fresh=fresh):
                result = self.check(fresh=fresh)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("missingAuditDeclaration", result.stdout + result.stderr)
                self.assertNotIn("PASS: all", result.stdout)

    def test_source_guard_rejects_admission(self):
        self.write("Applications.A", "theorem admitted : False := by sorry\n")
        for fresh in (False, True):
            with self.subTest(fresh=fresh):
                result = self.check(fresh=fresh)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Forbidden source construct", result.stderr)
                self.assertFalse((self.root / "audit-ran").exists())

    def test_compiler_version_must_match_pin(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        # An explicit executable avoids elan trying to install the fake pin.
        env = os.environ.copy()
        env["LEAN"] = subprocess.check_output(["elan", "which", "lean"], text=True).strip()
        result = subprocess.run(["./check.sh", "--fresh"], cwd=self.root, env=env,
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

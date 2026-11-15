#!/usr/bin/env python3
"""Exercise persistent acceptance through its CLI and the real Lean verifier."""

import fcntl
import importlib.util
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("check_fixtures", ROOT / "scripts/test-check.py")
fixtures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixtures)


class CandidateWorkspace(unittest.TestCase):
    def setUp(self):
        fixture = fixtures.FreshVerification()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.fixture = fixture
        self.root = fixture.root
        # The tiny fixture supplies the same pinned executables without a new
        # Nix evaluation. direnv correctly unloads the caller's environment.
        (self.root / ".envrc").write_text("export PATH=" + shlex.quote(os.environ["PATH"]) + "\n")
        fixture.write("ProofAudit", (ROOT / "ProofAudit.lean").read_text())
        fixture.write("SquareApplications", "import Applications.B\nimport Applications.C\n")
        for name, imports, definition in [
            ("A", "", "def a : Nat := 7"),
            ("B", "import Applications.A\n", "def b : Nat := a + 1"),
            ("C", "", "def c : Nat := 12"),
        ]:
            fixture.write(f"Applications.{name}", "import Lean\n" + imports + definition + f'''
run_cmd do
  IO.FS.createDirAll ".counts"
  let p : System.FilePath := ".counts/{name}"
  let old ← if ← p.pathExists then IO.FS.readFile p else pure "0"
  IO.FS.writeFile p (toString (old.toNat! + 1))
''')
        fixture.commit_candidate()
        with (self.root / ".gitignore").open("a") as output:
            output.write(".counts/\n.direnv/\n")
        self.commit("ignore fixture observations")
        self.workspace = self.root / ".git/conaled/acceptance"

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True).strip()

    def commit(self, message):
        self.git("add", ".")
        self.git("commit", "-m", message)
        return self.git("rev-parse", "HEAD")

    def run_candidate(self, revision="HEAD", *args):
        return subprocess.run([sys.executable, str(ROOT / "scripts/check-candidate.py"),
                               "--repo", str(self.root), revision, *args],
                              capture_output=True, text=True, timeout=90)

    def accepted(self, revision="HEAD", *args):
        result = self.run_candidate(revision, *args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Proof audit:", result.stdout)
        record = json.loads((self.workspace / ".lake/verification.json").read_text())
        self.assertEqual(record["candidate"], self.git("rev-parse", revision))
        self.assertEqual(self.run_candidate(revision, "--verify").returncode, 0)
        return result

    def counts(self):
        return {name: int((self.workspace / f".counts/{name}").read_text())
                for name in ("A", "B", "C")}

    def test_warm_and_changed_candidates_retain_unaffected_compilation(self):
        first = self.git("rev-parse", "HEAD")
        self.accepted(first)
        self.assertEqual(self.counts(), {"A": 1, "B": 1, "C": 1})
        # A dirty caller is permitted: only the resolved commit is checked.
        (self.root / "caller-notes").write_text("preserve this")
        self.accepted(first)
        self.assertEqual(self.counts(), {"A": 1, "B": 1, "C": 1})
        self.assertEqual((self.root / "caller-notes").read_text(), "preserve this")
        (self.root / "caller-notes").unlink()
        path = self.root / "Applications/B.lean"
        path.write_text(path.read_text().replace("a + 1", "a + 2"))
        leaf = self.commit("change leaf")
        self.accepted(leaf)
        self.assertEqual(self.counts(), {"A": 1, "B": 2, "C": 1})
        path = self.root / "Applications/A.lean"
        path.write_text(path.read_text().replace(":= 7", ":= 8"))
        foundation = self.commit("change foundation")
        self.accepted(foundation)
        self.assertEqual(self.counts(), {"A": 2, "B": 3, "C": 1})

    def test_refusals_preserve_workspace_and_failed_check_clears_receipt(self):
        first = self.git("rev-parse", "HEAD")
        self.accepted(first)
        state = self.workspace.parent
        receipt = self.workspace / ".lake/verification.json"
        original = receipt.read_bytes()
        notes = self.workspace / "notes"
        notes.write_text("keep this")
        result = self.run_candidate(first)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("has edits", result.stderr)
        self.assertEqual(notes.read_text(), "keep this")
        self.assertEqual(receipt.read_bytes(), original)
        notes.unlink()
        with (state / "acceptance.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            result = self.run_candidate(first)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("busy", result.stderr)
        marker = state / "acceptance-running.json"
        marker.write_text('{"pid": 0}')
        result = self.run_candidate(first)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("interrupted run", result.stderr)
        self.assertEqual(receipt.read_bytes(), original)
        marker.unlink()
        self.fixture.write("Applications.B", "import Applications.A\naxiom forbidden : False\n")
        bad = self.commit("introduce forbidden declaration")
        result = self.run_candidate(bad)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(receipt.exists())
        self.assertNotEqual(self.run_candidate(bad, "--verify").returncode, 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), bad)
        self.assertNotEqual(self.run_candidate(first, "--verify").returncode, 0)
        self.assertEqual(subprocess.check_output(
            ["git", "-C", str(self.workspace), "rev-parse", "HEAD"], text=True).strip(), bad)
        self.accepted(first)
        self.assertEqual(self.git("rev-parse", "HEAD"), bad)
        self.accepted(first, "--fresh", "--jobs", "1")
        record = json.loads(receipt.read_text())
        self.assertEqual(record["mode"], "fresh")

    def test_unowned_workspace_is_preserved(self):
        self.workspace.mkdir(parents=True)
        notes = self.workspace / "notes"
        notes.write_text("existing work")
        result = self.run_candidate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unowned", result.stderr)
        self.assertEqual(notes.read_text(), "existing work")


if __name__ == "__main__":
    unittest.main()

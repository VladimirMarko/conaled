#!/usr/bin/env python3
"""Exercise persistent acceptance through its CLI and the real Lean verifier."""

import fcntl
import importlib.util
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import time
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

    def status(self):
        result = subprocess.run([sys.executable, str(ROOT / "scripts/check-candidate.py"),
                                 "--repo", str(self.root), "--status"],
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return json.loads(result.stdout)

    def test_status_is_read_only_and_distinguishes_failure_and_unknown(self):
        state = self.root / ".git/conaled"
        self.assertEqual(self.status()["outcome"], "not-started")
        self.assertFalse(state.exists())
        self.accepted()
        before = {str(p.relative_to(state)): (p.read_bytes(), p.stat().st_mtime_ns)
                  for p in state.glob("*") if p.is_file()}
        status = self.status()
        self.assertEqual(status["outcome"], "passed")
        self.assertEqual(status["candidate"], self.git("rev-parse", "HEAD"))
        self.assertEqual(status["phase"], "complete")
        self.assertGreaterEqual(status["elapsed_seconds"], 0)
        after = {str(p.relative_to(state)): (p.read_bytes(), p.stat().st_mtime_ns)
                 for p in state.glob("*") if p.is_file()}
        self.assertEqual(before, after)
        self.fixture.write("Applications.B", "#check nonexistentName\n")
        bad = self.commit("failing compiler fixture")
        self.assertNotEqual(self.run_candidate(bad).returncode, 0)
        self.assertEqual(self.status()["outcome"], "failed")
        (state / "acceptance-running.json").write_text('{"candidate":"uncertain"}')
        self.assertEqual(self.status()["outcome"], "unknown")
        saved = json.loads((state / "acceptance-status.json").read_text())
        for field in ("phase", "outcome"):
            with self.subTest(malformed=field):
                (state / "acceptance-status.json").write_text(json.dumps({**saved, field: []}))
                self.assertEqual(self.status()["outcome"], "unknown")
        for value in (10**400, -1, float("nan"), True):
            with self.subTest(malformed_elapsed=str(value)):
                (state / "acceptance-status.json").write_text(json.dumps({**saved, "elapsed_seconds": value}))
                self.assertEqual(self.status()["outcome"], "unknown")
        (state / "acceptance-status.json").write_text("{")
        self.assertEqual(self.status()["outcome"], "unknown")

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

    def test_diagnostic_policy_change_reuses_compilation(self):
        config = self.root / "lakefile.toml"
        enabled = config.read_text()
        config.write_text(enabled.replace('["-EhasSorry"]', '[]'))
        self.accepted(self.commit("disable diagnostic severity"))
        before = self.counts()
        config.write_text(enabled)
        self.accepted(self.commit("enable diagnostic severity"))
        self.assertEqual(self.counts(), before)

    def test_clean_candidate_retains_outputs_and_records_its_mode(self):
        candidate = self.git("rev-parse", "HEAD")
        self.accepted(candidate)
        self.accepted(candidate, "--clean")
        self.assertEqual(self.counts(), {"A": 2, "B": 2, "C": 2})
        record = json.loads((self.workspace / ".lake/verification.json").read_text())
        self.assertEqual(record["mode"], "clean")
        for args in (("--clean", "--fresh"), ("--clean", "--verify"),
                     ("--clean", "--jobs", "1")):
            result = self.run_candidate(candidate, *args)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads((self.workspace / ".lake/verification.json").read_text()), record)
        self.accepted(candidate)
        self.assertEqual(self.counts(), {"A": 2, "B": 2, "C": 2})
        path = self.root / "Applications/A.lean"
        path.write_text(path.read_text().replace(":= 7", ":= 8"))
        self.accepted(self.commit("change clean-built dependency"))
        self.assertEqual(self.counts(), {"A": 3, "B": 3, "C": 2})

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

    def test_clean_refuses_symlink_before_touching_external_receipt(self):
        self.accepted()
        # Also ignore a symlink named .lake, so Git cleanliness does not mask
        # the output-root refusal that this public command must provide.
        exclude = Path(self.git("rev-parse", "--git-path", "info/exclude"))
        with (self.root / exclude).open("a") as out:
            out.write("\n.lake\n")
        for name in (".lake", ".lake/build"):
            with self.subTest(path=name):
                path = self.workspace / name
                saved = self.root / "saved-outputs"
                path.rename(saved)
                receipt = saved / "verification.json"
                if not receipt.exists():
                    receipt.write_text("external receipt")
                before = receipt.read_bytes()
                path.symlink_to(saved, target_is_directory=True)
                try:
                    result = self.run_candidate("HEAD", "--clean")
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("real .lake", result.stderr)
                    self.assertEqual(receipt.read_bytes(), before)
                    self.assertFalse((self.workspace.parent / "acceptance-running.json").exists())
                finally:
                    path.unlink()
                    saved.rename(path)

    def test_real_interruption_stops_resistant_process_group_and_recovers(self):
        first = self.git("rev-parse", "HEAD")
        self.accepted(first)
        (self.root / "blocking.py").write_text('''import json, os, signal, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, "scripts")
from verification_status import phase
phase("building")
signal.signal(signal.SIGTERM, signal.SIG_IGN)
signal.signal(signal.SIGINT, signal.SIG_IGN)
child = subprocess.Popen([sys.executable, "-c", "import signal,time; from pathlib import Path; signal.signal(signal.SIGTERM,signal.SIG_IGN); signal.signal(signal.SIGINT,signal.SIG_IGN); Path('.counts/child-ready').touch(); time.sleep(120)"])
Path('.counts/processes').write_text(json.dumps([os.getpid(), child.pid]))
time.sleep(120)
''')
        (self.root / "check.sh").write_text("#!/usr/bin/env bash\nexec python3 blocking.py\n")
        blocked = self.commit("controlled resistant verifier fixture")
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGKILL):
            with self.subTest(signal=sig):
                pids = []
                for name in ("processes", "child-ready"):
                    (self.workspace / ".counts" / name).unlink(missing_ok=True)
                process = subprocess.Popen([sys.executable, str(ROOT / "scripts/check-candidate.py"),
                                            "--repo", str(self.root), blocked],
                                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                try:
                    deadline = time.monotonic() + 15
                    while not all((self.workspace / ".counts" / name).exists()
                                  for name in ("child-ready", "processes")):
                        self.assertIsNone(process.poll(), "wrapper exited before fixture readiness")
                        self.assertLess(time.monotonic(), deadline, "fixture did not become ready")
                        time.sleep(.02)
                    pids = json.loads((self.workspace / ".counts/processes").read_text())
                    self.assertEqual(self.status()["outcome"], "running")
                    self.assertEqual(self.status()["candidate"], blocked)
                    self.assertEqual(self.status()["phase"], "building")
                    process.send_signal(sig)
                    if sig == signal.SIGKILL:
                        process.wait(timeout=5)
                        # The verifier still holds the inherited lock after the
                        # controller crashes; recovery cannot race that child.
                        self.assertEqual(self.status()["outcome"], "running")
                        self.assertIn("busy", self.run_candidate(first).stderr)
                        os.killpg(pids[0], signal.SIGKILL)
                    stdout, stderr = process.communicate(timeout=8)
                    self.assertNotEqual(process.returncode, 0, stdout + stderr)
                    for pid in pids:
                        stat = Path(f"/proc/{pid}/stat")
                        deadline = time.monotonic() + 2
                        while True:
                            try:
                                state = stat.read_text().rsplit(")", 1)[1].split()[0]
                            except FileNotFoundError:
                                break
                            if state == "Z":
                                break
                            self.assertLess(time.monotonic(), deadline,
                                            f"process {pid} still executing after cleanup")
                            time.sleep(.01)
                    self.assertFalse((self.workspace / ".lake/verification.json").exists())
                    self.assertEqual(self.status()["outcome"],
                                     "unknown" if sig == signal.SIGKILL else "interrupted")
                    result = self.run_candidate(first)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("interrupted run", result.stderr)
                finally:
                    if pids:
                        try:
                            os.killpg(pids[0], signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    if process.poll() is None:
                        process.kill()
                    process.communicate(timeout=5)
                (self.workspace.parent / "acceptance-running.json").unlink()
                self.accepted(first)


if __name__ == "__main__":
    unittest.main()

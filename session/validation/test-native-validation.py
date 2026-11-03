#!/usr/bin/env python3
"""Test the runner's public CLI refusal paths; never run a compiler or build.

Fixtures contain only deliberately nonpassing evidence or held locks. They
live in temporary workspace directories and are removed after each test.
"""

from pathlib import Path
import fcntl
import json
import shutil
import subprocess
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent


class RunnerGuards(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="runner-guard-test-", dir=HERE)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.validation = self.root / "session/validation"
        self.validation.mkdir(parents=True)
        self.runner = self.validation / "run-native-validation.py"
        shutil.copy2(HERE / self.runner.name, self.runner)

    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(self.runner), *args],
                              cwd=self.root, capture_output=True, text=True,
                              timeout=10)

    def test_existing_record_is_refused_without_overwrite(self):
        evidence = self.validation / "historical.json"
        original = b"HISTORICAL TEST SENTINEL\n"
        evidence.write_bytes(original)
        for flags in ((), ("--fresh",)):
            with self.subTest(flags=flags):
                result = self.run_cli("full", "historical", *flags)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Evidence path already exists", result.stderr)
                self.assertEqual(evidence.read_bytes(), original)
                self.assertFalse((self.validation / "historical.log").exists())

    def test_interrupted_full_record_cannot_support_verification(self):
        evidence = self.validation / "interrupted.json"
        original = json.dumps({"mode": "full", "status": "running",
                               "acceptance": False}).encode()
        evidence.write_bytes(original)
        result = self.run_cli("verify", "review", "--full-record", "interrupted")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Full evidence is not a successful finished run", result.stderr)
        self.assertEqual(evidence.read_bytes(), original)
        self.assertFalse((self.validation / "review.json").exists())

    def test_an_active_full_job_excludes_another_full_job(self):
        locks = self.root / "active-validation"
        locks.mkdir()
        with (locks / "full-build.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.run_cli("full", "second")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Validation lock is already held", result.stderr)
        self.assertFalse((self.validation / "second.json").exists())

    def test_focus_candidate_is_explicit_and_still_obeys_focus_lock(self):
        for mode, candidate in (("full", "a" * 40), ("focus", "HEAD")):
            result = self.run_cli(mode, "invalid", "--focus-candidate", candidate)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("--focus-candidate requires focus", result.stderr)
            self.assertFalse((self.validation / "invalid.json").exists())
        locks = self.root / "active-validation"
        locks.mkdir()
        with (locks / "focused-build.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.run_cli("focus", "second", "--focus-candidate", "a" * 40)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Validation lock is already held", result.stderr)
        self.assertFalse((self.validation / "second.json").exists())


if __name__ == "__main__":
    unittest.main()

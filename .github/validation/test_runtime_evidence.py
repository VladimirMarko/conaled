#!/usr/bin/env python3
"""Small public-CLI fixtures for the runtime evidence comparator; no Lean execution."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

DRIVER = Path(__file__).with_name("textbooks-runtime074.py").resolve()
TEST = "__main__.ExtractRuntime.test_fixture"
DIRECT = ["lake", "env", "lean", "--run", "scripts/ExtractSearchTree.lean"]
NATIVE = [".lake/build/bin/extract-searchtree"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_record(folder, number, *, kind, arguments, stdout, stderr=b"", inputs=(), exit=0, test=TEST):
    prefix = f"{test.rsplit('.', 1)[-1]}-{number:03d}"
    mode = folder.name
    command = (DIRECT if mode == "direct" else NATIVE) + arguments if kind == "driver" else [
        sys.executable, "-B", "/candidate/scripts/test-extract-searchtree.py", *arguments]
    meta = {"kind": kind, "test": test, "invocation": number, "command": command,
            "arguments": arguments, "returncode": exit, "started_utc": "2026-11-20T08:00:00+00:00",
            "seconds": 0.1, "stdout_file": prefix + ".stdout", "stdout_sha256": digest(stdout),
            "stderr_file": prefix + ".stderr", "stderr_sha256": digest(stderr), "input_files": []}
    (folder / meta["stdout_file"]).write_bytes(stdout)
    (folder / meta["stderr_file"]).write_bytes(stderr)
    for index, (option, path, data) in enumerate(inputs):
        record = {"option": option, "path": path}
        if data is None:
            record["missing"] = True
        else:
            name = prefix + f".input-{index}"
            (folder / name).write_bytes(data)
            record.update(bytes=len(data), sha256=digest(data), retained_file=name)
        meta["input_files"].append(record)
    (folder / (prefix + ".json")).write_text(json.dumps(meta) + "\n")


def fixture(root):
    (root / "plan.json").write_text(json.dumps({"expected_tests": [TEST], "python_executable": sys.executable,
                                               "harness_path": "/candidate/scripts/test-extract-searchtree.py"}))
    for mode, elapsed in (("direct", 100), ("standalone", 9999)):
        folder = root / mode
        folder.mkdir()
        base = "/tmp/" + mode + "-fixture"
        keys, receipt, missing = [base + "/" + name for name in ("keys.txt", "receipt.json", "missing.txt")]
        output = json.dumps({"schema": 3, "config": {"keysFile": keys},
                             "samples": [{"elapsedNs": elapsed, "keys": ["7", "2", "7"]}]}).encode()
        write_record(folder, 1, kind="driver", arguments=["binom-workload", "--pattern", "replay", "--keys-file", keys],
                     stdout=output, inputs=[("--keys-file", keys, b"7\n2\n7\n")])
        write_record(folder, 2, kind="observer", arguments=["--check-receipt", receipt], stdout=b'{"status":"accepted"}\n',
                     inputs=[("--check-receipt", receipt, output)])
        write_record(folder, 3, kind="driver", arguments=["binom-workload", "--pattern", "replay", "--keys-file", missing],
                     stdout=b"", stderr=("cannot read " + missing + "\n").encode(), inputs=[("--keys-file", missing, None)], exit=1)


def alter_input(root, mode, data):
    path = root / mode / "test_fixture-002.json"
    meta = json.loads(path.read_text())
    record = meta["input_files"][0]
    (root / mode / record["retained_file"]).write_bytes(data)
    record.update(bytes=len(data), sha256=digest(data))
    path.write_text(json.dumps(meta))


class ComparatorCLI(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="runtime-comparator-fixture-")
        self.root = Path(self.temporary.name)
        fixture(self.root)

    def tearDown(self):
        self.temporary.cleanup()

    def invoke(self):
        return subprocess.run([sys.executable, "-B", str(DRIVER), "compare", "--out", str(self.root)],
                              capture_output=True, check=False)

    def assert_passes(self):
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return json.loads(result.stdout)

    def assert_rejects(self, reason):
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(reason, result.stderr.decode())

    def test_complete_pair_allows_only_timing_and_bound_fixture_paths(self):
        result = self.assert_passes()
        self.assertEqual(result["invocations_per_mode"], 3)
        self.assertEqual(result["driver_invocations_per_mode"], 2)
        self.assertEqual(len(result["absent_path_bindings"]), 1)

    def test_changed_semantic_output_is_rejected_even_with_updated_digest(self):
        path = self.root / "standalone/test_fixture-001.json"
        meta = json.loads(path.read_text())
        stdout = self.root / "standalone" / meta["stdout_file"]
        data = stdout.read_bytes().replace(b'"7", "2", "7"', b'"7", "3", "7"')
        stdout.write_bytes(data)
        meta["stdout_sha256"] = digest(data)
        path.write_text(json.dumps(meta))
        self.assert_rejects("complete stdout semantic output differs")

    def test_changed_replay_bytes_are_rejected(self):
        path = self.root / "standalone/test_fixture-001.json"
        meta = json.loads(path.read_text()); record = meta["input_files"][0]
        data = b"7\n2\n8\n"
        (path.parent / record["retained_file"]).write_bytes(data)
        record.update(bytes=len(data), sha256=digest(data)); path.write_text(json.dumps(meta))
        self.assert_rejects("actual replay file bytes differ")

    def test_bad_saved_hash_is_rejected(self):
        path = self.root / "standalone/test_fixture-001.stdout"
        path.write_bytes(path.read_bytes() + b" ")
        self.assert_rejects("retained bytes changed")

    def test_extra_unaccounted_artifact_is_rejected(self):
        (self.root / "direct/extra.stdout").write_bytes(b"forgotten observation")
        self.assert_rejects("unaccounted direct invocation artifacts")

    def test_missing_input_identity_is_rejected(self):
        path = self.root / "standalone/test_fixture-003.json"
        meta = json.loads(path.read_text()); meta["input_files"] = []
        path.write_text(json.dumps(meta))
        self.assert_rejects("input identities do not cover exactly")

    def test_missing_path_without_authenticated_parent_is_rejected(self):
        for mode in ("direct", "standalone"):
            folder = self.root / mode
            for path in folder.iterdir():
                path.unlink()
            missing = "/tmp/" + mode + "-unbound/missing.txt"
            write_record(folder, 1, kind="driver", arguments=["binom-workload", "--keys-file", missing],
                         stdout=b"", stderr=("cannot read " + missing).encode(), inputs=[("--keys-file", missing, None)], exit=1)
        self.assert_rejects("missing-file path lacks a directory binding")

    def test_absent_basename_is_not_erased(self):
        path = self.root / "standalone/test_fixture-003.json"
        meta = json.loads(path.read_text())
        meta["arguments"][-1] = meta["arguments"][-1].replace("missing.txt", "different.txt")
        meta["command"][-1] = meta["arguments"][-1]
        meta["input_files"][0]["path"] = meta["arguments"][-1]
        path.write_text(json.dumps(meta))
        self.assert_rejects("not paired temporary fixture names")

    def test_duplicate_members_are_preserved_in_observer_inputs(self):
        alter_input(self.root, "direct", b'{"schema":3,"schema":4,"samples":[{"elapsedNs":1}]}')
        alter_input(self.root, "standalone", b'{"schema":4,"samples":[{"elapsedNs":5}]}')
        self.assert_rejects("observer inputs differ")

    def test_invalid_elapsed_values_are_not_normalized(self):
        for invalid in (b"-1", b"true", b"1.0", b"NaN", b"Infinity", b"-Infinity"):
            with self.subTest(value=invalid):
                alter_input(self.root, "direct", b'{"samples":[{"elapsedNs":' + invalid + b'}]}')
                alter_input(self.root, "standalone", b'{"samples":[{"elapsedNs":42}]}')
                self.assert_rejects("observer inputs differ")

    def test_same_malformed_utf8_and_json_bytes_survive(self):
        for data in (b"\xff", b"{", b'{"schema":3,"schema":4}', b'{"elapsedNs":NaN}'):
            with self.subTest(data=data):
                for mode in ("direct", "standalone"):
                    alter_input(self.root, mode, data)
                self.assert_passes()

    def test_different_malformed_bytes_fail(self):
        alter_input(self.root, "direct", b"\xff")
        alter_input(self.root, "standalone", b"\xfe")
        self.assert_rejects("observer inputs differ")

    def test_parent_binding_cannot_be_borrowed_from_another_test(self):
        other = "__main__.ExtractRuntime.test_other"
        planpath = self.root / "plan.json"
        plan = json.loads(planpath.read_text()); plan["expected_tests"].append(other)
        planpath.write_text(json.dumps(plan))
        for mode in ("direct", "standalone"):
            missing = "/tmp/" + mode + "-fixture/other-missing.txt"
            write_record(self.root / mode, 1, kind="driver", arguments=["binom-workload", "--keys-file", missing],
                         stdout=b"", stderr=b"missing", inputs=[("--keys-file", missing, None)], exit=1, test=other)
        self.assert_rejects("missing-file path lacks a directory binding")

    def test_verify_rejects_actual_failed_capture_before_any_identity_probe(self):
        (self.root / "failure.json").write_text('{"result":"failed"}')
        (self.root / "result.json").write_text('{"result":"passed"}')
        result = subprocess.run([sys.executable, "-B", str(DRIVER), "verify", "--out", str(self.root),
                                 "--repo", str(self.root / "nonexistent-candidate")], capture_output=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("capture recorded an actual failure", result.stderr.decode())


if __name__ == "__main__":
    unittest.main(verbosity=2)

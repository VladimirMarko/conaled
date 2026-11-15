"""Exercise the command/file boundary with real, short Python children."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
RECORDER = ROOT / "recorder.py"


class RecorderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix=".test-", dir=ROOT)
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.attempt = self.directory / "attempt"

    def invocation(self, child, *options):
        return [
            sys.executable, "-B", str(RECORDER),
            "--cwd", str(self.directory),
            "--attempt-dir", str(self.attempt),
            "--candidate", "test-candidate", "--mode", "test",
            *options, "--", *child,
        ]

    def read_json(self, name):
        return json.loads((self.attempt / name).read_text())

    def wait_until(self, predicate, timeout=5):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if predicate():
                return
            time.sleep(0.01)
        self.fail("owned test process did not reach the requested state in time")

    def test_direct_capture_nonzero_return_and_explicit_configuration(self):
        child = [sys.executable, "-c", """
import json, os, stat, sys
print(json.dumps({
    'argument': sys.argv[1],
    'explicit': os.environ['RECORDER_TEST_EXPLICIT'],
    'stdout_regular': stat.S_ISREG(os.fstat(1).st_mode),
    'stderr_regular': stat.S_ISREG(os.fstat(2).st_mode),
    'stdin_closed': os.read(0, 1) == b'',
}), flush=True)
print('retained stderr', file=sys.stderr, flush=True)
sys.exit(7)
""", "$(no-shell); literal argument"]
        env = os.environ.copy()
        env["RECORDER_TEST_INHERITED"] = "not-an-output-setting"
        result = subprocess.run(
            self.invocation(child, "--env", "RECORDER_TEST_EXPLICIT=visible"),
            env=env, capture_output=True, text=True, timeout=15,
        )
        self.assertEqual(result.returncode, 7, result.stderr)
        lines = (self.attempt / "child.log").read_text().splitlines()
        self.assertEqual(json.loads(lines[0]), {
            "argument": "$(no-shell); literal argument", "explicit": "visible",
            "stdout_regular": True, "stderr_regular": True, "stdin_closed": True,
        })
        self.assertEqual(lines[1], "retained stderr")
        launch_text = (self.attempt / "launch.json").read_text()
        launch = json.loads(launch_text)
        self.assertEqual(launch["requested"]["command"], child)
        self.assertEqual(launch["requested"]["environment_changes"], {
            "RECORDER_TEST_EXPLICIT": "visible",
        })
        self.assertNotIn("not-an-output-setting", launch_text)
        self.assertEqual(launch["recorder"]["python_executable"], sys.executable)
        self.assertEqual(len(launch["recorder"]["source_sha256"]), 64)
        state = self.read_json("run.json")
        self.assertEqual(state["state"], "finished")
        self.assertEqual(state["recorder_outcome"], "completed")
        self.assertEqual(state["child_returncode"], 7)
        self.assertEqual(state["recorder_exit_code"], 7)
        self.assertFalse(state["descendant_quiescence_verified"])
        self.assertEqual(self.attempt.stat().st_mode & 0o777, 0o700)

    def test_recording_failure_stops_owned_child_with_bounded_grace(self):
        child = [sys.executable, "-c", """
import signal, time
signal.signal(signal.SIGTERM, lambda *_: print('received SIGTERM', flush=True))
print('child ready', flush=True)
time.sleep(30)
"""]
        invocation = self.invocation(
            child, "--heartbeat-seconds", "0.01", "--cleanup-grace-seconds", "0.1",
        )
        # A genuine per-process filesystem write failure, without mocks, device
        # exhaustion, permissions changes or effects on any other process.
        limiter = [sys.executable, "-c", """
import os, resource, signal, sys
signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
resource.setrlimit(resource.RLIMIT_FSIZE, (16384, 16384))
os.execv(sys.executable, [sys.executable, *sys.argv[1:]])
""", *invocation[1:]]
        sentinel = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
        try:
            started = time.monotonic()
            result = subprocess.run(limiter, capture_output=True, text=True, timeout=12)
            self.assertEqual(result.returncode, 125, result.stderr)
            self.assertLess(time.monotonic() - started, 10)
            state = self.read_json("run.json")
            self.assertEqual(state["recorder_outcome"], "failed")
            self.assertEqual(state["child_returncode"], -signal.SIGKILL)
            self.assertTrue(state["errors"])
            self.assertIn("File too large", state["errors"][0]["detail"])
            self.assertIn("received SIGTERM", (self.attempt / "child.log").read_text())
            self.assertIsNone(sentinel.poll(), "cleanup reached an unrelated process")
            self.assertFalse(state["descendant_quiescence_verified"])
        finally:
            if sentinel.poll() is None:
                sentinel.kill()
            sentinel.wait(timeout=5)

    def test_zero_and_negative_raw_returns_are_not_recorder_failures(self):
        for label, code, raw, exit_code in (
            ("zero", "pass", 0, 0),
            ("signal", "import os, signal; os.kill(os.getpid(), signal.SIGTERM)", -signal.SIGTERM, 143),
        ):
            with self.subTest(label=label):
                self.attempt = self.directory / label
                result = subprocess.run(
                    self.invocation([sys.executable, "-c", code]),
                    capture_output=True, text=True, timeout=10,
                )
                self.assertEqual(result.returncode, exit_code, result.stderr)
                state = self.read_json("run.json")
                self.assertEqual(state["recorder_outcome"], "completed")
                self.assertEqual(state["child_returncode"], raw)
                self.assertEqual(state["child_status"], "reaped")
                last = json.loads((self.attempt / "heartbeat.log").read_text().splitlines()[-1])
                self.assertEqual(last["child_poll_returncode"], raw)

    def test_existing_attempt_is_preserved_and_command_is_not_started(self):
        self.attempt.mkdir()
        original = self.attempt / "run.json"
        original.write_bytes(b'{"earlier": "untouched"}\n')
        marker = self.directory / "should-not-exist"
        result = subprocess.run(
            self.invocation([sys.executable, "-c", "from pathlib import Path; Path('should-not-exist').touch()"]),
            capture_output=True, text=True, timeout=10,
        )
        self.assertEqual(result.returncode, 125)
        self.assertEqual(original.read_bytes(), b'{"earlier": "untouched"}\n')
        self.assertEqual(list(self.attempt.iterdir()), [original])
        self.assertFalse(marker.exists())

    def test_launch_failure_does_not_invent_a_child_return(self):
        result = subprocess.run(
            self.invocation([str(self.directory / "missing-executable")]),
            capture_output=True, text=True, timeout=10,
        )
        self.assertEqual(result.returncode, 125)
        state = self.read_json("run.json")
        self.assertEqual(state["recorder_outcome"], "failed")
        self.assertIsNone(state["child_returncode"])
        self.assertIsNone(state["child"])
        self.assertEqual(state["child_status"], "no_child_handle")
        self.assertEqual(state["errors"][0]["type"], "FileNotFoundError")

    def test_automatic_child_reaping_is_refused_instead_of_inventing_zero(self):
        invocation = self.invocation([sys.executable, "-c", "raise SystemExit(23)"])
        wrapper = [sys.executable, "-c", """
import os, signal, sys
signal.signal(signal.SIGCHLD, signal.SIG_IGN)
os.execv(sys.executable, [sys.executable, *sys.argv[1:]])
""", *invocation[1:]]
        result = subprocess.run(wrapper, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 125)
        state = self.read_json("run.json")
        self.assertEqual(state["recorder_outcome"], "failed")
        self.assertIsNone(state["child_returncode"])
        self.assertIsNone(state["child"])
        self.assertIn("SIGCHLD", state["errors"][0]["detail"])

    def test_heartbeat_keeps_running_state_stable_and_interrupt_is_distinct(self):
        child = [sys.executable, "-c", """
import signal, sys, time
signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))
print('child ready', flush=True)
time.sleep(30)
"""]
        process = subprocess.Popen(
            self.invocation(child, "--heartbeat-seconds", "0.05", "--cleanup-grace-seconds", "0.2"),
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        try:
            self.wait_until(lambda: (self.attempt / "child.log").exists()
                            and "child ready" in (self.attempt / "child.log").read_text())
            self.wait_until(lambda: self.read_json("run.json")["state"] == "running")
            run_path = self.attempt / "run.json"
            before = (run_path.read_bytes(), run_path.stat().st_mtime_ns)
            self.wait_until(lambda: (self.attempt / "heartbeat.log").read_bytes().count(b"\n") >= 3)
            self.assertEqual((run_path.read_bytes(), run_path.stat().st_mtime_ns), before)
            heartbeats = [json.loads(line) for line in (self.attempt / "heartbeat.log").read_text().splitlines()]
            self.assertGreaterEqual(len(heartbeats), 3)
            self.assertEqual([item["sequence"] for item in heartbeats], list(range(1, len(heartbeats) + 1)))
            self.assertTrue(all(item["child_poll_returncode"] is None for item in heartbeats))
            self.assertLess(heartbeats[0]["elapsed_seconds"], heartbeats[-1]["elapsed_seconds"])
            process.send_signal(signal.SIGINT)
            self.assertEqual(process.wait(timeout=5), 130)
            state = self.read_json("run.json")
            self.assertEqual(state["recorder_outcome"], "interrupted")
            self.assertEqual(state["interrupt_signal"], signal.SIGINT)
            # The requested interruption and the child's cooperative zero exit
            # must not be conflated with normal recorder completion.
            self.assertEqual(state["child_returncode"], 0)
            self.assertFalse(state["descendant_quiescence_verified"])
        finally:
            if process.poll() is None:
                process.send_signal(signal.SIGINT)
            process.wait(timeout=5)


if __name__ == "__main__":
    unittest.main()

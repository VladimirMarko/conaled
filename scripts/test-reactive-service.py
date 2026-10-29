#!/usr/bin/env python3
"""Public stdin/stdout checks for the finite-state synchronous runner."""
import subprocess
import os
import select
import time
import unittest

COMMAND = ["lake", "env", "lean", "--run", "scripts/reactive-service.lean"]


class ReactiveService(unittest.TestCase):
    def test_delay_trace(self):
        result = subprocess.run(COMMAND, input=b"10110", capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout, b"01011")

    def test_two_delays(self):
        result = subprocess.run(COMMAND + ["twice"], input=b"10110", capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout, b"00101")

    def test_invalid_byte_stops_after_accepted_outputs(self):
        result = subprocess.run(COMMAND, input=b"10x1", capture_output=True, timeout=60)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"01")
        self.assertIn(b"expected ASCII 0 or 1", result.stderr)

    def test_empty_session(self):
        result = subprocess.run(COMMAND, input=b"", capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout, b"")

    def test_invalid_mode(self):
        result = subprocess.run(COMMAND + ["unknown"], input=b"1", capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"usage:", result.stderr)

    def test_incremental_and_long_stream(self):
        # Keep stdin open: output must arrive before EOF or another input.
        # Consume every block before producing another; no lifetime transcript.
        process = subprocess.Popen(COMMAND, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)
        def read_exact(count):
            result = bytearray()
            deadline = time.monotonic() + 60
            while len(result) < count:
                ready, _, _ = select.select([process.stdout], [], [], max(0, deadline-time.monotonic()))
                self.assertTrue(ready, "output stalled while stdin remained open")
                part = os.read(process.stdout.fileno(), count-len(result))
                self.assertTrue(part, "runner stopped before completing output")
                result.extend(part)
            return bytes(result)
        try:
            process.stdin.write(b"1")
            process.stdin.flush()
            self.assertEqual(read_exact(1), b"0")
            # Each block starts with previous input 1, ends with current input 1.
            block = b"01" * 2048
            for _ in range(32):
                process.stdin.write(block)
                process.stdin.flush()
                self.assertEqual(read_exact(len(block)), b"10" * 2048)
            process.stdin.close()
            self.assertEqual(process.wait(timeout=60), 0, process.stderr.read().decode())
            self.assertEqual(process.stdout.read(), b"")
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
            process.stdout.close()
            process.stderr.close()


if __name__ == "__main__":
    unittest.main()

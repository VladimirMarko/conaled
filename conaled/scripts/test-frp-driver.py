#!/usr/bin/env python3
"""Exercise the public bounded FRP stdin/stdout protocol."""
import subprocess
import unittest

COMMAND = ["lake", "env", "lean", "--run", "scripts/frp-driver.lean"]


def run(data, **kwargs):
    return subprocess.run(COMMAND, input=data, capture_output=True, timeout=60, **kwargs)


class DriverTests(unittest.TestCase):
    def test_normal(self):
        result = run(b"begin 0 2\nsource left 3 1 2 2 3 4\nsource right 3 1 2 1 3\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.decode().splitlines(), [
            "ok packet - status accepted response - aggregate -",
            "ok packet accepted status - response - aggregate -",
            "ok packet accepted status - response - aggregate -",
            "ok packet - status - response 0 2 3 3 4 3 aggregate 1 10",
        ])

    def test_empty_is_not_silence_and_sources_are_complete_windows(self):
        result = run(b"begin 0 0\nprocess 0\nsource left 1 0\nprocess 0\nsource right 1 0\nprocess 0\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(lines[1], "ok packet - status - response - aggregate -")
        self.assertEqual(lines[3], "ok packet - status - response - aggregate -")
        self.assertEqual(lines[5], "ok packet - status - response 0 0 0 aggregate 1 0")
        self.assertEqual(lines[6], "ok packet - status - response - aggregate -")

    def test_rejected_busy_stale_wrong_id_and_retained_consumer(self):
        result = run(b"begin 0 0\nbegin 1 0\nsource left 1 1 0 2 7 8\nsource right 1 0\nsource left 0 0\nprocess 1\nprocess 0\nbegin 0 0\nbegin 1 0\nprocess 0\nprocess 1\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertIn("status busy", lines[1])
        self.assertIn("packet rejected", lines[4])
        self.assertEqual(lines[5], "ok packet - status - response - aggregate -")
        self.assertEqual(lines[6], "ok packet - status - response 0 0 2 7 8 aggregate 1 15")
        self.assertIn("status stale", lines[7])
        self.assertEqual(lines[9], "ok packet - status - response - aggregate -")
        self.assertEqual(lines[10], "ok packet - status - response 1 0 2 7 8 aggregate 2 30")

    def test_malformed_and_limits_do_not_mutate_the_lifecycle(self):
        result = run(b"begin 0 0\nsource left 1 1 0 2 9\nbegin 01 0\nbegin 65536 0\nsource left 1 0\nsource right 1 0\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(lines[1:4], ["error malformed", "error malformed", "error limit"])
        self.assertEqual(lines[-1], "ok packet - status - response 0 0 0 aggregate 1 0")

    def test_maximum_id_allows_completion_then_exhausts_without_wrap(self):
        result = run(b"begin 65535 0\nbegin 0 0\nsource left 1 0\nsource right 1 0\nprocess 65535\nbegin 0 0\nbegin 65536 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertIn("status busy", lines[1])
        self.assertEqual(lines[4], "ok packet - status - response 65535 0 0 aggregate 1 0")
        self.assertIn("status stale", lines[5])
        self.assertEqual(lines[6], "error limit")

    def test_output_failure_has_no_retry_or_next_input(self):
        result = subprocess.run(["lake", "env", "lean", "--run", "scripts/frp-driver-faults.lean"],
                                capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, b"failure fixtures passed\n")

    def test_order_and_empty_fragments(self):
        result = run(b"source left 1 3 0 1 7 0 0 0 1 8\nsource right 1 0\nbegin 0 0\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.decode().splitlines()[-1],
                         "ok packet - status - response 0 0 2 7 8 aggregate 1 15")

    def test_packet_capacity_boundaries(self):
        large = b"source left 1 1 0 65 " + b" ".join([b"0"] * 65) + b"\n"
        allowed = b"source left 1 1 0 64 " + b" ".join([b"0"] * 64) + b"\n"
        result = run(large + allowed + b"source right 1 0\nbegin 0 0\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(lines[0], "error limit")
        self.assertEqual(lines[-1], "ok packet - status - response 0 0 64 " +
                         " ".join(["0"] * 64) + " aggregate 1 0")
        fragments = run(b"source left 1 65 " + b" ".join([b"0 0"] * 65) + b"\n" +
                        b"source left 1 64 " + b" ".join([b"0 0"] * 64) + b"\n")
        self.assertEqual(fragments.returncode, 0, fragments.stderr)
        self.assertEqual(fragments.stdout.decode().splitlines(),
                         ["error limit", "ok packet accepted status - response - aggregate -"])

    def test_frames_are_bounded_before_parsing(self):
        for data, expected, code in [
            (b" " * 4096 + b"\n", b"error malformed\n", 0),
            (b" " * 4097 + b"\nidle\n", b"error frame-limit\n", 2),
            (b"begin 0 0", b"error incomplete-frame\n", 2),
            (b"idle\r\n", b"error non-ascii\n", 2),
            (b"\xff\n", b"error non-ascii\n", 2),
        ]:
            with self.subTest(expected=expected):
                result = run(data)
                self.assertEqual(result.returncode, code, result.stderr)
                self.assertEqual(result.stdout, expected)

    def test_frame_budget_counts_invalid_frames(self):
        result = run(b"bad\n" * 257)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(result.stdout.decode().splitlines(),
                         ["error malformed"] * 256 + ["error frame-budget"])

    def test_real_output_failure(self):
        with open("/dev/full", "wb") as full:
            result = subprocess.run(COMMAND, input=b"begin 0 0\nidle\n", stdout=full,
                                    stderr=subprocess.PIPE, timeout=60)
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn(b"publication may be partial; no retry", result.stderr)

    def test_query_limit_leaves_room_for_a_closing_frontier(self):
        result = run(b"begin 0 65535\nbegin 0 65534\nsource left 65535 1 65534 1 65535\nsource right 65535 0\nprocess 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(lines[0], "error limit")
        self.assertEqual(lines[1], "ok packet - status accepted response - aggregate -")
        self.assertEqual(lines[-1],
                         "ok packet - status - response 0 65534 1 65535 aggregate 1 65535")


if __name__ == "__main__":
    unittest.main()

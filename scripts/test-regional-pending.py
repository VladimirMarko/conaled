#!/usr/bin/env python3
"""Independent fork/join oracle through the public pending regional runner."""
import subprocess
import os
import select
import unittest


class RegionalPending(unittest.TestCase):
    def run_client(self, commands, outputs):
        p = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/regional-pending-main.lean'],
                           input=commands, text=True, capture_output=True, timeout=120)
        self.assertEqual(p.returncode, 0, p.stderr)
        lines = p.stdout.splitlines()
        self.assertEqual([x for x in lines if x.startswith('B:')],
                         ['B:' + str(int(x)) for x in outputs])
        return lines

    def test_lost_ack_and_partial_shared_delivery(self):
        # Independent source: output = old XOR NOT input; next = input.
        expected, old = [], False
        for value in (True, True, False):
            expected.append(old ^ (not value))
            old = value
        for first, second in (('', ''), ('ro', ''), ('ho', 'go')):
            commands = '1ewpx1' + first + 'kddtcleD' + second + 'Njpddtcl0ewpddtclq'
            lines = self.run_client(commands, expected)
            self.assertTrue(lines[-1].endswith(':0:0:0:0:0'))
            self.assertEqual(lines.count('C:produced'), 3)
            self.assertEqual(lines.count('C:delivered-D'), 1)
            self.assertEqual(lines.count('C:delivered-N'), 1)

    def test_cancel_owns_internal_deliveries_until_drained(self):
        lines = self.run_client('1enclqDNl0ewpddtclq', [True])
        self.assertIn('C:prevented', lines)
        self.assertIn('C:busy', lines)
        self.assertIn('Q:split:d:0:1:0:2:0', lines)
        self.assertEqual(lines.count('C:drained'), 2)
        self.assertEqual(lines[-1], 'Q:split:d:0:0:0:0:0')

    def test_failures_and_prepared_freeze(self):
        for control, status in [('f', 'allocation'), ('v', 'validation'), ('b', 'capacity'), ('hs', 'cancelled')]:
            lines = self.run_client('1e' + control + 'DNjpddtclq', [False])
            self.assertIn('C:' + status, lines)
        lines = self.run_client('1ehDNsDNjpddtclq', [False])
        self.assertEqual(lines.count('C:frozen'), 2)
        # Unequal retained consumer fields detect the swapped wiring.
        lines = self.run_client('1eDWNjpddtclq', [False])
        self.assertIn('C:validation', lines)

    def test_second_cancel_and_too_late(self):
        lines = self.run_client('10Xewpxnkddtclclq', [False])
        self.assertIn('C:prevented', lines)
        self.assertIn('C:too-late', lines)
        self.assertEqual(lines[-1], 'Q:split:d:1:0:0:0:0')

    def test_control_attempts_do_not_starve_work(self):
        lines = self.run_client('hgohgo1ewpddtclho0ewpddtclq', [False, False])
        self.assertIn('C:throttled', lines)
        self.assertEqual(lines[-1], 'Q:checked:r:0:0:0:0:0')

    def test_policy_is_proposal_and_resumes_partial_dependency(self):
        lines = self.run_client('1eDPoNjpddtclq', [False])
        self.assertIn('C:prepared', lines)
        self.assertIn('C:migrated', lines)
        self.assertEqual(lines.count('C:produced'), 1)
        self.assertEqual(lines.count('C:delivered-D'), 1)
        self.assertEqual(lines.count('C:delivered-N'), 1)

    def test_long_stream_before_eof(self):
        p = subprocess.Popen(['lake', 'env', 'lean', '--run', 'scripts/regional-pending-main.lean'],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             bufsize=0)
        def frame():
            line = bytearray()
            while not line.endswith(b'\n'):
                self.assertTrue(select.select([p.stdout], [], [], 30)[0], 'runner stalled')
                byte = os.read(p.stdout.fileno(), 1)
                self.assertTrue(byte, 'runner exited')
                line.extend(byte)
                self.assertLess(len(line), 64)
            return bytes(line).rstrip(b'\n')
        def command(c):
            p.stdin.write(bytes([c])); p.stdin.flush()
            response = frame()
            effect = None
            if response.startswith(b'B:'):
                effect, response = response, frame()
            return effect, response
        old = False
        try:
            for i in range(128):
                value = bool((i * 7 + i // 3) % 2)
                for c in bytes([48 + value]) + b'eD':
                    self.assertIsNone(command(c)[0])
                if i % 7 == 0:
                    for c in (b'ho' if i % 2 else b'go'):
                        self.assertIsNone(command(c)[0])
                for c in b'Njpx':
                    effect, _ = command(c)
                    if c == ord('x'):
                        self.assertEqual(effect, b'B:1' if old ^ (not value) else b'B:0')
                    else:
                        self.assertIsNone(effect)
                for c in b'kddtcl':
                    self.assertIsNone(command(c)[0])
                old = value
            self.assertTrue(command(ord('q'))[1].endswith(b':0:0:0:0'))
            p.stdin.close()
            self.assertEqual(p.wait(timeout=30), 0, p.stderr.read().decode())
        finally:
            if p.poll() is None:
                p.kill(); p.wait(timeout=10)
            for stream in (p.stdin, p.stdout, p.stderr):
                stream.close()

    def test_fail_stop(self):
        argv = ['lake', 'env', 'lean', '--run', 'scripts/regional-pending-main.lean']
        p = subprocess.run(argv, input='?', text=True, capture_output=True, timeout=120)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn('invalid regional pending command byte', p.stderr)
        # Failure is a control write before any business publication.
        with open('/dev/full', 'wb') as sink:
            p = subprocess.run(argv, input=b'1ewpddtcl', stdout=sink,
                               stderr=subprocess.PIPE, timeout=120)
        self.assertNotEqual(p.returncode, 0)


if __name__ == '__main__':
    unittest.main()

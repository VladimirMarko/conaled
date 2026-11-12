#!/usr/bin/env python3
"""Independent source observations through the executable pending-work adapter."""
import os
import select
import subprocess
import unittest


class PendingMigration(unittest.TestCase):
    def check(self, commands, outputs, mode='delay'):
        p = subprocess.run(['lake', 'env', 'lean', '--run',
                            'scripts/pending-migration.lean', mode],
                           input=commands, capture_output=True, timeout=120)
        self.assertEqual(p.returncode, 0, p.stderr.decode() + p.stdout.decode())
        self.assertEqual([x for x in p.stdout.splitlines() if x.startswith(b'B:')],
                         [b'B:1' if x else b'B:0' for x in outputs])
        return p.stdout

    def test_cancellation_before_effect_and_too_late(self):
        # Tombstone blocks the already queued publication.
        out = self.check(b'1epnrdosddcl0epddtclq', [0])
        self.assertIn(b'C:prevented', out)
        self.assertIn(b'C:busy', out)  # prepared copies freeze dispatch
        self.assertIn(b'C:q:r:0:0:0', out)
        # An effect with lost confirmation cannot be undone or locally committed.
        out = self.check(b'1epxntqkddtclq', [0])
        self.assertIn(b'C:too-late', out)
        self.assertIn(b'C:q:d:0:1:0', out)
        self.assertIn(b'C:q:d:1:0:0', out)

    def test_prepare_failure_and_cancel_preserve_pending_work(self):
        for failure, status in ((b'f', b'allocation-failure'),
                                (b'v', b'validation-failure'),
                                (b'b', b'resource-failure'),
                                (b'rs', b'cancelled')):
            out = self.check(b'1epx0' + failure + b'kddtclepddtclq', [0, 1])
            self.assertIn(b'C:' + status, out)
            self.assertIn(b'C:q:d:0:0:0', out)

    def test_delayed_traffic_quarantine_conflicts_and_reuse(self):
        # A duplicate query generates a reply after local commit; that reply,
        # retry and query all remain owned and block release after close.
        out = self.check(b'1epdkdtdykclqdddl0epddtclq', [0, 1])
        self.assertIn(b'C:refused', out)
        self.assertIn(b'C:q:d:1:1:3', out)
        self.assertIn(b'C:q:d:0:0:0', out)
        # Conflicting retries queued before close must also drain.
        out = self.check(b'1epddtykzclqddd l0epddtclq'.replace(b' ', b''), [0, 1])
        self.assertIn(b'C:refused', out)
        self.assertIn(b'C:q:d:1:1:3', out)
        self.assertIn(b'C:q:d:0:0:0', out)
        out = self.check(b'1epxzddkddtcl', [0])
        self.assertIn(b'C:conflict', out)
        # Four events saturate the owned store; rejection does not hide an
        # extra event outside it. Drain after cancellation before reuse.
        out = self.check(b'1epppppncldddd l0epddtclq'.replace(b' ', b''), [0])
        self.assertIn(b'C:full', out)
        self.assertIn(b'C:q:d:0:0:0', out)

    def test_noninitial_and_repeated_bidirectional_cuts(self):
        for mode, transfer in (('delay', b'ro'), ('redundant', b'ao')):
            for cut in (b'', b'e', b'epx'):
                suffix = {b'': b'epddtcl', b'e': b'pddtcl', b'epx': b'kddtcl'}[cut]
                out = self.check(b'1epddtcl0' + cut + transfer + suffix +
                                 b'1epxroaokddtclq', [0, 1, 0], mode)
                self.assertIn(b'C:q:d:1:0:0', out)

    def test_long_stream_reuses_slots_without_eof(self):
        p = subprocess.Popen(['lake', 'env', 'lean', '--run',
                              'scripts/pending-migration.lean'],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, bufsize=0)
        def line():
            frame = bytearray()
            while not frame.endswith(b'\n'):
                self.assertTrue(select.select([p.stdout], [], [], 30)[0], 'runner stalled')
                byte = os.read(p.stdout.fileno(), 1)
                self.assertTrue(byte, 'runner exited')
                frame.extend(byte)
                self.assertLessEqual(len(frame), 32)
            return bytes(frame).rstrip(b'\n')
        def command(c):
            p.stdin.write(bytes([c]))
            p.stdin.flush()
            response = line()
            effect = None
            if response.startswith(b'B:'):
                effect, response = response, line()
            return effect, response
        try:
            previous = 0
            for i in range(256):
                value = (i * 7 + i // 3) % 2
                for c in bytes([48 + value]) + b'epx':
                    effect, _ = command(c)
                    if c == ord('x'):
                        self.assertEqual(effect, b'B:1' if previous else b'B:0')
                    else:
                        self.assertIsNone(effect)
                if i % 7 == 0:
                    for c in (b'ro' if i % 2 else b'ao'):
                        self.assertIsNone(command(c)[0])
                for c in b'kddtcl':
                    self.assertIsNone(command(c)[0])
                previous = value
            self.assertEqual(command(ord('q'))[1].split(b':')[3:],
                             [str(previous).encode(), b'0', b'0'])
            p.stdin.close()
            self.assertEqual(p.wait(timeout=30), 0, p.stderr.read().decode())
        finally:
            if p.poll() is None:
                p.kill()
                p.wait(timeout=10)
            for stream in (p.stdin,p.stdout,p.stderr):
                stream.close()

    def test_invalid_byte_and_output_failure_stop(self):
        p = subprocess.run(['lake', 'env', 'lean', '--run',
                            'scripts/pending-migration.lean'],
                           input=b'?' * 4096, capture_output=True, timeout=120)
        self.assertNotEqual(p.returncode, 0)
        self.assertIn(b'invalid pending migration command byte', p.stderr)
        # Failure is the first acceptance control frame, before publication.
        with open('/dev/full', 'wb') as sink:
            p = subprocess.run(['lake', 'env', 'lean', '--run',
                                'scripts/pending-migration.lean'],
                               input=b'1epddtcl', stdout=sink, stderr=subprocess.PIPE,
                               timeout=120)
        self.assertNotEqual(p.returncode, 0)

    def test_cancel_second_pending_input(self):
        p = subprocess.run(['lake', 'env', 'lean', '--run',
                            'scripts/pending-migration.lean'],
                           input=b'10Nepddtclclq', capture_output=True, timeout=120)
        self.assertEqual(p.returncode, 0, p.stderr.decode())
        self.assertEqual([x for x in p.stdout.splitlines() if x.startswith(b'B:')], [b'B:0'])
        self.assertIn(b'C:prevented', p.stdout)
        self.assertIn(b'C:q:d:1:0:0', p.stdout)

    def test_lost_confirmation_across_transfer(self):
        # Delay(false,[true,false]) = ([false,true],false). First publication
        # loses its reply; transfer precedes query/confirmation and local commit.
        p = subprocess.run(['lake', 'env', 'lean', '--run',
                            'scripts/pending-migration.lean'],
                           input=b'1epx0rokddtclepddtclq',
                           capture_output=True, timeout=120)
        self.assertEqual(p.returncode, 0, p.stderr.decode())
        lines = p.stdout.splitlines()
        self.assertEqual([x for x in lines if x.startswith(b'B:')], [b'B:0', b'B:1'])
        self.assertIn(b'C:q:r:0:0:0', lines)


if __name__ == '__main__':
    unittest.main()

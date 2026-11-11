#!/usr/bin/env python3
"""Independent public process fixtures for between-tick migration."""
import os
import select
import subprocess
import time
import unittest

COMMAND = ['lake', 'env', 'lean', '--run', 'scripts/migration-service.lean']


def run(data, mode=()):
    return subprocess.run(COMMAND + list(mode), input=data, capture_output=True, timeout=60)


def business(out):
    return [line for line in out.splitlines() if line.startswith(b'B:')]


class Client:
    """Bounded, incremental client: retain only the current response frame."""
    def __init__(self, mode='delay'):
        self.process = subprocess.Popen(COMMAND + [mode], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.buffer = bytearray()

    def line(self):
        deadline = time.monotonic() + 60
        while b'\n' not in self.buffer:
            ready, _, _ = select.select([self.process.stdout], [], [],
                                        max(0, deadline - time.monotonic()))
            if not ready:
                raise AssertionError('output stalled with stdin open')
            chunk = os.read(self.process.stdout.fileno(), 128)
            if not chunk:
                raise AssertionError('runner exited before response')
            self.buffer.extend(chunk)
            if len(self.buffer) > 256:
                raise AssertionError('response exceeded bounded frame')
        end = self.buffer.index(10) + 1
        line = bytes(self.buffer[:end]).rstrip(b'\n')
        del self.buffer[:end]
        return line

    def command(self, byte):
        self.process.stdin.write(byte)
        self.process.stdin.flush()
        first = self.line()
        if first.startswith(b'B:'):
            return [first, self.line()]
        return [first]

    def close(self):
        if not self.process.stdin.closed:
            self.process.stdin.close()
        try:
            code = self.process.wait(timeout=60)
            error = self.process.stderr.read()
            if code:
                raise AssertionError(error.decode())
        finally:
            self.cleanup()

    def cleanup(self):
        if self.process.poll() is None:
            self.process.kill()
            self.process.wait(timeout=10)
        for stream in (self.process.stdin, self.process.stdout, self.process.stderr):
            stream.close()


class MigrationService(unittest.TestCase):
    def check_run(self, data, expected, mode=()):
        p = run(data, mode)
        self.assertEqual(p.returncode, 0, p.stderr.decode())
        self.assertEqual(business(p.stdout), [b'B:' + bytes([48 + x]) for x in expected])
        return p.stdout

    def test_nonempty_both_directions(self):
        self.check_run(b'1eptrmo0eptdmo1ept', [0, 1, 0])
        self.check_run(b'1eptdmo0ept', [0, 1], ['redundant'])

    def test_repeated_transfers_queries(self):
        self.check_run(b'qq1eptqrmodmo0ept1eptrmo1eptdmo0eptqq', [0,1,0,1,1])
        self.check_run(b'qq1eptqq1eptqq', [0,1])

    def test_wait_cancel_and_request_admission(self):
        for prefix in (b'1r', b'1er', b'1epr'):
            suffix = {b'1r': b'ept', b'1er': b'pt', b'1epr': b't'}[prefix]
            out = self.check_run(prefix + b'0mqc' + suffix + b'0ept', [0,1])
            self.assertIn(b'C:busy', out)
        self.check_run(b'1erwwq0mpptmo0ept', [0,1])

    def test_failure_release_and_rejection(self):
        for fail, status in ((b'b', b'resource-failure'), (b'f', b'allocation-failure'),
                             (b'v', b'validation-failure'), (b'mc', b'cancelled')):
            out = self.check_run(b'1eptr' + fail + b'q0ept', [0,1])
            self.assertIn(b'C:' + status + b'\n', out)
            self.assertIn(b'C:q:d:1:idle:0:-:0\n', out)
            self.assertNotIn(b'C:migrated', out)
        out = self.check_run(b'zddq1ept', [0])
        self.assertEqual(out.splitlines()[:4],
                         [b'C:unsupported', b'C:same-backend', b'C:same-backend',
                          b'C:q:d:0:idle:-:-:0'])

    def test_stale_owner_and_duplicate_publish(self):
        out = self.check_run(b'1epprtmou0jeptpp', [0,1])
        self.assertIn(b'C:wrong-owner', out)

    def test_query_phases_and_prepared_cancel(self):
        out = self.check_run(b'q1qeqrqqwqpqtqmqcq0ept', [0,1])
        queries = [x for x in out.splitlines() if x.startswith(b'C:q:')]
        self.assertEqual(queries, [b'C:q:d:0:idle:-:-:0', b'C:q:d:0:accepted:-:-:0',
            b'C:q:d:0:pending:-:-:0', b'C:q:d:0:pending:-:r:0',
            b'C:q:d:0:pending:-:r:0', b'C:q:d:0:pending:-:r:0',
            b'C:q:d:0:published:0:r:0', b'C:q:d:1:idle:0:r:0',
            b'C:q:d:1:idle:0:r:1', b'C:q:d:1:idle:0:-:0'])

    def test_conflicting_request_preserves_target(self):
        out = self.check_run(b'rqdqmoq1ept', [0])
        self.assertIn(b'C:q:d:0:idle:-:r:0', out)
        self.assertIn(b'C:busy', out)
        self.assertIn(b'C:q:r:0:idle:-:-:0', out)

    def test_empty_bad_and_long_malformed_input(self):
        self.check_run(b'', [])
        for data in (b'1ept?0ept', b'1ept?' + b'0ept' * 16384):
            p = run(data)
            self.assertNotEqual(p.returncode, 0)
            self.assertEqual(business(p.stdout), [b'B:0'])
            self.assertIn(b'invalid migration command byte', p.stderr)
        p = run(b'', ['invalid'])
        self.assertEqual(p.returncode, 2)
        self.assertIn(b'usage:', p.stderr)

    def test_incremental_long_stream(self):
        client = Client()
        try:
            self.assertEqual(client.command(b'q'), [b'C:q:d:0:idle:-:-:0'])
            previous = 0
            for index in range(4096):
                value = index % 2
                self.assertEqual(client.command(bytes([48 + value])), [b'C:accepted'])
                self.assertEqual(client.command(b'e'), [b'C:evaluated'])
                self.assertEqual(client.command(b'p'),
                                 [b'B:' + bytes([48 + previous]), b'C:published'])
                self.assertEqual(client.command(b't'), [b'C:tick-committed'])
                previous = value
            self.assertEqual(client.command(b'q'), [b'C:q:d:1:idle:0:-:0'])
            client.close()
        finally:
            client.cleanup()

    @unittest.skipUnless(os.path.exists('/dev/full'), 'requires Linux /dev/full')
    def test_output_failure_terminates_without_replay(self):
        # The first control response fails. This establishes fail-stop handling
        # of an actual stream failure, not the timing of a later business effect.
        with open('/dev/full', 'wb', buffering=0) as sink:
            p = subprocess.run(COMMAND, input=b'1eptrmo0ept', stdout=sink,
                               stderr=subprocess.PIPE, timeout=60)
        self.assertNotEqual(p.returncode, 0)
        self.assertTrue(p.stderr)


if __name__ == '__main__':
    unittest.main()

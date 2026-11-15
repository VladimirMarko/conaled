"""Public CLI and observable artifact tests for captured-attempt-v1 (#194)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import platform
import sys
import selectors
import signal
import subprocess
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
MAIN = Path(__file__).with_name('Main.lean')
FIXTURE = MAIN.with_name('fixture.py')
RECEIPT_CAP = 1024 * 1024
RESULTS = None


def supervised(command, cwd, timeout=30):
    """Drain two pipes with bounded retained prefixes; kill/reap the owned group on error."""
    start = time.monotonic()
    child = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, start_new_session=True)
    streams = {'stdout': bytearray(), 'stderr': bytearray()}
    selector = selectors.DefaultSelector()
    for name, stream in [('stdout', child.stdout), ('stderr', child.stderr)]:
        os.set_blocking(stream.fileno(), False)
        selector.register(stream, selectors.EVENT_READ, name)
    failure = None
    try:
        while selector.get_map():
            if time.monotonic() - start >= timeout:
                raise TimeoutError('external case envelope exhausted')
            for key, _ in selector.select(0.05):
                chunk = os.read(key.fd, 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                buf = streams[key.data]
                room = RECEIPT_CAP - len(buf)
                buf.extend(chunk[:room])
                if len(chunk) > room:
                    raise ValueError('supervisor receipt/diagnostic cap exceeded')
        child.wait(timeout=max(0.01, timeout - (time.monotonic() - start)))
    except Exception as exc:
        failure = str(exc)
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait(timeout=5)
    finally:
        selector.close()
        child.stdout.close()
        child.stderr.close()
    return {'command': list(map(str, command)), 'returncode': child.returncode,
            'stdout': bytes(streams['stdout']), 'stderr': bytes(streams['stderr']),
            'supervisor_failure': failure, 'wall_seconds': time.monotonic() - start,
            'children_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}


class AttemptTests(unittest.TestCase):
    def attempt(self, case='success', fault='none', *, arrangement=None, launched=True, published=True, delivered=True):
        work = RESULTS / (case + '--' + fault + ('--' + arrangement if arrangement else ''))
        work.mkdir()
        for name in ('live', 'sealed', 'barrier'):
            (work / name).mkdir()
        (work / 'live/A').write_bytes(b'A0\n')
        (work / 'live/B').write_bytes(b'B0\n')
        if arrangement == 'missing-a':
            (work / 'live/A').unlink()
        if arrangement == 'oversized-a':
            (work / 'live/A').write_bytes(b'x' * 4097)
        command = ['lake', 'env', 'lean', '--run', str(MAIN), str(work), case, fault, str(FIXTURE)]
        writer = None
        writer_stream = None
        try:
            if case in ('mixed', 'live-input-bug'):
                writer_stream = (work / 'writer.log').open('wb')
                writer = subprocess.Popen(['python3', str(FIXTURE), 'writer', str(work)],
                                          stdout=writer_stream, stderr=writer_stream, start_new_session=True)
                for _ in range(500):
                    if (work / 'barrier/writer-ready').exists():
                        break
                    if writer.poll() is not None:
                        self.fail('writer exited before ready')
                    time.sleep(0.01)
                else:
                    self.fail('writer ready barrier exhausted')
            result = supervised(command, ROOT)
        finally:
            if writer is not None:
                try:
                    writer.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    os.killpg(writer.pid, signal.SIGKILL)
                    writer.wait(timeout=5)
                writer_stream.close()
        for name in ('stdout', 'stderr'):
            (work / ('adapter.' + name)).write_bytes(result[name])
        summary = {key: value for key, value in result.items() if key not in ('stdout', 'stderr')}
        summary['writer_returncode'] = writer.returncode if writer else None
        try:
            received = json.loads(result['stdout'])
            complete = isinstance(received, dict) and received.get('protocol') == 'captured-attempt-v1'
        except (json.JSONDecodeError, UnicodeDecodeError):
            complete = False
        summary['receipt_delivery'] = 'complete-json' if complete else 'unknown'
        summary['selected_success'] = received.get('success') if complete else None
        (work / 'supervisor.json').write_text(json.dumps(summary, indent=2) + '\n')
        self.assertIsNone(result['supervisor_failure'], summary)
        self.assertIn(result['returncode'], (0, 1), result['stderr'].decode(errors='replace'))
        if delivered:
            receipt = json.loads(result['stdout'])
            self.assertEqual(receipt['protocol'], 'captured-attempt-v1')
            self.assertEqual([e['seq'] for e in receipt['events']], list(range(len(receipt['events']))))
            self.assertLessEqual(sum(e['event'] == 'authorize' for e in receipt['events']), 1)
        else:
            with self.assertRaises(json.JSONDecodeError):
                json.loads(result['stdout'])
            receipt = None
        disk = json.loads((work / 'evidence.json').read_text()) if (work / 'evidence.json').is_file() else None
        self.assertEqual(disk is not None, published)
        marker = (work / 'attempt.marker').read_bytes() if (work / 'attempt.marker').exists() else None
        if launched is None:
            self.assertIn(marker, (None, b'attempt\n'))
        else:
            self.assertEqual(marker, b'attempt\n' if launched else None)
        if published:
            self.assertFalse(disk['success'])
            self.assertEqual(disk['publication'], 'unknown')
        if launched and delivered:
            self.assertTrue(receipt['retry_refused'])
        return receipt, disk, result

    def test_success(self):
        receipt, disk, result = self.attempt()
        self.assertEqual(result['returncode'], 0)
        self.assertTrue(receipt['success'])
        self.assertEqual(receipt['captured_a'], [65, 48, 10])
        self.assertEqual(receipt['captured_b'], [66, 48, 10])
        self.assertEqual(receipt['consumed']['sum'], 247)
        self.assertEqual(receipt['publication'], 'confirmed')
        self.assertEqual(receipt['cleanup'], 'confirmed')

    def test_mixed(self):
        receipt, disk, result = self.attempt('mixed')
        self.assertEqual(result['returncode'], 0)
        self.assertTrue(receipt['success'])
        self.assertEqual(receipt['captured_a'], [65, 48, 10])
        self.assertEqual(receipt['captured_b'], [66, 49, 10])
        self.assertEqual(receipt['consumed']['a'], [65, 48, 10])
        self.assertEqual(receipt['consumed']['b'], [66, 49, 10])
        self.assertEqual(receipt['consumed']['sum'], 248)
        work = RESULTS / 'mixed--none'
        self.assertEqual((work / 'live/A').read_bytes(), b'A1\n')
        self.assertEqual((work / 'live/B').read_bytes(), b'B1\n')
        self.assertEqual(json.loads((work / 'writer-history.json').read_text()),
                         [['A0', 'B0'], ['A1', 'B0'], ['A1', 'B1']])

    def test_publication_after_write(self):
        receipt, disk, result = self.attempt('success', 'publication-after-write')
        self.assertEqual(result['returncode'], 1)
        self.assertFalse(receipt['success'])
        self.assertEqual(receipt['completion'], 'exit:0')
        self.assertEqual(receipt['publication'], 'unknown')
        self.assertEqual(receipt['consumed']['sum'], 247)
        self.assertEqual(disk['captured_a'], [65, 48, 10])
        self.assertIn('publication_ack_lost', [e['event'] for e in receipt['events']])
        self.assertEqual(sum(e['event'] == 'authorize' for e in receipt['events']), 1)

    def test_nonzero(self):
        receipt, disk, result = self.attempt('nonzero')
        self.assertEqual(result['returncode'], 1)
        self.assertEqual(receipt['raw_termination'], 7)
        self.assertEqual(receipt['completion'], 'unknown')
        self.assertFalse(receipt['success'])

    def test_signal(self):
        receipt, disk, result = self.attempt('signal')
        self.assertEqual(result['returncode'], 1)
        self.assertNotEqual(receipt['raw_termination'], 0)
        self.assertEqual(receipt['completion'], 'unknown')
        self.assertEqual(receipt['cleanup'], 'confirmed')
        self.assertFalse(receipt['success'])

    def test_incomplete_channels(self):
        for case in ('missing-output', 'stdout-overflow', 'stderr-overflow', 'invalid-output'):
            with self.subTest(case=case):
                receipt, disk, result = self.attempt(case)
                self.assertEqual(result['returncode'], 1)
                self.assertFalse(receipt['output_complete'])
                self.assertFalse(receipt['success'])
                self.assertTrue(receipt['stdout_bytes'])
                expected = {'missing-output': 'read-error', 'stdout-overflow': 'overflow',
                            'stderr-overflow': 'overflow', 'invalid-output': 'invalid-utf8'}
                channel = 'stderr_status' if case in ('missing-output', 'stderr-overflow') else 'stdout_status'
                self.assertEqual(receipt[channel], expected[case])
                if case == 'stdout-overflow':
                    self.assertEqual(len(receipt['stdout_bytes']), 65537)
                if case == 'stderr-overflow':
                    self.assertEqual(len(receipt['stderr_bytes']), 65537)
                if case == 'invalid-output':
                    self.assertEqual(receipt['stdout_bytes'], [255])

    def test_capture_abort(self):
        cases = [('none', 'missing-a', 'read-A'), ('none', 'oversized-a', 'read-A'),
                 ('read-a-denied', None, 'read-A'),
                 ('read-b-error-after-prefix', None, 'read-B'),
                 ('seal-b-error-after-prefix', None, 'seal-B')]
        for fault, arrangement, stage in cases:
            with self.subTest(fault=fault, arrangement=arrangement):
                receipt, disk, result = self.attempt(fault=fault, arrangement=arrangement, launched=False)
                self.assertEqual(result['returncode'], 1)
                self.assertFalse(receipt['success'])
                self.assertEqual(receipt['failure_stage'], stage)
                self.assertNotIn('authorize', [e['event'] for e in receipt['events']])
                if fault == 'read-b-error-after-prefix':
                    self.assertEqual(receipt['captured_b'], [66])
                if fault == 'seal-b-error-after-prefix':
                    work = RESULTS / ('success--' + fault)
                    self.assertEqual((work / 'sealed/B').read_bytes(), b'B')

    def test_poll_budget(self):
        receipt, disk, result = self.attempt('timeout')
        self.assertEqual(result['returncode'], 1)
        self.assertEqual(receipt['completion'], 'timeout')
        self.assertEqual(receipt['cleanup'], 'confirmed')
        self.assertEqual(receipt['stdout_bytes'], list(b'partial:'))
        self.assertFalse(receipt['output_complete'])
        receipt, disk, result = self.attempt('boundary')
        self.assertIn(receipt['completion'], ('timeout', 'exit:0'))
        self.assertEqual(receipt['success'], receipt['completion'] == 'exit:0')
        self.assertEqual(result['returncode'], 0 if receipt['success'] else 1)
        self.assertEqual(receipt['cleanup'], 'confirmed')

    def test_uncertain_process(self):
        for fault in ('poll-error', 'completion-unknown', 'cleanup-unknown', 'cleanup-failed'):
            with self.subTest(fault=fault):
                receipt, disk, result = self.attempt(fault=fault, launched=None if fault == 'poll-error' else True)
                self.assertEqual(result['returncode'], 1)
                self.assertFalse(receipt['success'])
                self.assertTrue(receipt['injection_applied'])
                if fault in ('poll-error', 'completion-unknown'):
                    self.assertEqual(receipt['completion'], 'unknown')
                    self.assertFalse(receipt['output_complete'])
                if fault.startswith('cleanup-'):
                    self.assertEqual(receipt['cleanup'], fault.removeprefix('cleanup-'))
                self.assertTrue(any(e['event'] == 'cleanup_observed' for e in receipt['events']))

    def test_spawn_before_call(self):
        receipt, disk, result = self.attempt(fault='spawn-before-call', launched=False)
        self.assertEqual(result['returncode'], 1)
        self.assertEqual(receipt['completion'], 'spawn-failed')
        self.assertEqual(receipt['cleanup'], 'confirmed')
        self.assertTrue(receipt['retry_refused'])
        self.assertTrue(receipt['injection_applied'])
        self.assertNotIn('spawn_return', [e['event'] for e in receipt['events']])

    def test_publication_failures(self):
        for fault in ('publication-before-write', 'receipt-truncated'):
            with self.subTest(fault=fault):
                receipt, disk, result = self.attempt(fault=fault,
                    published=fault != 'publication-before-write', delivered=fault != 'receipt-truncated')
                if receipt is not None:
                    self.assertEqual(result['returncode'], 1)
                    self.assertFalse(receipt['success'])
                    self.assertEqual(receipt['publication'], 'failed')
                    self.assertTrue(receipt['injection_applied'])
                else:
                    self.assertIsNotNone(disk)
                    self.assertFalse(disk['success'])

    def test_live_input_bug(self):
        receipt, disk, result = self.attempt('live-input-bug')
        self.assertEqual(result['returncode'], 1)
        self.assertEqual(receipt['completion'], 'exit:0')
        self.assertEqual(receipt['captured_a'], [65, 48, 10])
        consumed = json.loads(bytes(receipt['stdout_bytes']))
        self.assertEqual(consumed['a'], [65, 49, 10])
        self.assertEqual(consumed['b'], [66, 49, 10])
        self.assertFalse(receipt['output_complete'])
        self.assertFalse(receipt['success'])

    def test_existing_evidence(self):
        work = RESULTS / 'existing-evidence'
        work.mkdir()
        evidence = work / 'evidence.json'
        evidence.write_bytes(b'earlier evidence\n')
        command = ['lake', 'env', 'lean', '--run', str(MAIN), str(work), 'success', 'none', str(FIXTURE)]
        result = supervised(command, ROOT)
        for name in ('stdout', 'stderr'):
            (work / ('adapter.' + name)).write_bytes(result[name])
        summary = {key: value for key, value in result.items() if key not in ('stdout', 'stderr')}
        (work / 'supervisor.json').write_text(json.dumps(summary, indent=2) + '\n')
        self.assertIsNone(result['supervisor_failure'])
        self.assertEqual(result['returncode'], 2)
        self.assertEqual(evidence.read_bytes(), b'earlier evidence\n')
        self.assertFalse((work / 'attempt.marker').exists())


def main():
    global RESULTS
    parser = argparse.ArgumentParser()
    parser.add_argument('--results-dir', required=True, type=Path)
    parser.add_argument('--only', nargs='+')
    args = parser.parse_args()
    RESULTS = args.results_dir.resolve()
    RESULTS.mkdir(parents=True, exist_ok=False)
    source_paths = [MAIN, FIXTURE, Path(__file__), MAIN.with_name('README.md'),
                    ROOT / 'Applications/Interaction/CapturedAttempt.lean',
                    ROOT / 'Examples/CapturedAttempt.lean', ROOT / 'SquareApplications.lean',
                    ROOT / 'docs/research/captured-attempt-adapter.md', ROOT / 'lean-toolchain',
                    ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json', ROOT / 'flake.lock']
    def source_identity():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in source_paths if p.exists()}
    identities = source_identity()
    (RESULTS / 'source-identity.json').write_text(json.dumps(identities, indent=2) + '\n')
    version = subprocess.run(['lean', '--version'], cwd=ROOT, capture_output=True, check=True, timeout=10)
    environment = {'platform': platform.platform(), 'python': sys.version,
                   'lean': version.stdout.decode().strip(),
                   'cpu_affinity': sorted(os.sched_getaffinity(0)),
                   'local_olean_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted((ROOT / '.lake/build/lib/lean').rglob('*.olean'))},
                   'package_view': str((ROOT / '.lake/packages').resolve())}
    (RESULTS / 'environment.json').write_text(json.dumps(environment, indent=2) + '\n')
    names = ['test_' + name.replace('-', '_') for name in args.only] if args.only else unittest.defaultTestLoader.getTestCaseNames(AttemptTests)
    suite = unittest.TestSuite(AttemptTests(name) for name in names)
    outcome = unittest.TextTestRunner(verbosity=2, failfast=True).run(suite)
    after = source_identity()
    (RESULTS / 'source-identity-after.json').write_text(json.dumps(after, indent=2) + '\n')
    unchanged = identities == after
    (RESULTS / 'result.json').write_text(json.dumps({'passed': outcome.wasSuccessful() and unchanged,
        'tests': outcome.testsRun, 'failures': len(outcome.failures), 'errors': len(outcome.errors),
        'source_unchanged': unchanged}, indent=2) + '\n')
    raise SystemExit(0 if outcome.wasSuccessful() and unchanged else 1)


if __name__ == '__main__':
    main()

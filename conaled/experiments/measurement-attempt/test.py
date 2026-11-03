"""Public CLI fixtures for the bounded measurement experiment (#216)."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MAIN = ROOT / 'experiments/measurement-attempt/Main.lean'
CHILD = MAIN.with_name('child.py')

class AttemptTests(unittest.TestCase):
    def attempt(self, mode='success', fault='none', publish_failure=False):
        with tempfile.TemporaryDirectory(prefix='measurement-216-') as tmp:
            work = Path(tmp)
            source = work / 'live'
            source.write_text('original\n')
            evidence = work / 'evidence.json'
            if publish_failure:
                evidence.mkdir()
            command = ['lake', 'env', 'lean', '--run', str(MAIN), str(work),
                       str(source), str(evidence), mode, fault, str(CHILD)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                    text=True, timeout=30)
            self.assertIn(result.returncode, (0, 1), result.stderr)
            record = json.loads(result.stdout)
            launches = (work / 'executions').read_text().splitlines() if (work / 'executions').exists() else []
            self.assertEqual(launches, [] if mode == 'spawn-failure' or fault == 'spawn-error' else ['attempt'])
            disk = json.loads(evidence.read_text()) if evidence.is_file() else None
            if target := os.environ.get('MEASUREMENT_RESULTS'):
                with Path(target).open('a') as stream:
                    stream.write(json.dumps({'mode': mode, 'fault': fault,
                        'publication_failure': publish_failure,
                        'exit_code': result.returncode, 'receipt': record,
                        'stored_payload': disk, 'executions': launches}) + '\n')
            return result.returncode, record, disk

    def test_success(self):
        code, result, disk = self.attempt()
        self.assertEqual(code, 0)
        self.assertTrue(result['success'])
        self.assertEqual(result['completion'], 'exit:0')
        self.assertEqual(result['output'], 'original\n')
        self.assertEqual(result['publication'], 'confirmed')
        self.assertEqual(disk['publication'], 'unknown')

    def test_nonzero(self):
        code, result, _ = self.attempt('nonzero')
        self.assertEqual(code, 1)
        self.assertFalse(result['success'])
        self.assertEqual(result['completion'], 'exit:7')

    def test_spawn_failure(self):
        code, result, _ = self.attempt('spawn-failure')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'exit:255')
        self.assertFalse(result['output_complete'])

    def test_partial_timeout(self):
        code, result, _ = self.attempt('timeout')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'timeout')
        self.assertEqual(result['output'], 'partial:original\n')
        self.assertFalse(result['output_complete'])
        self.assertEqual(result['cleanup'], 'confirmed')

    def test_publication_failure(self):
        code, result, disk = self.attempt(publish_failure=True)
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'exit:0')
        self.assertEqual(result['publication'], 'failed')
        self.assertFalse(result['success'])
        self.assertIsNone(disk)

    def test_cleanup_observation_faults(self):
        for status in ('failed', 'unknown'):
            with self.subTest(status=status):
                code, result, _ = self.attempt(fault='cleanup-' + status)
                self.assertEqual(code, 1)
                self.assertEqual(result['completion'], 'exit:0')
                self.assertEqual(result['cleanup'], status)
                self.assertFalse(result['success'])
                self.assertEqual(result['injected_fault'], 'cleanup-' + status)

    def test_unknown_completion_boundary(self):
        code, result, _ = self.attempt(fault='completion-unknown')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'unknown')
        self.assertFalse(result['output_complete'])
        self.assertFalse(result['success'])

    def test_capture_survives_live_mutation(self):
        code, result, _ = self.attempt('mutate')
        self.assertEqual(code, 0)
        self.assertEqual(result['output'], 'original\n')
        self.assertEqual(result['captured_bytes'], [111, 114, 105, 103, 105, 110, 97, 108, 10])
        self.assertEqual(result['live_after_capture'], 'changed\n')

    def test_injected_spawn_error(self):
        code, result, _ = self.attempt(fault='spawn-error')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'spawn-failed')
        self.assertEqual(result['output'], '')
        self.assertEqual(result['injected_fault'], 'spawn-error')

    def test_output_overflow_is_incomplete(self):
        code, result, _ = self.attempt('overflow')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'exit:0')
        self.assertFalse(result['output_complete'])
        self.assertEqual(len(result['output']), 4096)

    def test_missing_output_is_incomplete(self):
        code, result, _ = self.attempt('missing-output')
        self.assertEqual(code, 1)
        self.assertEqual(result['completion'], 'exit:0')
        self.assertFalse(result['output_complete'])
        self.assertEqual(result['output'], '')

    def test_real_completion_timeout_boundary(self):
        code, result, _ = self.attempt('boundary')
        self.assertIn(result['completion'], ('exit:0', 'timeout'))
        if result['completion'] == 'timeout':
            self.assertEqual(code, 1)
            self.assertFalse(result['success'])
            self.assertFalse(result['output_complete'])
        else:
            self.assertEqual(code, 0)
            self.assertTrue(result['success'])

if __name__ == '__main__':
    unittest.main()

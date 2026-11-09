#!/usr/bin/env python3
"""Black-box source selection controls; no compilation or historical scripts."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('reproduce.py')

class SelectionTests(unittest.TestCase):
    def invoke(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), '--prepare-only', *map(str, args)],
                              capture_output=True, text=True, timeout=30)

    def test_fresh_selection_and_inverse(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'fresh'
            result = self.invoke('--out', out)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads((out / 'provenance.json').read_text())
            self.assertFalse(receipt['complete'])
            self.assertEqual(len(receipt['selected']), 20)
            self.assertTrue(receipt['inverse_correspondence'])
            self.assertFalse((out / 'output').exists())

    def test_comparison_selects_corrected_proof_and_retains_client_support(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'comparison'
            result = self.invoke('--selection', 'comparison', '--out', out)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads((out / 'provenance.json').read_text())
            self.assertEqual(len(receipt['selected']), 29)
            self.assertTrue(receipt['reflection_correction'])
            self.assertIn('proof-corrections/source/FirstRowReflection.lean',
                          next(r['member'] for r in receipt['selected']
                               if r['module'] == 'FirstRowReflection'))
            self.assertFalse(receipt['complete'])

    def test_native_selection_is_complete_and_source_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'native'
            result = self.invoke('--selection', 'native', '--out', out)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads((out / 'provenance.json').read_text())
            self.assertEqual(len(receipt['selected']), 31)
            self.assertEqual(receipt['selected'][-1]['module'],
                             'FirstRowReflectionRestrictedNatCheckerMain')
            self.assertTrue(receipt['reflection_correction'])
            self.assertTrue(receipt['inverse_correspondence'])
            self.assertFalse(receipt['complete'])
            self.assertFalse((out / 'output').exists())

    def test_native_observer_checks_separate_streams_and_status(self):
        observer = SCRIPT.with_name('native.py')
        cases = [
            ("print('REJECT'); raise SystemExit(1)", 1, 'REJECT\n', True),
            ("print('REJECT')", 1, 'REJECT\n', False),
            ("import sys; print('REJECT', file=sys.stderr); raise SystemExit(1)",
             1, 'REJECT\n', False),
            ("print('ACCEPT wrong')", 0, 'ACCEPT expected\n', False),
        ]
        with tempfile.TemporaryDirectory() as tmp:
            for index, (code, expected_exit, stdout, passed) in enumerate(cases):
                spec = Path(tmp) / f'case{index}.json'
                spec.write_text(json.dumps({'argv': [sys.executable, '-c', code],
                                            'expected_exit': expected_exit,
                                            'expected_stdout': stdout}))
                result = subprocess.run([sys.executable, str(observer), '--observe', str(spec)],
                                        capture_output=True, timeout=10)
                self.assertEqual(result.returncode == 0, passed, result.stderr)
                receipt = json.loads(spec.with_suffix('.result.json').read_text())
                self.assertEqual(receipt['passed'], passed)
                self.assertTrue(spec.with_suffix('.stdout').exists())
                self.assertTrue(spec.with_suffix('.stderr').exists())

    def test_reject_corrupt_archive(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = Path(tmp) / 'bad.zip'
            bad.write_bytes(b'not the pinned preview')
            result = self.invoke('--archive', bad, '--out', Path(tmp) / 'fresh')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Archive hash mismatch', result.stderr)

    def test_refuse_existing_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = self.invoke('--out', tmp)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('exists', result.stderr)

if __name__ == '__main__':
    unittest.main()

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

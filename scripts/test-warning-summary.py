#!/usr/bin/env python3
"""Exercise warning summaries through the public offline CLI."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class WarningSummary(unittest.TestCase):
    def test_lean_and_lake_warnings_are_grouped_and_compared(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = root / 'before.log'
            current = root / 'after.log'
            baseline.write_text('Applications/A.lean:3:2: warning: This simp argument is unused:\n  helper\n')
            current.write_text('\x1b[33mwarning: ./Applications/A.lean:3:2: This simp argument is unused:\x1b[0m\n'
                               '  helper\n'
                               'Applications/A.lean:7:0: warning: automatically included section variable(s) unused in theorem `a`:\n'
                               'warning: SquareKit/B.lean: imports `External` from package `dep`, which is designed for use with the module system\n'
                               'warning: Some new diagnostic without a location\n'
                               'Applications/A.lean:99:0: error: not a warning\n'
                               '✔ Built Applications.A\n')
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/summarize-warnings.py'),
                                     str(current), '--baseline', str(baseline)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(data['warnings'], 4)
            self.assertEqual(data['by_module'], {'Applications.A': 2, 'SquareKit.B': 1, '<unknown>': 1})
            self.assertEqual(data['by_category'], {'unused-simp-argument': 1, 'unused-section-variable': 1,
                                                   'module-import': 1, 'other': 1})
            self.assertEqual(data['comparison']['baseline_warnings'], 1)
            self.assertEqual(data['comparison']['delta'], 3)
            self.assertEqual(sum(x['delta'] for x in data['comparison']['changes']), 3)

    def test_missing_log_fails_and_empty_log_reports_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'log'
            command = [sys.executable, str(ROOT / 'scripts/summarize-warnings.py'), str(path)]
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            path.write_text('Build completed successfully.\n')
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['warnings'], 0)


if __name__ == '__main__':
    unittest.main()

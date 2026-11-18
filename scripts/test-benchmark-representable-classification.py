#!/usr/bin/env python3
"""Real Lean integration test: counted commands must retain their resource limits.

Run in the development shell with the benchmark import closure built.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
WORKSPACE = Path(os.environ.get('REPRESENTABLE_BENCH_WORKSPACE', ROOT))

class BenchmarkTest(unittest.TestCase):
    def test_inner_heartbeat_budget_is_enforced(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / 'result.json'
            subprocess.run([sys.executable, str(ROOT / 'scripts/benchmark-representable-classification.py'),
                            '--workspace', f'test={WORKSPACE}', '--depths', '1',
                            '--budgets', '512:1,512:200000', '--probes', 'nested',
                            '--output', str(output)], check=True)
            rows = json.loads(output.read_text())['results']
            self.assertEqual([r['status'] for r in rows], ['heartbeats', 'pass'])
            self.assertTrue(all(r['heartbeats'] is not None for r in rows))

if __name__ == '__main__':
    unittest.main()

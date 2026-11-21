#!/usr/bin/env python3
"""Real Lean checks for unchanged-file profiling and finite budget enforcement."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('clients', ROOT / 'scripts/benchmark-classification-clients.py')
BENCH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCH)


class ClientMeasurements(unittest.TestCase):
    def test_nested_profiles_are_not_double_counted(self):
        output = ('[Elab.command] [12000.000000] outer\n'
                  '  [Elab.command] [9000.000000] inner\n'
                  '[Elab.command] [3000.000000] second\n')
        self.assertEqual(BENCH.measurements(output), [12000, 3000])

    def test_original_file_and_heartbeat_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Probe.lean'
            path.write_text('import Mathlib.Data.Nat.Basic\nexample : 1 + 1 = 2 := by decide\n')
            before = hashlib.sha256(path.read_bytes()).hexdigest()
            tiny = BENCH.run(ROOT, path, heartbeats=1)
            ordinary = BENCH.run(ROOT, path, heartbeats=200000)
            self.assertEqual(tiny['status'], 'heartbeats', tiny['diagnostics'])
            self.assertEqual(ordinary['status'], 'pass', ordinary['diagnostics'])
            self.assertGreater(ordinary['total_internal_heartbeats'], 1000)
            self.assertEqual(before, hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertNotIn('-DmaxRecDepth=1024', ordinary['command'])


if __name__ == '__main__':
    unittest.main()

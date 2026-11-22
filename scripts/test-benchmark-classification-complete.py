#!/usr/bin/env python3
"""Public measurement seam: real Lean budgets, positions and timeout diagnostics."""
import hashlib
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('complete', ROOT / 'scripts/benchmark-classification-complete.py')
BENCH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BENCH)
WORKSPACE = Path(os.environ.get('CLASSIFICATION_BENCH_WORKSPACE', ROOT))


class CompleteMeasurements(unittest.TestCase):
    def test_budget_positions_and_unchanged_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Probe.lean'
            path.write_text('import Mathlib.Data.Nat.Basic\nexample : 1 + 1 = 2 := by decide\n')
            before = hashlib.sha256(path.read_bytes()).hexdigest()
            tiny = BENCH.run(WORKSPACE, path, 'heartbeats', 512, 30, heartbeats=1)
            ordinary = BENCH.run(WORKSPACE, path, 'heartbeats', 512, 30)
            self.assertEqual(tiny['status'], 'heartbeats', tiny['diagnostics'])
            self.assertEqual(ordinary['status'], 'pass', ordinary['diagnostics'])
            self.assertTrue(ordinary['measurements_complete'])
            self.assertGreater(ordinary['total_internal_heartbeats'], 1000)
            self.assertTrue(any(c['line'] == 2 and 'example' in c['text'] for c in ordinary['commands']))
            self.assertEqual(before, hashlib.sha256(path.read_bytes()).hexdigest())

    def test_timeout_retains_completed_commands(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Slow.lean'
            path.write_text('import Mathlib.Data.Nat.Basic\nexample : 1 + 1 = 2 := by decide\n#eval IO.sleep 10000\n')
            row = BENCH.run(WORKSPACE, path, 'heartbeats', 512, 4)
            self.assertEqual(row['status'], 'timeout', row['diagnostics'])
            self.assertFalse(row['measurements_complete'])
            self.assertTrue(any(c['line'] == 2 for c in row['commands']), row['diagnostics'])
            self.assertGreater(row['total_internal_heartbeats'], 0)

    def test_wall_profile_and_async_control(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Modes.lean'
            path.write_text('import Mathlib.Data.Nat.Basic\nexample : 2 + 2 = 4 := by decide\n')
            wall = BENCH.run(WORKSPACE, path, 'seconds', 512, 30)
            async_row = BENCH.run(WORKSPACE, path, 'async', 512, 30)
            sync = BENCH.run(WORKSPACE, path, 'sync', 512, 30)
            self.assertEqual(wall['status'], 'pass', wall['diagnostics'])
            self.assertGreater(wall['total_command_seconds'], 0)
            self.assertIsNone(wall['total_internal_heartbeats'])
            self.assertEqual(async_row['status'], 'pass', async_row['diagnostics'])
            self.assertEqual(sync['status'], 'pass', sync['diagnostics'])
            self.assertEqual(async_row['commands'], [])
            self.assertFalse(any('Elab.async' in arg for arg in async_row['command']))
            self.assertFalse(any('trace.profiler' in arg for arg in async_row['command']))

    def test_buffering_control(self):
        control = BENCH.buffering_control(WORKSPACE)
        self.assertTrue(control['source_unchanged'])
        self.assertEqual(control['line_buffered']['status'], 'timeout')
        self.assertEqual(control['default_buffering']['status'], 'timeout')
        self.assertGreater(len(control['line_buffered']['commands']), 0)

    def test_scoped_option_counts_outer_command_once(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Scoped.lean'
            path.write_text('import Mathlib.Data.Nat.Basic\nset_option pp.universes true in\nexample : 1 + 1 = 2 := by decide\n')
            row = BENCH.run(WORKSPACE, path, 'heartbeats', 512, 30)
            self.assertEqual(row['status'], 'pass', row['diagnostics'])
            roots = [c for c in row['commands'] if c['line'] in (2, 3)]
            self.assertEqual(len(roots), 1, roots)
            self.assertEqual(roots[0]['line'], 2)
            self.assertGreater(len(row['command_traces']), len(row['commands']))

    def test_inclusive_roots_only(self):
        import json
        output = json.dumps({'pos': {'line': 7, 'column': 0}, 'data':
            '[Elab.command] [12000.000000] outer\n  [Elab.command] [9000.000000] nested'})
        records = BENCH.command_measurements(output, 'heartbeats')
        self.assertEqual([r['internal_heartbeats'] for r in records], [12000])


if __name__ == '__main__':
    unittest.main()

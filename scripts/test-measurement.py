#!/usr/bin/env python3
"""Public process/evidence and CLI regression tests; no Lean build required."""
import json
import warnings
import os
import shutil
import subprocess
from unittest.mock import patch
from pathlib import Path
import sys
import tempfile
import unittest

from measurement import Limits, run_attempt, source_identity


class Attempts(unittest.TestCase):
    def test_success_retains_command_output_and_publication_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory) / 'one'
            command = [sys.executable, '-c', 'print("observed")']
            result = run_attempt(command, cwd=directory, prefix=prefix, limits=Limits(wall=2))
            self.assertEqual(result['status'], 'exited')
            self.assertEqual(result['returncode'], 0)
            self.assertEqual(result['stdout'], 'observed\n')
            self.assertEqual(result['command'], command)
            self.assertEqual(result['publication'], 'confirmed')
            self.assertTrue(result['success'])
            stored = json.loads(prefix.with_suffix('.meta.json').read_text())
            self.assertEqual(stored['publication'], 'unknown')
            self.assertFalse(stored['success'])
            self.assertEqual(stored['returncode'], 0)

    def test_timeout_retains_partial_output_without_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'executions'
            command = [sys.executable, '-c',
                       f'from pathlib import Path; import time; Path({str(marker)!r}).open("a").write("x"); print("prefix", flush=True); time.sleep(.3)']
            result = run_attempt(command, cwd=directory, prefix=Path(directory)/'one',
                                 limits=Limits(wall=.1))
            self.assertEqual(result['status'], 'timeout')
            self.assertEqual(result['stdout'], 'prefix\n')
            self.assertEqual(result['cleanup'], 'confirmed')
            self.assertFalse(result['success'])
            self.assertEqual(marker.read_text(), 'x')

    def test_unsuccessful_process_observations_are_distinct(self):
        cases = [([sys.executable, '-c', 'raise SystemExit(7)'], 'nonzero', 7),
                 ([sys.executable, '-c', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)'], 'signal', -15),
                 (['/does/not/exist/measurement-child'], 'spawn_failed', None)]
        with tempfile.TemporaryDirectory() as directory:
            for index, (command, status, code) in enumerate(cases):
                with self.subTest(status=status):
                    result = run_attempt(command, cwd=directory,
                                         prefix=Path(directory)/str(index), limits=Limits(wall=2))
                    self.assertEqual(result['status'], status)
                    self.assertEqual(result['returncode'], code)
                    self.assertEqual(result['publication'], 'confirmed')
                    self.assertFalse(result['success'])

    def test_output_failure_never_becomes_a_success(self):
        for source, expected in [('import os; os.write(1,b"x"*2048)', 'overflow'),
                                 ('import os; os.write(1,bytes([255]))', 'invalid_utf8')]:
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as directory:
                result = run_attempt([sys.executable, '-c', source], cwd=directory,
                                     prefix=Path(directory)/'one', limits=Limits(output_bytes=1024))
                self.assertEqual(result['output'], expected)
                self.assertFalse(result['success'])
                self.assertLessEqual((Path(directory)/'one.stdout').stat().st_size, 1024)

    def test_log_creation_failure_preserves_existing_bytes_and_records_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory)/'one'
            (Path(directory)/'one.stdout').write_text('old evidence')
            result = run_attempt([sys.executable, '-c', 'raise AssertionError("must not run")'],
                                 cwd=directory, prefix=prefix, limits=Limits())
            self.assertEqual(result['status'], 'recording_failed')
            self.assertFalse(result['success'])
            self.assertEqual((Path(directory)/'one.stdout').read_text(), 'old evidence')

    def test_failed_final_publication_cannot_retry_or_claim_success(self):
        with tempfile.TemporaryDirectory() as directory:
            source = ('from pathlib import Path; Path("executions").open("a").write("x"); '
                      'Path("one.meta.json").unlink(); Path("one.meta.json").mkdir()')
            result = run_attempt([sys.executable, '-c', source], cwd=directory,
                                 prefix=Path(directory)/'one', limits=Limits())
            self.assertEqual(result['publication'], 'failed')
            self.assertFalse(result['success'])
            self.assertEqual((Path(directory)/'executions').read_text(), 'x')

    def test_interruption_is_recorded_and_child_reaped(self):
        original = os.wait4
        first = True
        def interrupted(pid, options):
            nonlocal first
            if first:
                first = False
                raise KeyboardInterrupt()
            return original(pid, options)
        with tempfile.TemporaryDirectory() as directory, patch('os.wait4', interrupted):
            result = run_attempt([sys.executable, '-c', 'import time; time.sleep(.3)'],
                                 cwd=directory, prefix=Path(directory)/'one', limits=Limits(),
                                 metadata={'injected_fault': 'wait interruption'})
            self.assertEqual(result['status'], 'interrupted')
            self.assertEqual(result['cleanup'], 'confirmed')
            self.assertFalse(result['success'])

    def test_unknown_cleanup_stays_unknown_after_observation_budget(self):
        pids = []
        def unavailable(pid, options):
            pids.append(pid)
            return 0, 0, None
        with tempfile.TemporaryDirectory() as directory:
            try:
                with warnings.catch_warnings(), patch('os.wait4', unavailable):
                    warnings.simplefilter('ignore', ResourceWarning)
                    result = run_attempt([sys.executable, '-c', 'import time; time.sleep(.3)'],
                                         cwd=directory, prefix=Path(directory)/'one',
                                         limits=Limits(wall=.03, cleanup=.03),
                                         metadata={'injected_fault': 'wait observation unavailable'})
                self.assertEqual(result['status'], 'timeout')
                self.assertEqual(result['cleanup'], 'unknown')
                self.assertEqual(result['output'], 'incomplete')
                self.assertFalse(result['success'])
            finally:
                if pids:
                    try:
                        os.waitpid(pids[0], 0)
                    except ChildProcessError:
                        pass

    def test_initial_record_failure_never_launches_or_overwrites(self):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory)/'one.meta.json').write_text('retained')
            result = run_attempt([sys.executable, '-c', 'open("executed","w").close()'],
                                 cwd=directory, prefix=Path(directory)/'one', limits=Limits())
            self.assertEqual(result['publication'], 'failed')
            self.assertFalse((Path(directory)/'executed').exists())
            self.assertEqual((Path(directory)/'one.meta.json').read_text(), 'retained')

    def test_source_identity_detects_changed_bytes_and_missing_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'input').write_bytes(b'original')
            original = source_identity(root, ['input'])
            (root/'input').write_bytes(b'changed')
            self.assertNotEqual(source_identity(root, ['input']), original)
            (root/'input').unlink()
            with self.assertRaises(FileNotFoundError):
                source_identity(root, ['input'])

    def test_invalid_limits_cannot_disable_the_observation_budget(self):
        for limits in ({'wall': float('nan')}, {'wall': float('inf')}, {'cleanup': -1},
                       {'cpu': (3, 2)}, {'output_bytes': 0}, {'address_space': -1}):
            with self.subTest(limits=limits), self.assertRaises(ValueError):
                Limits(**limits)


class PublicClients(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        repository = Path(__file__).resolve().parents[1]
        for name in ['scripts/measurement.py', 'scripts/project_sources.py',
                     'scripts/benchmark-order-certificate.py', 'scripts/probes/run-disk-feasibility.py',
                     'scripts/probes/DiskDriverFeasibility.lean', 'scripts/lean-source-info.lean',
                     'ProofAudit.lean', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'flake.lock']:
            target = root/name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(repository/name, target)
        (root/'bin').mkdir()
        lake = root/'bin/lake'
        lake.write_text('#!' + sys.executable + '\n' +
                        'import os,sys\n'
                        'if "--version" in sys.argv: print("Lean (version 4.35.0, fixture)")\n'
                        'else:\n'
                        ' sys.stdout.write(os.environ["PROBE_OUTPUT"])\n'
                        ' if os.environ.get("MUTATE_SOURCE"): open("lean-toolchain","a").write("changed")\n'
                        ' sys.exit(int(os.environ.get("PROBE_EXIT","0")))\n')
        lake.chmod(0o755)
        return root, dict(os.environ, PATH=str(root/'bin')+os.pathsep+os.environ['PATH'])

    def test_numerical_cli_distinguishes_domain_result_from_process_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            env['PROBE_OUTPUT'] = 'event=whole success=true attempts=1 accepted=1 rejected=0 num_bits=47 den_bits=48 error="39/1048576" meets_tolerance=false elapsed_ns=123'
            command = [sys.executable, str(root/'scripts/probes/run-disk-feasibility.py'),
                       str(root/'output'), 'one', 'move', '1', '1', '1024', '32768', '16384', 'whole']
            result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(result.stdout)
            self.assertEqual(receipt['numerical']['outcome'], 'misses_tolerance')
            self.assertEqual(receipt['numerical']['events'][0]['elapsed_ns'], '123')
            self.assertIn('scripts/probes/DiskDriverFeasibility.lean', receipt['sources'])
            retained = (root/'output/one.meta.json').read_bytes()
            again = subprocess.run(command, env=env, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(again.returncode, 0)
            self.assertEqual((root/'output/one.meta.json').read_bytes(), retained)

    def test_benchmark_cli_uses_native_imports_and_keeps_private_audit_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            (root/'Examples').mkdir()
            (root/'Examples/OrderCertificate.lean').write_text('import Foundation\n')
            (root/'Foundation.lean').write_text('-- fixture\n')
            lean = root/'bin/lean'
            lean.write_text('#!' + sys.executable + '\n' +
                'import json,os,sys\nfrom pathlib import Path\n'
                'a=sys.argv[1:]\n'
                'if "--version" in a: print("Lean (version 4.35.0, fixture)")\n'
                'elif "scripts/lean-source-info.lean" in a:\n'
                ' names=json.loads(Path(a[-1]).read_text()); print(json.dumps([["Foundation"] if n=="Examples/OrderCertificate.lean" else [] for n in names]))\n'
                'elif a[-1]=="ProofAudit.lean":\n'
                ' assert Path("scripts/project_sources.py").is_file(), "audit inventory missing"\n'
                'elif a[-1]=="Runtime.lean":\n'
                ' if os.environ.get("BAD_RUNTIME"): sys.exit(0)\n'
                ' for n in [64,256,1024]:\n'
                '  for alg in ["reference","adjacent"]: print(f"{alg} n={n} repeats=20 accepted=20 ns=123")\n')
            lean.chmod(0o755)
            (root/'bin/lake').write_text('#!' + sys.executable + '\nprint("/fixture/dependencies")\n')
            result = subprocess.run([sys.executable, str(root/'scripts/benchmark-order-certificate.py')],
                                    env=env, capture_output=True, text=True, timeout=8)
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            records = list((root/'.lake').glob('order-certificate-*/results.json'))
            self.assertEqual(len(records), 1)
            record = json.loads(records[0].read_text())
            self.assertEqual(record['status'], 'exited')
            self.assertIn('Runtime.lean', record['sources'])
            self.assertIn('ProofAudit.lean', record['sources'])
            phases = {row['phase'] for row in record['runs']}
            self.assertTrue({'build', 'kernel checking', 'audit', 'execution'} <= phases)
            self.assertEqual(len(record['measurements']), 6)
            broken = subprocess.run([sys.executable, str(root/'scripts/benchmark-order-certificate.py')],
                                    env=dict(env, BAD_RUNTIME='1'), capture_output=True, text=True, timeout=8)
            self.assertNotEqual(broken.returncode, 0)
            failed = json.loads(broken.stderr)
            self.assertEqual(failed['status'], 'malformed_output')
            self.assertFalse(failed['success'])

    def test_numerical_cli_rejects_malformed_complete_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            env['PROBE_OUTPUT'] = ('event=step index=1 num_bits=47 den_bits=48 error=39/1048576 clock=1/1024 step_ns=1\n'
                                   'event=complete accepted=1 error=39/1048576 clock=null meets_tolerance=false elapsed_ns=2')
            result = subprocess.run([sys.executable, str(root/'scripts/probes/run-disk-feasibility.py'),
                                     str(root/'output'), 'bad', 'move', '1', '1', '1024', '32768', '16384', 'steps'],
                                    env=env, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(json.loads(result.stdout)['status'], 'malformed_output')

    def test_numerical_cli_keeps_rejection_cutoff_and_missing_output_distinct(self):
        cases = [
            ('event=whole success=false attempts=1 accepted=0 rejected=1 num_bits=1 den_bits=2 error=null meets_tolerance=false elapsed_ns=3', 'whole', '0', 'checked_rejection', 0),
            ('event=bit_cutoff accepted=0 num_bits=20000 den_bits=20001', 'steps', '3', 'bit_cutoff', 1),
            ('', 'whole', '0', None, 1),
            ('event=whole success=true attempts=1 accepted=1 rejected=0 num_bits=47 den_bits=48 error="39/1048576" meets_tolerance=false elapsed_ns=3', 'whole', '7', None, 1),
        ]
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            for index, (output, mode, child_exit, outcome, cli_exit) in enumerate(cases):
                with self.subTest(outcome=outcome, child_exit=child_exit):
                    env.update(PROBE_OUTPUT=output, PROBE_EXIT=child_exit)
                    result = subprocess.run([sys.executable, str(root/'scripts/probes/run-disk-feasibility.py'),
                                             str(root/'output'), str(index), 'move', '1', '1', '1024', '32768', '16384', mode],
                                            env=env, capture_output=True, text=True, timeout=5)
                    self.assertEqual(result.returncode, cli_exit, result.stderr)
                    receipt = json.loads(result.stdout)
                    if outcome:
                        self.assertEqual(receipt['numerical']['outcome'], outcome)
                    else:
                        self.assertEqual(receipt['status'], 'malformed_output')

    def test_numerical_cli_marks_source_change_as_failed_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            env.update(PROBE_OUTPUT='event=whole success=true attempts=1 accepted=1 rejected=0 num_bits=47 den_bits=48 error="39/1048576" meets_tolerance=false elapsed_ns=3', MUTATE_SOURCE='1')
            result = subprocess.run([sys.executable, str(root/'scripts/probes/run-disk-feasibility.py'),
                                     str(root/'output'), 'changed', 'move', '1', '1', '1024', '32768', '16384', 'whole'],
                                    cwd=root, env=env, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(result.stdout)['status'], 'input_changed')

    def test_benchmark_cli_retains_native_preflight_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            lean = root/'bin/lean'
            lean.write_text('#!' + sys.executable + '\nimport sys\n'
                            'if "--version" in sys.argv: print("Lean (version 4.35.0, fixture)")\n'
                            'else: print("rejected source policy"); sys.exit(2)\n')
            lean.chmod(0o755)
            result = subprocess.run([sys.executable, str(root/'scripts/benchmark-order-certificate.py')],
                                    env=env, capture_output=True, text=True, timeout=5)
            self.assertNotEqual(result.returncode, 0)
            record = json.loads(next((root/'.lake').glob('order-certificate-*/results.json')).read_text())
            self.assertEqual(record['status'], 'failed')
            self.assertEqual(record['runs'][-1]['phase'], 'source preflight')
            self.assertEqual(record['runs'][-1]['status'], 'nonzero')

    def test_numerical_cli_accepts_retained_checkpoint_protocol(self):
        evidence = Path(__file__).resolve().parents[1]/'docs/research/numerical-driver-checkpoint'
        outcomes = {'baseline-move': 'misses_tolerance', 'baseline-turn': 'misses_tolerance',
                    'domain-reject': 'checked_rejection', 'long-move16': 'bit_cutoff',
                    'word-refine8': 'bit_cutoff'}
        with tempfile.TemporaryDirectory() as directory:
            root, env = self.fixture(directory)
            for meta_path in sorted(evidence.glob('*.meta.json')):
                name = meta_path.name.removesuffix('.meta.json')
                if name.startswith('smoke'):
                    continue  # Historical setup errors are not numerical observations.
                with self.subTest(name=name):
                    meta = json.loads(meta_path.read_text())
                    args = meta['recorded_command_sanitized'][-7:]
                    env.update(PROBE_OUTPUT=(evidence/(name+'.stdout')).read_text(),
                               PROBE_EXIT=str(meta['returncode']))
                    result = subprocess.run([sys.executable, str(root/'scripts/probes/run-disk-feasibility.py'),
                                             str(root/'output'), name, *args],
                                            env=env, capture_output=True, text=True, timeout=5)
                    self.assertEqual(result.returncode, 1 if meta['returncode'] else 0, result.stderr)
                    receipt = json.loads(result.stdout)
                    self.assertEqual(receipt.get('numerical', {}).get('outcome'),
                                     outcomes.get(name, 'meets_tolerance'), receipt.get('output_error', receipt['status']))


if __name__ == '__main__':
    unittest.main()

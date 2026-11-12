"""Administrative tests through the recorder and release command interfaces."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent


class RecorderTests(unittest.TestCase):
    def test_failed_check_is_snapshotted_and_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'draft.lean'
            source.write_text('example : True := True.intro\n')
            context = root / 'context.json'
            context.write_text(json.dumps({'slot': 'slot-1', 'session': 'synthetic',
                'route': 'direct', 'phase': 'initial', 'release_sha256': 'a' * 64,
                'environment_sha256': 'b' * 64}))
            attempt = root / 'Attempt01'
            command = [sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(source), '--attempt', str(attempt), '--cwd', tmp,
                '--context', str(context), '--', sys.executable, '-c',
                'import pathlib,sys; print(pathlib.Path(sys.argv[1]).read_text()); sys.exit(7)',
                '{source}']
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 7, result.stderr)
            receipt = json.loads((attempt / 'result.json').read_text())
            self.assertEqual(receipt['exit_code'], 7)
            self.assertEqual(receipt['status'], 'check-failed')
            self.assertEqual((attempt / 'source.lean').read_bytes(), source.read_bytes())
            self.assertIn('True.intro', (attempt / 'output.log').read_text())
            self.assertIsNone(receipt['observations']['active_reasoning_seconds'])
            self.assertGreaterEqual(receipt['finish_monotonic_ns'], receipt['start_monotonic_ns'])
            old = (attempt / 'result.json').read_bytes()
            source.write_text('changed\n')
            repeat = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(repeat.returncode, 0)
            self.assertEqual((attempt / 'result.json').read_bytes(), old)
            self.assertNotEqual((attempt / 'source.lean').read_bytes(), source.read_bytes())


    def test_missing_executable_retains_a_final_failure_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'draft.lean').write_text('synthetic source')
            (root / 'context.json').write_text(json.dumps({'slot': 'slot-2',
                'session': 'synthetic', 'route': 'service', 'phase': 'scale',
                'release_sha256': 'a' * 64, 'environment_sha256': 'b' * 64}))
            result = subprocess.run([sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(root / 'draft.lean'), '--attempt', str(root / 'Attempt01'),
                '--cwd', tmp, '--context', str(root / 'context.json'), '--',
                str(root / 'missing-command'), '{source}'], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            receipt = json.loads((root / 'Attempt01/result.json').read_text())
            self.assertEqual(receipt['status'], 'environment-failed')
            self.assertIsNone(receipt['exit_code'])
            self.assertIn('No such file', receipt['error'])


    def test_interrupted_check_keeps_partial_output_and_receipt(self):
        import signal
        import time
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'draft.lean').write_text('synthetic')
            (root / 'context.json').write_text(json.dumps({'slot': 'slot-1',
                'session': 'synthetic', 'route': 'direct', 'phase': 'initial',
                'release_sha256': 'a' * 64, 'environment_sha256': 'b' * 64}))
            proc = subprocess.Popen([sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(root / 'draft.lean'), '--attempt', str(root / 'Attempt01'),
                '--cwd', tmp, '--context', str(root / 'context.json'), '--', sys.executable,
                '-c', 'import time; print("ready", flush=True); time.sleep(30)', '{source}'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                deadline = time.monotonic() + 5
                log = root / 'Attempt01/output.log'
                while not (log.exists() and 'ready' in log.read_text()):
                    if time.monotonic() > deadline:
                        self.fail('synthetic check did not start')
                    time.sleep(0.01)
                proc.send_signal(signal.SIGTERM)
                proc.communicate(timeout=5)
                receipt = json.loads((root / 'Attempt01/result.json').read_text())
                self.assertEqual(receipt['status'], 'interrupted')
                self.assertIn('ready', log.read_text())
                self.assertEqual(receipt['observations']['interruptions'][0]['signal'], signal.SIGTERM)
            finally:
                if proc.poll() is None:
                    proc.kill()
                    proc.communicate()


    def test_interruption_stops_descendant_after_leader_exits(self):
        import os
        import signal
        import time
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'draft.lean').write_text('synthetic')
            (root / 'context.json').write_text(json.dumps({'slot': 'slot-1',
                'session': 'synthetic', 'route': 'direct', 'phase': 'initial',
                'release_sha256': 'a' * 64, 'environment_sha256': 'b' * 64}))
            # A real same-group descendant keeps writing and ignores SIGTERM.
            (root / 'child.py').write_text(
                'import os, pathlib, signal, time\n'
                'signal.signal(signal.SIGTERM, signal.SIG_IGN)\n'
                'pathlib.Path("descendant.pid").write_text(str(os.getpid()))\n'
                'while True:\n'
                ' print("heartbeat", flush=True)\n'
                ' time.sleep(0.02)\n')
            leader = ('import os,pathlib,subprocess,sys,time; '
                      'pathlib.Path("group.pid").write_text(str(os.getpid())); '
                      'subprocess.Popen([sys.executable,"child.py"]); time.sleep(30)')
            proc = subprocess.Popen([sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(root / 'draft.lean'), '--attempt', str(root / 'Attempt01'),
                '--cwd', tmp, '--context', str(root / 'context.json'), '--',
                sys.executable, '-c', leader, '{source}'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                log = root / 'Attempt01/output.log'
                deadline = time.monotonic() + 5
                while not (log.exists() and 'heartbeat' in log.read_text()):
                    if time.monotonic() > deadline:
                        self.fail('descendant did not start')
                    time.sleep(0.01)
                proc.send_signal(signal.SIGTERM)
                proc.communicate(timeout=7)
                receipt = json.loads((root / 'Attempt01/result.json').read_text())
                self.assertEqual(proc.returncode, 130)
                self.assertEqual(receipt['status'], 'interrupted')
                self.assertEqual(receipt['exit_code'], -signal.SIGTERM)
                final_output = log.read_bytes()
                self.assertIn(b'heartbeat', final_output)
                time.sleep(0.15)
                self.assertEqual(log.read_bytes(), final_output,
                                 'descendant wrote after the final receipt')
                pid = int((root / 'descendant.pid').read_text())
                stat = Path(f'/proc/{pid}/stat')
                if stat.exists():
                    self.assertEqual(stat.read_text().rsplit(')', 1)[1].split()[0], 'Z')
                self.assertEqual(receipt['output_sha256'],
                                 hashlib.sha256(final_output).hexdigest())
            finally:
                if (root / 'group.pid').exists():
                    try:
                        os.killpg(int((root / 'group.pid').read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if proc.poll() is None:
                    proc.kill()
                proc.communicate(timeout=5)


    def test_cleanup_os_error_retains_unconfirmed_final_observation(self):
        import os
        import signal
        import time
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'draft.lean').write_text('synthetic')
            (root / 'context.json').write_text(json.dumps({'slot': 'slot-1',
                'session': 'synthetic', 'route': 'direct', 'phase': 'initial',
                'release_sha256': 'a' * 64, 'environment_sha256': 'b' * 64}))
            # Inject a failure at the external OS boundary in a fresh CLI process.
            # The test process retains the real killpg for unconditional cleanup.
            (root / 'sitecustomize.py').write_text(
                'import os\n'
                'def denied(group, sig):\n'
                ' raise PermissionError("synthetic OS killpg denial")\n'
                'os.killpg = denied\n')
            env = os.environ.copy()
            env['PYTHONPATH'] = tmp
            leader = ('import os,pathlib,time; '
                      'pathlib.Path("group.pid").write_text(str(os.getpid())); '
                      'print("ready",flush=True); time.sleep(30)')
            proc = subprocess.Popen([sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(root / 'draft.lean'), '--attempt', str(root / 'Attempt01'),
                '--cwd', tmp, '--context', str(root / 'context.json'), '--',
                sys.executable, '-c', leader, '{source}'], env=env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                log = root / 'Attempt01/output.log'
                deadline = time.monotonic() + 5
                while not (log.exists() and 'ready' in log.read_text()):
                    if time.monotonic() > deadline:
                        self.fail('synthetic check did not start')
                    time.sleep(0.01)
                proc.send_signal(signal.SIGTERM)
                proc.communicate(timeout=7)
                receipt = json.loads((root / 'Attempt01/result.json').read_text())
                self.assertEqual(proc.returncode, 130)
                self.assertEqual(receipt['status'], 'interrupted')
                cleanup = receipt['observations']['cleanup']
                self.assertEqual(cleanup['status'], 'cleanup-failed')
                self.assertTrue(any('synthetic OS killpg denial' in error
                                    for error in cleanup['errors']))
                self.assertIsNone(receipt['exit_code'])
                self.assertIn('ready', log.read_text())
                self.assertTrue((root / 'Attempt01/started.json').exists())
                self.assertEqual((root / 'Attempt01/source.lean').read_text(), 'synthetic')
            finally:
                if (root / 'group.pid').exists():
                    try:
                        os.killpg(int((root / 'group.pid').read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if proc.poll() is None:
                    proc.kill()
                proc.communicate(timeout=5)


    def test_native_policy_receives_snapshot_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'draft.lean').write_text('original')
            (root / 'context.json').write_text(json.dumps({'slot': 'slot-1',
                'session': 'synthetic', 'route': 'direct', 'phase': 'initial',
                'release_sha256': 'a' * 64, 'environment_sha256': 'b' * 64}))
            result = subprocess.run([sys.executable, str(HERE / 'record_attempt.py'),
                '--source', str(root / 'draft.lean'), '--attempt', str(root / 'Policy01'),
                '--cwd', tmp, '--context', str(root / 'context.json'), '--', sys.executable,
                '-c', 'import json,pathlib,sys; print(pathlib.Path(json.load(open(sys.argv[1]))[0]).read_text())',
                '{sources}'], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / 'Policy01/output.log').read_text(), 'original\n')


class BundleTests(unittest.TestCase):
    def test_six_copy_only_trees_withhold_future_tasks_and_direct_converter(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = root / 'repo'
            repo.mkdir()
            inputs = {'SquareKit/Internal/DependentFunctions.lean': 'generic\n',
                'SquareKit/Internal/DependentFunctionConversion.lean': 'service\n',
                'fixtures/Initial.lean': 'initial\n',
                'fixtures/Repair.lean': 'before\nchange\n',
                'direct.md': 'direct instructions\n', 'service.md': 'service instructions\n'}
            for name, content in inputs.items():
                path = repo / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            freeze = {'seed': 'synthetic-seed', 'source_files':
                {name: hashlib.sha256(content.encode()).hexdigest() for name, content in inputs.items()},
                'routes': {'direct': ['SquareKit/Internal/DependentFunctions.lean'],
                    'service': ['SquareKit/Internal/DependentFunctions.lean',
                        'SquareKit/Internal/DependentFunctionConversion.lean']},
                'instructions': {'direct': 'direct.md', 'service': 'service.md'},
                'common_files': [],
                'phases': {'initial': [{'source': 'fixtures/Initial.lean',
                    'destination': 'Examples/ConversionTrial/Initial.lean'}],
                    'repair-baseline': [{'source': 'fixtures/Repair.lean',
                    'destination': 'Examples/ConversionTrial/Repair.lean', 'lines': [[1, 1]]}],
                    'repair-change': [{'source': 'fixtures/Repair.lean',
                    'destination': 'Examples/ConversionTrial/Repair.lean'}]}}
            config = root / 'freeze.json'
            config.write_text(json.dumps(freeze))
            output = root / 'prepared'
            result = subprocess.run([sys.executable, str(HERE / 'prepare_bundles.py'),
                '--repo', str(repo), '--freeze', str(config), '--output', str(output)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            manifest = json.loads((output / 'prepared.json').read_text())
            self.assertEqual(len(manifest['slots']), 6)
            self.assertEqual([s['route'] for s in manifest['slots']].count('direct'), 3)
            for slot in manifest['slots']:
                public = output / 'slots' / slot['id'] / 'public'
                self.assertTrue((public / 'Examples/ConversionTrial/Initial.lean').is_file())
                self.assertFalse((public / 'Examples/ConversionTrial/Repair.lean').exists())
                self.assertEqual((public / 'SquareKit/Internal/DependentFunctionConversion.lean').exists(),
                                 slot['route'] == 'service')
                self.assertFalse(any(p.is_symlink() for p in public.rglob('*')))
            baseline = output / 'sealed/repair-baseline/Examples/ConversionTrial/Repair.lean'
            self.assertEqual(baseline.read_text(), 'before\n')
            self.assertEqual((output / 'sealed/repair-change/Examples/ConversionTrial/Repair.lean').read_text(),
                             'before\nchange\n')
            old = (output / 'prepared.json').read_bytes()
            repeat = subprocess.run([sys.executable, str(HERE / 'prepare_bundles.py'),
                '--repo', str(repo), '--freeze', str(config), '--output', str(output)], capture_output=True)
            self.assertNotEqual(repeat.returncode, 0)
            self.assertEqual((output / 'prepared.json').read_bytes(), old)


    def test_direct_converter_and_private_source_are_refused_before_copy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for forbidden in ['SquareKit/Internal/DependentFunctionConversion.lean',
                              'private/DirectReference.lean']:
                with self.subTest(forbidden=forbidden):
                    path = root / forbidden
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('synthetic')
                    config = root / 'freeze.json'
                    config.write_text(json.dumps({'seed': 's', 'source_files':
                        {forbidden: hashlib.sha256(b'synthetic').hexdigest()},
                        'routes': {'direct': [forbidden], 'service': []},
                        'instructions': {}, 'common_files': [], 'phases': {'initial': []}}))
                    output = root / 'output'
                    result = subprocess.run([sys.executable, str(HERE / 'prepare_bundles.py'),
                        '--repo', str(root), '--freeze', str(config), '--output', str(output)],
                        capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertFalse(output.exists(), result.stderr)


    def test_changed_or_symlinked_frozen_source_never_creates_release(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'source.lean'
            source.write_text('changed')
            freeze = root / 'freeze.json'
            freeze.write_text(json.dumps({'source_files':
                {'source.lean': hashlib.sha256(b'expected').hexdigest()}}))
            command = [sys.executable, str(HERE / 'prepare_bundles.py'), '--repo', tmp,
                       '--freeze', str(freeze), '--output', str(root / 'public')]
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            self.assertFalse((root / 'public').exists())
            source.unlink()
            (root / 'target.lean').write_text('expected')
            source.symlink_to(root / 'target.lean')
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            self.assertFalse((root / 'public').exists())


if __name__ == '__main__':
    unittest.main()

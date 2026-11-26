#!/usr/bin/env python3
"""Black-box controls for the isolated acceptance audit and runner."""
from pathlib import Path
import os
import json
import importlib.util
import time
import subprocess
import shutil
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
LEAN = subprocess.check_output(['elan', 'which', 'lean'], cwd=HERE, text=True).strip()


class AcceptanceControls(unittest.TestCase):
    def plan_fixture(self, source, *, broken_helper=False):
        with tempfile.TemporaryDirectory(prefix='source-preflight-control-') as tmp:
            root = Path(tmp)
            paths = ['lean-toolchain', 'scripts/check.py', 'scripts/lake_integrity.py',
                     'scripts/project_sources.py', 'scripts/verification_status.py',
                     'scripts/LeanSourceInfo.lean',
                     'experiments/relative-graph/reproduce-acceptance.py']
            for relative in paths:
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(HERE.parents[1] / relative, target)
            (root / 'Dep.lean').write_text('def dep : Nat := 7\n')
            (root / 'experiments/relative-graph/Main.lean').write_text(source)
            if broken_helper:
                (root / 'scripts/LeanSourceInfo.lean').write_text('def broken : Nat := false\n')
            return subprocess.run([sys.executable,
                str(root / 'experiments/relative-graph/reproduce-acceptance.py'), '--plan'],
                cwd='/', capture_output=True, text=True, timeout=30)

    def test_native_header_and_literal_handling(self):
        result = self.plan_fixture('module\npublic import\n /- nested /- import Missing -/ -/ Dep\n'
            'def text := r#"axiom sorry unsafe import Missing"#\n')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        plan = json.loads(result.stdout)
        self.assertEqual(plan['native'], ['Dep'])
        self.assertEqual(plan['graph'], ['Main'])

    def test_native_policy_and_header_fail_closed(self):
        for source, diagnostic in [
            ('axiom forbidden : False\n', 'Forbidden source construct'),
            ('/-! module documentation -/\nimport Dep\n', 'imports must precede commands'),
            ('import (\n', 'Invalid Lean module header'),
        ]:
            with self.subTest(source=source):
                result = self.plan_fixture(source)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stdout + result.stderr)
                self.assertNotIn('"graph"', result.stdout)

    def test_native_helper_failure_cannot_produce_plan(self):
        result = self.plan_fixture('import Dep\n', broken_helper=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('"graph"', result.stdout)

    def test_native_implicit_and_explicit_init_imports(self):
        spec = importlib.util.spec_from_file_location('acceptance_runner', HERE / 'reproduce-acceptance.py')
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        with tempfile.TemporaryDirectory() as tmp:
            paths = [Path(tmp) / f'Case{i}.lean' for i in range(3)]
            for path, source in zip(paths, ['import Lean\n',
                    'prelude\nimport Lean\n', 'import Init\nimport Lean\n'], strict=True):
                path.write_text(source)
            self.assertEqual(runner.source_imports(paths),
                [['Init', 'Init', 'Lean'], ['Lean'], ['Init', 'Init', 'Init', 'Lean']])

    def test_command_deadline_applies_after_output_closes(self):
        spec = importlib.util.spec_from_file_location('acceptance_runner', HERE / 'reproduce-acceptance.py')
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        with tempfile.TemporaryDirectory() as tmp:
            commands = runner.Commands(Path(tmp) / 'logs', dict(os.environ))
            start = time.monotonic()
            with self.assertRaisesRegex(RuntimeError, 'timeout'):
                commands.run('closed-output', [sys.executable, '-c',
                    'import os,time; os.close(1); os.close(2); time.sleep(2)'],
                    cwd=Path(tmp), timeout=0.1)
            self.assertLess(time.monotonic() - start, 1.5)

    def test_plan_includes_actual_emission_and_native_dependencies(self):
        result = subprocess.run([sys.executable, str(HERE / 'reproduce-acceptance.py'), '--plan'],
                                cwd='/', capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(result.stdout)
        self.assertIn('EmittedEnvironment', plan['graph'])
        self.assertIn('EmittedClosed', plan['graph'])
        for module in ('CachedEmittedAcceptance', 'CachedAcceptedEmission', 'CachedRejections'):
            self.assertIn(module, plan['graph'])
        self.assertLess(plan['graph'].index('CachedPending10'),
                        plan['graph'].index('CachedEmittedAcceptance'))
        self.assertLess(plan['graph'].index('CachedEmittedAcceptance'),
                        plan['graph'].index('CachedAcceptedEmission'))
        self.assertLess(plan['graph'].index('CachedRejectionsComposition'),
                        plan['graph'].index('CachedRejections'))
        self.assertIn('SquareKit.Internal.GraphEmissionContract', plan['native'])
        self.assertNotIn('Lean4LeanAudit', plan['graph'])
        self.assertLess(plan['graph'].index('EmittedEnvironment'), plan['graph'].index('EmittedClosed'))

    def test_runner_refuses_reusing_output_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run([sys.executable, str(HERE / 'reproduce-acceptance.py'),
                                     '--run-dir', tmp], cwd='/', capture_output=True,
                                    text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('must not exist', result.stderr)

    def test_audit_checks_unused_private_roots_and_dependency_axioms(self):
        with tempfile.TemporaryDirectory(prefix='graph-audit-control-') as tmp:
            root = Path(tmp)
            env = dict(os.environ, LEAN_PATH=str(root))
            (root / 'ClosureAudit.lean').write_text((HERE / 'ClosureAudit.lean').read_text())
            def compile(name, source=None):
                if source is not None:
                    (root / f'{name}.lean').write_text(source)
                return subprocess.run([LEAN, '-R', str(root), '-o', str(root / f'{name}.olean'),
                                       str(root / f'{name}.lean')], cwd=root, env=env,
                                      capture_output=True, text=True, timeout=60)
            result = compile('ClosureAudit')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(compile('Good', 'private theorem hidden : True := True.intro\ndef value : Nat := 2\n').returncode, 0)
            self.assertEqual(compile('Bad', 'private axiom unused : False\n').returncode, 0)
            self.assertEqual(compile('Unsafe', 'unsafe def raw : Nat := 0\n').returncode, 0)
            self.assertEqual(compile('Foreign', 'axiom external : False\n').returncode, 0)
            for label, imports, scope, succeeds in [
                ('positive', 'Good\nimport Foreign', 'Good', True),
                ('unused', 'Bad', 'Bad', False),
                ('missing', 'Good', 'Missing', False),
                ('unsafe-local', 'Unsafe', 'Unsafe', False),
            ]:
                result = compile('Check', f'import ClosureAudit\nimport {imports}\n#audit_closure [{scope}] local [{scope}]\n')
                self.assertEqual(result.returncode == 0, succeeds, label + result.stdout + result.stderr)
            result = compile('Check', 'import ClosureAudit\nimport Unsafe\nimport Good\n#audit_closure [Unsafe, Good] local [Good]\n')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Upstream unsafe source excluded', result.stdout)
            self.assertEqual(compile('UsesForeign', 'import Foreign\ntheorem inherited : False := external\n').returncode, 0)
            result = compile('Check', 'import ClosureAudit\nimport UsesForeign\n#audit_closure [UsesForeign] local [UsesForeign]\n')
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn('external', result.stdout)


if __name__ == '__main__':
    unittest.main()

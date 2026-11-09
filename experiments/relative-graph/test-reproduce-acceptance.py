#!/usr/bin/env python3
"""Black-box controls for the isolated acceptance audit and runner."""
from pathlib import Path
import os
import json
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
LEAN = subprocess.check_output(['elan', 'which', 'lean'], cwd=HERE, text=True).strip()


class AcceptanceControls(unittest.TestCase):
    def test_plan_includes_actual_emission_and_native_dependencies(self):
        result = subprocess.run([sys.executable, str(HERE / 'reproduce-acceptance.py'), '--plan'],
                                cwd='/', capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(result.stdout)
        self.assertIn('EmittedEnvironment', plan['graph'])
        self.assertIn('EmittedClosed', plan['graph'])
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

#!/usr/bin/env python3
"""Public-command controls with real native preflight, compilation and audits."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class HostTargetControls(unittest.TestCase):
    def invoke(self, source):
        with tempfile.TemporaryDirectory(prefix='host-target-control-') as tmp:
            root = Path(tmp)
            paths = ['lean-toolchain', 'scripts/check.py', 'scripts/lake_integrity.py',
                     'scripts/project_sources.py', 'scripts/verification_status.py',
                     'scripts/LeanSourceInfo.lean', 'experiments/host-target/check.py',
                     'experiments/relative-graph/reproduce-acceptance.py',
                     'experiments/relative-graph/ArtifactAudit.lean']
            for relative in paths:
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, target)
            (root / 'Leaf.lean').write_text('def leaf : Nat := 7\n')
            (root / 'experiments/host-target/Contracts.lean').write_text(source(root))
            result = subprocess.run([sys.executable,
                str(root / 'experiments/host-target/check.py'), '--jobs', '1'],
                cwd='/', capture_output=True, text=True, timeout=60)
            return result, (root / 'executed').exists()

    def test_fresh_compile_and_audit_with_native_imports(self):
        result, _ = self.invoke(lambda _: 'import\n /- import Missing -/ Leaf\n'
            'def text := r#"axiom sorry unsafe import Missing"#\n'
            'theorem leaf_eq : leaf = 7 := rfl\n')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('PASS: 3 freshly compiled modules', result.stdout)
        inputs = json.loads(next(line.removeprefix('Source inputs: ')
            for line in result.stdout.splitlines() if line.startswith('Source inputs: ')))
        self.assertIn('scripts/LeanSourceInfo.lean', inputs)
        self.assertIn('scripts/project_sources.py', inputs)
        self.assertIn('experiments/relative-graph/reproduce-acceptance.py', inputs)

    def test_source_rejection_precedes_elaboration(self):
        cases = [
            ('axiom forbidden : False\n', 'Forbidden source construct'),
            ('/-! documentation -/\nimport Leaf\n', 'imports must precede commands'),
            ('import (\n', 'Invalid Lean module header'),
        ]
        for source, diagnostic in cases:
            with self.subTest(source=source):
                result, executed = self.invoke(lambda root: source +
                    f'\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile {json.dumps(str(root / "executed"))} "yes")\n')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stdout + result.stderr)
                self.assertNotIn('PASS:', result.stdout)
                self.assertFalse(executed)

    def test_compilation_error_cannot_pass(self):
        result, _ = self.invoke(lambda _: 'theorem false_proof : False := True.intro\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('PASS:', result.stdout)

    def test_helper_mutation_during_compile_cannot_pass(self):
        result, _ = self.invoke(lambda root:
            'import Lean\nrun_cmd Lean.Elab.Command.liftIO (IO.FS.writeFile '
            + json.dumps(str(root / 'scripts/LeanSourceInfo.lean')) + ' "")\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('validation inputs changed', result.stdout + result.stderr)
        self.assertNotIn('PASS:', result.stdout)


if __name__ == '__main__':
    unittest.main()

#!/usr/bin/env python3
"""Exercise successor comparison through its public command-line interface."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import warnings
import zipfile

COMMAND = Path(__file__).with_name('adwh-snapshot-diff.py')


class SnapshotComparison(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='adwh-diff-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def archive(self, name, members):
        path = self.root / name
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', UserWarning)
            with zipfile.ZipFile(path, 'w') as target:
                for member, content in members:
                    target.writestr(member, content)
        return path

    def run_diff(self, old, new, *args):
        return subprocess.run([sys.executable, str(COMMAND), str(old), str(new), *args],
                              capture_output=True, text=True, check=False)

    def test_changed_added_removed_and_dependency_controls(self):
        old = self.archive('old.zip', [('project/lean-toolchain', 'v1'),
            ('project/Keep.lean', 'same'), ('project/Edit.lean', 'old'),
            ('project/Delete.lean', 'gone')])
        new = self.archive('new.zip', [('project/lean-toolchain', 'v2'),
            ('project/Keep.lean', 'same'), ('project/Edit.lean', 'new'),
            ('project/Add.lean', 'fresh')])
        result = self.run_diff(old, new)
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertEqual(data['counts'], dict(old_members=4, new_members=4,
            unchanged=1, changed=2, added=1, removed=1))
        self.assertEqual(data['unchanged'], ['project/Keep.lean'])
        self.assertEqual(list(data['added']), ['project/Add.lean'])
        self.assertEqual(list(data['removed']), ['project/Delete.lean'])
        self.assertEqual(data['dependency_review']['build_control_paths'],
                         ['project/lean-toolchain'])
        self.assertEqual(data['dependency_review']['changed_lean_paths'],
                         ['project/Add.lean', 'project/Delete.lean', 'project/Edit.lean'])
        self.assertEqual(data['relocation_candidates'], [])
        control = data['dependency_review']['build_control_diffs']['project/lean-toolchain']
        self.assertIn('-v1', control)
        self.assertIn('+v2', control)

    def test_relocation_keeps_ambiguous_copies_visible(self):
        old = self.archive('old.zip', [('old/A.lean', 'proof')])
        new = self.archive('new.zip', [('new/B.lean', 'proof'), ('new/C.lean', 'proof')])
        data = json.loads(self.run_diff(old, new).stdout)
        self.assertEqual(len(data['relocation_candidates']), 1)
        move = data['relocation_candidates'][0]
        self.assertEqual(move['old_paths'], ['old/A.lean'])
        self.assertEqual(move['new_paths'], ['new/B.lean', 'new/C.lean'])
        self.assertEqual(data['counts']['added'], 2)
        self.assertEqual(data['counts']['removed'], 1)

    def test_same_archive_has_no_changes_and_writes_report(self):
        archive = self.archive('same.zip', [('a.lean', 'proof'), ('notes.txt', 'scope')])
        output = self.root / 'result.json'
        result = self.run_diff(archive, archive, '--output', str(output))
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(output.read_text())
        self.assertEqual(data['counts']['unchanged'], 2)
        self.assertEqual(data['changed'], {})
        self.assertEqual(data['old_archive']['sha256'], data['new_archive']['sha256'])

    def test_ambiguous_duplicate_member_rejected(self):
        old = self.archive('duplicate.zip', [('a.lean', 'one'), ('a.lean', 'two')])
        new = self.archive('new.zip', [])
        self.assertNotEqual(self.run_diff(old, new).returncode, 0)

    def test_nonrelative_member_rejected(self):
        old = self.archive('parent.zip', [('../a.lean', 'proof')])
        new = self.archive('new.zip', [])
        self.assertNotEqual(self.run_diff(old, new).returncode, 0)

    def test_output_cannot_replace_input(self):
        archive = self.archive('source.zip', [('a.lean', 'proof')])
        original = archive.read_bytes()
        result = self.run_diff(archive, archive, '--output', str(archive))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(archive.read_bytes(), original)


if __name__ == '__main__':
    unittest.main()

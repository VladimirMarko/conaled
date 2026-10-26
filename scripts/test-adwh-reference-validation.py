#!/usr/bin/env python3
"""Exercise failed restoration receipts without running Lean or altering evidence."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

DRIVER = Path(__file__).resolve().parents[1] / 'docs/research/adwh-reference-validation.py'


class RestorationFailures(unittest.TestCase):
    def run_failure(self, mode, expected_stage):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            driver = root / 'docs/research/adwh-reference-validation.py'
            driver.parent.mkdir(parents=True)
            shutil.copyfile(DRIVER, driver)
            history = root / 'docs/history/algorithm-design-haskell'
            history.mkdir(parents=True)
            archive = history / 'checkpoint-233.zip'
            if mode == 'missing_member':
                with zipfile.ZipFile(archive, 'w') as output:
                    output.writestr('actual.txt', 'fixture')
            else:
                archive.write_bytes(b'not a ZIP archive')
            manifest = history / 'checkpoint-233.files.sha256'
            manifest.write_text('0' * 64 + '  missing.txt\n')
            metadata = dict(archive=archive.name, member_manifest=manifest.name,
                            archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                            member_manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
                            regular_files=1)
            if mode == 'bad_hash':
                metadata['archive_sha256'] = '0' * 64
            (history / 'checkpoint-233.json').write_text(json.dumps(metadata))
            state = root / 'run'
            result = subprocess.run([sys.executable, str(driver), str(state)],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            receipt = json.loads((state / 'result.json').read_text())
            self.assertEqual(receipt['status'], 'failed')
            self.assertEqual(receipt['stage'], expected_stage)
            self.assertIn('Traceback', (state / 'failure.log').read_text())
            self.assertIn('total_seconds', receipt)
            self.assertFalse((state / 'fresh-objects').exists())

    def test_bad_archive_digest(self):
        self.run_failure('bad_hash', 'archive_integrity')

    def test_invalid_zip(self):
        self.run_failure('invalid_zip', 'archive_restoration')

    def test_missing_manifest_member(self):
        self.run_failure('missing_member', 'member_integrity')


if __name__ == '__main__':
    unittest.main()

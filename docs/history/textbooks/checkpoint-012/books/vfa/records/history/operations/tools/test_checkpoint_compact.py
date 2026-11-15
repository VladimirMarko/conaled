#!/usr/bin/env python3
"""Focused recovery tests; every fixture lives in a disposable workspace."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest
from unittest import mock


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("compact", HERE / "checkpoint_compact.py")
compact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compact)


class Recovery(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="compact-test-", dir=HERE.parents[1])
        self.root = Path(self.temp.name)
        self.ws = self.root / "workspace"
        self.repo = self.ws / "conaled"
        self.state = self.ws / "work-state"
        self.repo.mkdir(parents=True)
        self.state.mkdir()
        self.kit = self.root / "kit"
        self.kit.mkdir()
        (self.kit / "conaled_native.py").write_text(
            "import sys\nassert sys.argv[1:] == ['verify']\nprint('verified fixture')\n")
        (self.state / "STATUS.md").write_text("Pending mathematical gates.\n")
        (self.state / "readonly.evidence").write_text("Read-only evidence bytes\n")
        (self.state / "readonly.evidence").chmod(0o444)
        compact.run(["git", "init", "--quiet", str(self.repo)])
        compact.git(self.repo, "config", "user.name", "Recovery test")
        compact.git(self.repo, "config", "user.email", "recovery@example.invalid")
        for name, data in {"a.txt": b"base\n", "deleted.txt": b"remove me\n",
                           "file-to-dir": b"old file\n", "dir-to-file/child": b"old child\n",
                           "dir-to-link/child": b"old child\n", ".gitignore": b"ignored/\n"}.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        compact.git(self.repo, "add", ".")
        compact.git(self.repo, "commit", "--quiet", "-m", "test baseline")
        self.baseline = compact.git(self.repo, "rev-parse", "HEAD").decode().strip()
        bundle = self.root / "original.bundle"
        compact.git(self.repo, "bundle", "create", str(bundle), "--all", "HEAD")
        self.base = self.root / "base.tar.gz"
        compact.create_base(argparse.Namespace(bundle=bundle, base_commit=self.baseline,
                                               output=self.base))

    def tearDown(self):
        self.temp.cleanup()

    def capture(self, filename="latest.tar.gz", active=()):
        output = self.root / filename
        result = compact.capture(argparse.Namespace(
            workspace=self.ws, kit=self.kit, base=self.base, output=output,
            base_library_id=None, active_attempt=list(active)))
        self.assertEqual(result["restore_smoke"], "passed")
        return output

    def test_clean_and_cumulative_recovery_needs_no_previous_snapshot(self):
        first = self.capture("first.tar.gz")
        (self.repo / "a.txt").write_text("first change\n")
        compact.git(self.repo, "add", "a.txt")
        compact.git(self.repo, "commit", "--quiet", "-m", "first task commit")
        (self.repo / "new.txt").write_text("second change\n")
        compact.git(self.repo, "add", "new.txt")
        compact.git(self.repo, "commit", "--quiet", "-m", "second task commit")
        latest = self.capture()
        first.unlink()
        destination = self.root / "recovered"
        compact.restore(self.base, latest, destination)
        self.assertEqual(compact.source_state(self.repo),
                         compact.source_state(destination / "conaled"))
        self.assertEqual(compact.refs(self.repo), compact.refs(destination / "conaled"))
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            compact.restore(self.base, latest, destination)

    def test_exact_dirty_index_binary_modes_deletions_and_path_transitions(self):
        (self.repo / "a.txt").write_bytes(b"staged\x00binary\n")
        compact.git(self.repo, "add", "a.txt")
        (self.repo / "a.txt").write_bytes(b"working\x00binary\n")
        compact.git(self.repo, "rm", "--quiet", "deleted.txt")
        (self.repo / "file-to-dir").unlink()
        (self.repo / "file-to-dir").mkdir()
        (self.repo / "file-to-dir/new").write_text("replacement child\n")
        shutil.rmtree(self.repo / "dir-to-file")
        (self.repo / "dir-to-file").write_text("replacement file\n")
        shutil.rmtree(self.repo / "dir-to-link")
        os.symlink("file-to-dir", self.repo / "dir-to-link")
        (self.repo / "executable.sh").write_text("#!/bin/sh\nexit 0\n")
        (self.repo / "executable.sh").chmod(0o755)
        os.symlink("a.txt", self.repo / "new-link")
        (self.repo / "ignored").mkdir()
        (self.repo / "ignored/cache").write_text("not source\n")
        before = compact.source_state(self.repo)
        latest = self.capture()
        destination = self.root / "dirty-recovered"
        compact.restore(self.base, latest, destination)
        self.assertEqual(before, compact.source_state(destination / "conaled"))
        self.assertFalse((destination / "conaled/ignored/cache").exists())
        self.assertEqual(os.readlink(destination / "conaled/new-link"), "a.txt")

    def test_corruption_wrong_base_and_unsafe_members_rejected(self):
        latest = self.capture()
        unpacked = compact.unpack(latest, self.root / "unpack", "checkpoint")
        (unpacked / "work-state/STATUS.md").write_text("corrupted")
        bad = self.root / "bad.tar.gz"
        compact.pack(unpacked, bad)
        with self.assertRaisesRegex(RuntimeError, "manifest mismatch"):
            compact.restore(self.base, bad, self.root / "must-not-exist")
        self.assertFalse((self.root / "must-not-exist").exists())
        other_base = self.root / "other-base.tar.gz"
        base_root = compact.unpack(self.base, self.root / "base-unpack", "base")
        (base_root / "extra.txt").write_text("valid but different base archive")
        compact.manifest(base_root, write=True)
        compact.pack(base_root, other_base)
        with self.assertRaisesRegex(RuntimeError, "Wrong immutable base"):
            compact.restore(other_base, latest, self.root / "wrong-base-destination")
        unsafe = self.root / "unsafe.tar.gz"
        with tarfile.open(unsafe, "w:gz") as archive:
            member = tarfile.TarInfo("checkpoint/../../escape")
            archive.addfile(member)
        with self.assertRaisesRegex(RuntimeError, "Unsafe"):
            compact.unpack(unsafe, self.root / "unsafe-extract", "checkpoint")
        self.assertFalse((self.root / "escape").exists())

    def test_credential_source_paths_refuse_publication(self):
        for tracked in (False, True):
            for name in (".env", "nested/.aws/config"):
                with self.subTest(tracked=tracked, path=name):
                    path = self.repo / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("dummy fixture credential\n")
                    if tracked:
                        compact.git(self.repo, "add", "--", name)
                    filename = f"credential-{tracked}-{path.name}.tar.gz"
                    try:
                        with self.assertRaisesRegex(RuntimeError, "Credential-like source path"):
                            self.capture(filename)
                        self.assertFalse((self.root / filename).exists())
                    finally:
                        if tracked:
                            compact.git(self.repo, "reset", "--quiet", "HEAD", "--", name)
                        path.unlink()

    def test_missing_or_symlink_work_state_root_refuses_publication(self):
        saved = self.ws / "saved-work-state"
        self.state.rename(saved)
        with self.assertRaisesRegex(RuntimeError, "Required work-state/kit root"):
            self.capture("missing-state.tar.gz")
        self.assertFalse((self.root / "missing-state.tar.gz").exists())
        self.state.symlink_to(saved, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "root symlinks"):
            self.capture("symlink-state.tar.gz")
        self.assertFalse((self.root / "symlink-state.tar.gz").exists())

    def test_symlink_kit_root_refuses_publication(self):
        original_kit = self.kit
        self.kit = self.root / "symlink-kit"
        self.kit.symlink_to(original_kit, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "root symlinks"):
            self.capture("symlink-kit.tar.gz")
        self.assertFalse((self.root / "symlink-kit.tar.gz").exists())

    def test_unreadable_work_state_subtree_refuses_publication(self):
        blocked = self.state / "evidence"
        blocked.mkdir()
        (blocked / "required.txt").write_text("required evidence\n")
        original_scandir = os.scandir
        def denied_scandir(path):
            if not isinstance(path, int) and Path(path) == blocked:
                raise PermissionError("injected evidence enumeration failure")
            return original_scandir(path)
        with mock.patch.object(compact.os, "scandir", side_effect=denied_scandir):
            with self.assertRaisesRegex(PermissionError, "injected evidence enumeration failure"):
                self.capture("unreadable-state.tar.gz")
        self.assertFalse((self.root / "unreadable-state.tar.gz").exists())

    def test_stable_state_change_refuses_publication(self):
        original = compact.restore
        def changing_restore(*args, **kwargs):
            result = original(*args, **kwargs)
            (self.state / "STATUS.md").write_text("Concurrent tracker edit\n")
            return result
        with mock.patch.object(compact, "restore", side_effect=changing_restore):
            with self.assertRaisesRegex(RuntimeError, "workflow files changed"):
                self.capture()
        self.assertFalse((self.root / "latest.tar.gz").exists())

    def test_declared_active_attempt_is_retained_as_prefix(self):
        attempt = self.state / "validation/active"
        attempt.mkdir(parents=True)
        (attempt / "child.log").write_text("prefix\n")
        (attempt / "run.json").write_text('{"status":"running"}\n')
        original = compact.restore
        def growing_restore(*args, **kwargs):
            result = original(*args, **kwargs)
            with (attempt / "child.log").open("a") as out:
                out.write("later output\n")
            (attempt / "run.json").write_text('{"status":"still running"}\n')
            return result
        with mock.patch.object(compact, "restore", side_effect=growing_restore):
            latest = self.capture(active=["validation/active"])
        destination = self.root / "active-recovered"
        meta = compact.restore(self.base, latest, destination)
        self.assertEqual(meta["active_attempts"], ["validation/active"])
        self.assertEqual((destination / "work-state/validation/active/child.log").read_text(),
                         "prefix\n")
        self.assertEqual(json.loads((destination / "work-state/validation/active/run.json").read_text()),
                         {"status": "running"})


if __name__ == "__main__":
    unittest.main(verbosity=2)

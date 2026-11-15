"""Disposable metadata/Git fixtures. No project source or Lean is executed."""
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
TOOL = Path(__file__).resolve().with_name("checkpoint.py")
SPEC = importlib.util.spec_from_file_location("checkpoint_under_test", TOOL)
cp = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cp)
RUNTIME = TOOL.parent.parent.parent / ".checkpoint-tests"
RUNTIME.mkdir(exist_ok=True)


def shell_git(repo, *args):
    env = cp.git_environment()
    env.update(GIT_AUTHOR_NAME="Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid", GIT_COMMITTER_NAME="Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid")
    return subprocess.check_output(["git", "-C", str(repo), *map(str, args)], env=env, stderr=subprocess.PIPE).decode().strip()


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=RUNTIME)
        self.base = Path(self.temp.name)
        self.root = self.base / "conaled-textbooks"
        self.root.mkdir()
        self.repo = self.base / "development"
        self.repo.mkdir()
        shell_git(self.repo, "init", "-b", "work")
        (self.repo / "Fixture.lean").write_text("-- Disposable inert source fixture, not a proof.\n")
        shell_git(self.repo, "add", ".")
        shell_git(self.repo, "commit", "-m", "fixture baseline")
        self.oid = shell_git(self.repo, "rev-parse", "HEAD")
        for name in ("README.md", "AGENTS.md", "docs/DURABILITY.md"):
            self.write(name, name + ": fixture control\n")
        self.write("tools/checkpoint.py", TOOL.read_bytes())
        self.write("reference/pin.md", "Fixture pinned governance\n")
        self.write("support/native-kit/helper.c", "/* Fixed historical bootstrap fixture. */\n")
        self.catalog = {"schema": 1, "base_commit": self.oid, "repository_url": "fixture-local", "objects": "repository.bundle", "external_archive_dependencies": [], "baseline_refs": [], "books": {}}
        for book in sorted(cp.BOOKS):
            ref = f"refs/checkpoint/{book}/heads/work"
            shell_git(self.repo, "update-ref", ref, self.oid)
            self.catalog["books"][book] = {"refs": [{"original_ref": "refs/heads/work", "stored_ref": ref, "object": self.oid}], "roles": {"main": ref, "candidate": ref}}
            self.write(f"books/{book}/records/math.md", "Frozen " + book + "\n")
            self.write(f"books/{book}/work/README.md", "New work owner " + book + "\n")
            self.write(f"books/{book}/STATE.json", "{}\n")
            self.write(f"books/{book}/README.md", book + " entry\n")
        self.write_json("source/refs.json", self.catalog)
        self.write_json("source/saved-worktrees.json", {"schema": 1, "worktrees": [{"book": "pfds", "name": "review", "commit": self.oid}]})
        self.bundle()
        self.policy = {"schema": 1, "protected_files": {x: cp.file_hash(self.root / x) for x in ["README.md", "AGENTS.md", "docs/DURABILITY.md", "tools/checkpoint.py"]}, "initial_refs": cp.refs_from_catalog(self.catalog), "required_commits": [self.oid], "inherited_archive_blobs": {}, "native_kit": {"root": "support/native-kit", "files": {"helper.c": cp.metadata(self.root / "support/native-kit/helper.c")}}, "frozen_trees": {}, "limits": {"max_files": 500, "max_total_bytes": 5 * 1024 * 1024, "max_file_bytes": 2 * 1024 * 1024, "max_archive_bytes": 2 * 1024 * 1024, "max_growth_ratio": 1.05, "max_growth_bytes": 1024 * 1024}}
        for prefix in ["reference"] + [f"books/{book}/records" for book in sorted(cp.BOOKS)]:
            self.policy["frozen_trees"][prefix] = cp.digest(cp.canonical({p.relative_to(self.root / prefix).as_posix(): cp.metadata(p) for p in (self.root / prefix).rglob("*") if p.is_file()}))
        self.write_policy()

    def tearDown(self):
        self.temp.cleanup()

    def write(self, name, value):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(value.encode() if isinstance(value, str) else value)
        p.chmod(0o644)
        return p

    def write_json(self, name, value):
        return self.write(name, cp.json_bytes(value))

    def write_policy(self):
        self.write_json("policy.json", self.policy)
        self.write_json("checkpoint.json", {"schema": 1, "series": "conaled-textbooks", "serial": 1, "policy_sha256": cp.file_hash(self.root / "policy.json"), "parent_manifest_sha256": None})

    def bundle(self):
        out = self.root / "source/repository.bundle"
        out.parent.mkdir(exist_ok=True)
        out.unlink(missing_ok=True)
        refs = list(cp.refs_from_catalog(self.catalog))
        shell_git(self.repo, "bundle", "create", out, *refs)
        out.chmod(0o644)

    def first_pack(self):
        archive = self.base / "conaled-textbooks-001.tar.xz"
        result = cp.pack(self.root, archive, False)
        return archive, result

    def mark_uploaded(self, archive):
        receipt = self.base / "real-receipt-fixture.json"
        receipt.write_bytes(cp.json_bytes({"method": "create_library_file", "destination": "owner-root", "library_file_id": "libfile_fixture", "archive_sha256": cp.file_hash(archive), "archive_bytes": archive.stat().st_size}))
        return cp.record_delivery(self.root, archive, receipt=receipt)

    def snapshot(self):
        return {p.relative_to(self.root).as_posix(): p.read_bytes() for p in self.root.rglob("*") if p.is_file() and not p.is_symlink()}

    def prepare_contract_amendment(self):
        self.write_json("books/vfa/STATE.json", {"accepted": False})
        archive, _ = self.first_pack()
        self.mark_uploaded(archive)
        old_manifest = (self.root / "MANIFEST.json").read_bytes()
        archive_bytes = b"PK\x03\x04immutable upstream archive fixture"
        (self.repo / "history.zip").write_bytes(archive_bytes)
        shell_git(self.repo, "add", "history.zip")
        shell_git(self.repo, "commit", "-m", "pinned upstream historical source")
        pin = shell_git(self.repo, "rev-parse", "HEAD")
        blob = shell_git(self.repo, "rev-parse", "HEAD:history.zip")
        ref = "refs/checkpoint/base/pinned-master"
        shell_git(self.repo, "update-ref", ref, pin)
        self.catalog["baseline_refs"].append({"original_ref": "refs/heads/master", "stored_ref": ref, "object": pin})
        self.write_json("source/refs.json", self.catalog)
        self.bundle()
        self.policy["required_commits"].append(pin)
        identity = {"bytes": len(archive_bytes), "sha256": cp.digest(archive_bytes)}
        self.policy["inherited_archive_blobs"][blob] = identity
        self.policy["limits"]["max_archive_bytes"] += 1024 * 1024
        self.write("README.md", "Updated native setup guidance; unchanged mathematical scope.\n")
        self.policy["protected_files"]["README.md"] = cp.file_hash(self.root / "README.md")
        self.write_json("books/vfa/STATE.json", {"accepted": False, "integration": {"status": "pending", "pin": pin}})
        self.write("books/common/amendment.md", "User-directed pinned upstream import and operational setup correction.\n")
        self.policy["source_import_amendment"] = {
            "schema": 1, "from_serial": 1, "to_serial": 2,
            "previous_manifest_sha256": cp.digest(old_manifest),
            "previous_archive_sha256": cp.file_hash(archive), "master_commit": pin,
            "source_bundle": {k: cp.metadata(self.root / "source/repository.bundle")[k] for k in ("bytes", "sha256")},
            "added_archive_blobs": {blob: identity}, "rationale_path": "books/common/amendment.md",
        }
        self.write_policy()
        return archive, pin

    def test_contract_update_preserves_history_and_requires_explicit_exact_prior(self):
        archive, pin = self.prepare_contract_amendment()
        output = self.base / "conaled-textbooks-002.tar.xz"
        with self.assertRaisesRegex(cp.Refusal, "Checkpoint metadata changed"):
            cp.pack(self.root, output, True)
        wrong = self.base / "wrong-prior.tar.xz"
        wrong.write_bytes(archive.read_bytes() + b"wrong")
        with self.assertRaisesRegex(cp.Refusal, "Previous archive differs"):
            cp.pack(self.root, output, True, wrong)
        result = cp.pack(self.root, output, True, archive)
        self.assertTrue(result["contract_update_applied"])
        self.assertFalse(result["completed"])
        self.assertTrue(cp.verify(self.root, True)["deep_source"])
        self.assertEqual(cp.read_json(self.root / "books/vfa/STATE.json")["accepted"], False)
        self.assertIn(pin, cp.refs_from_catalog(cp.read_json(self.root / "source/refs.json")).values())
        self.mark_uploaded(output)
        with self.assertRaisesRegex(cp.Refusal, "001 -> 002"):
            cp.pack(self.root, self.base / "conaled-textbooks-003.tar.xz", True, output)
        # The retained amendment never makes a future ordinary pack exceptional.
        third = cp.pack(self.root, self.base / "conaled-textbooks-003.tar.xz", True)
        self.assertFalse(third["contract_update_applied"])

    def test_contract_update_refuses_math_loss_even_with_rewritten_policy(self):
        archive, _ = self.prepare_contract_amendment()
        self.write("books/pfds/records/math.md", "Changed mathematical evidence\n")
        prefix = self.root / "books/pfds/records"
        self.policy["frozen_trees"]["books/pfds/records"] = cp.digest(cp.canonical({p.relative_to(prefix).as_posix(): cp.metadata(p) for p in prefix.rglob("*") if p.is_file()}))
        self.write_policy()
        before = self.snapshot()
        output = self.base / "conaled-textbooks-002.tar.xz"
        with self.assertRaisesRegex(cp.Refusal, "preserved mathematical/evidence"):
            cp.pack(self.root, output, True, archive)
        self.assertEqual(before, self.snapshot())
        self.assertFalse(output.exists())

    def test_contract_update_refuses_acceptance_change_and_growth_relaxation(self):
        archive, _ = self.prepare_contract_amendment()
        self.write_json("books/vfa/STATE.json", {"accepted": True, "integration": {"status": "pending"}})
        with self.assertRaisesRegex(cp.Refusal, "state/acceptance"):
            cp.pack(self.root, self.base / "conaled-textbooks-002.tar.xz", True, archive)
        self.write_json("books/vfa/STATE.json", {"accepted": False, "integration": {"status": "pending"}})
        self.policy["limits"]["max_growth_ratio"] = 2.0
        self.write_policy()
        with self.assertRaisesRegex(cp.Refusal, "normal payload/source/growth"):
            cp.pack(self.root, self.base / "conaled-textbooks-002.tar.xz", True, archive)
        self.policy["limits"]["max_growth_ratio"] = 1.05
        self.write_policy()
        self.write("books/pfds/work/excess.md", "x" * (1024 * 1024 + 8192))
        with self.assertRaisesRegex(cp.Refusal, "Growth exceeds"):
            cp.pack(self.root, self.base / "conaled-textbooks-002.tar.xz", True, archive)

    def test_contract_update_refuses_archive_exception_outside_pinned_history(self):
        archive, pin = self.prepare_contract_amendment()
        data = b"PK\x03\x04unrelated new checkpoint archive"
        (self.repo / "unrelated.zip").write_bytes(data)
        shell_git(self.repo, "add", "unrelated.zip")
        shell_git(self.repo, "commit", "-m", "unapproved later archive")
        tip = shell_git(self.repo, "rev-parse", "HEAD")
        blob = shell_git(self.repo, "rev-parse", "HEAD:unrelated.zip")
        ref = "refs/checkpoint/base/unrelated"
        shell_git(self.repo, "update-ref", ref, tip)
        self.catalog["baseline_refs"].append({"original_ref": "refs/heads/unrelated", "stored_ref": ref, "object": tip})
        self.write_json("source/refs.json", self.catalog)
        self.bundle()
        identity = {"bytes": len(data), "sha256": cp.digest(data)}
        self.policy["inherited_archive_blobs"][blob] = identity
        amendment = self.policy["source_import_amendment"]
        amendment["added_archive_blobs"][blob] = identity
        amendment["source_bundle"] = {k: cp.metadata(self.root / "source/repository.bundle")[k] for k in ("bytes", "sha256")}
        self.write_policy()
        before = self.snapshot()
        output = self.base / "conaled-textbooks-002.tar.xz"
        with self.assertRaisesRegex(cp.Refusal, "not in the exact pinned master history"):
            cp.pack(self.root, output, True, archive)
        self.assertEqual(before, self.snapshot())
        self.assertFalse(output.exists())

    def test_initial_pack_exact_offline_restore_and_delivery_separation(self):
        archive, result = self.first_pack()
        self.assertFalse(result["completed"])
        self.assertFalse(result["durable_uploaded"])
        self.assertTrue(cp.verify(self.root, True)["deep_source"])
        destination = self.base / "restored"
        restored = cp.restore(self.root, destination, True)
        self.assertEqual(restored["historical_refs"], 3)
        for book in cp.BOOKS:
            work = destination / "worktrees" / book
            self.assertEqual(shell_git(work, "rev-parse", "HEAD"), self.oid)
            self.assertNotEqual(subprocess.run(["git", "-C", str(work), "symbolic-ref", "-q", "HEAD"], capture_output=True).returncode, 0)
        self.assertEqual(len(list((destination / "saved-worktrees").iterdir())), 1)
        self.assertEqual((destination / "worktrees/pfds/Fixture.lean").read_bytes(), (self.repo / "Fixture.lean").read_bytes())

    def test_next_requires_real_receipt_and_can_adopt_saved_input_after_wipe(self):
        archive, _ = self.first_pack()
        before = self.snapshot()
        with self.assertRaisesRegex(cp.Refusal, "durable delivery"):
            cp.pack(self.root, self.base / "conaled-textbooks-002.tar.xz", True)
        with self.assertRaisesRegex(cp.Refusal, "Prior release is not recorded"):
            cp.capture(self.root, "pfds", self.repo, "refs/heads/work")
        self.assertEqual(before, self.snapshot())
        self.assertTrue(self.mark_uploaded(archive)["completed"])
        cp.delivery_path(self.root).unlink()
        self.assertTrue(cp.record_delivery(self.root, archive, library_id="libfile_attached_fixture")["completed"])
        old_manifest = (self.root / "MANIFEST.json").read_bytes()
        self.write("books/pfds/work/unfinished.md", "Useful incomplete paper mathematics.\n")
        second = self.base / "conaled-textbooks-002.tar.xz"
        result = cp.pack(self.root, second, True)
        self.assertEqual(result["serial"], 2)
        self.assertEqual(cp.read_json(self.root / "checkpoint.json")["parent_manifest_sha256"], cp.digest(old_manifest))
        self.assertFalse(result["completed"])
        with tarfile.open(second, "r:xz") as t:
            names = t.getnames()
        self.assertEqual(sum(x.endswith("/MANIFEST.json") for x in names), 1)
        self.assertFalse(any("001.tar" in x for x in names))

    def test_payload_guards_archives_magic_partials_symlinks_hardlinks_and_frozen_controls(self):
        checks = [("books/pfds/work/old.zip", b"plain", "Nested archive"), ("books/pfds/work/hidden.txt", b"PK\x03\x04x", "Archive magic"), ("books/pfds/work/transfer.partial", b"half", "Partial"), ("books/pfds/work/object.olean", b"cache", "Build/cache"), ("books/pfds/records/extra.md", b"drift", "Frozen tree")]
        for name, content, message in checks:
            with self.subTest(name=name):
                p = self.write(name, content)
                with self.assertRaisesRegex(cp.Refusal, message):
                    cp.inspect_payload(self.root, self.policy)
                p.unlink()
        link = self.root / "books/pfds/work/link.md"
        link.symlink_to(self.root / "AGENTS.md")
        with self.assertRaises(cp.Refusal):
            cp.inspect_payload(self.root, self.policy)
        link.unlink()
        os.link(self.root / "AGENTS.md", link)
        with self.assertRaises(cp.Refusal):
            cp.inspect_payload(self.root, self.policy)
        link.unlink()
        self.write("AGENTS.md", "changed")
        with self.assertRaisesRegex(cp.Refusal, "Protected"):
            cp.inspect_payload(self.root, self.policy)

    def test_native_kit_exact_modes_files_and_policy_binding(self):
        p = self.root / "support/native-kit/helper.c"
        p.chmod(0o755)
        with self.assertRaisesRegex(cp.Refusal, "Native kit"):
            cp.inspect_payload(self.root, self.policy)
        p.chmod(0o644)
        self.write("support/native-kit/new.c", "new")
        with self.assertRaisesRegex(cp.Refusal, "Native kit"):
            cp.inspect_payload(self.root, self.policy)
        (self.root / "support/native-kit/new.c").unlink()
        self.write("policy.json", "{}\n")
        with self.assertRaises(cp.Refusal):
            cp.policy_and_checkpoint(self.root)

    def test_mutable_book_state_and_navigation_cannot_disappear(self):
        for name in ("books/pfds/STATE.json", "books/vfa/README.md"):
            path = self.root / name
            content = path.read_bytes()
            path.unlink()
            with self.assertRaisesRegex(cp.Refusal, "Required book navigation/state"):
                cp.inspect_payload(self.root, self.policy)
            path.write_bytes(content)
        self.write_json("books/fdsa/STATE.json", [])
        with self.assertRaisesRegex(cp.Refusal, "must be an object"):
            cp.inspect_payload(self.root, self.policy)

    def test_tar_rejects_traversal_links_duplicate_and_multiple_roots(self):
        cases = [("../escape", None), ("conaled-textbooks/../../escape", None), ("other/file", None), ("conaled-textbooks/link", tarfile.SYMTYPE), ("conaled-textbooks/hard", tarfile.LNKTYPE)]
        for i, (name, kind) in enumerate(cases):
            archive = self.base / f"evil-{i}.tar.xz"
            with tarfile.open(archive, "w:xz") as t:
                info = tarfile.TarInfo(name)
                info.mode = 0o644
                if kind:
                    info.type, info.linkname = kind, "../../escape"
                t.addfile(info)
            destination = self.base / f"extract-{i}"
            destination.mkdir()
            with self.assertRaises(cp.Refusal):
                cp.safe_extract(archive, destination, "conaled-textbooks", self.policy["limits"])
        archive = self.base / "duplicate.tar.xz"
        with tarfile.open(archive, "w:xz") as t:
            for _ in range(2):
                t.addfile(tarfile.TarInfo("conaled-textbooks/file"))
        destination = self.base / "duplicates"
        destination.mkdir()
        with self.assertRaises(cp.Refusal):
            cp.safe_extract(archive, destination, "conaled-textbooks", self.policy["limits"])

    def test_missing_prerequisite_and_initial_ref_loss_are_refused(self):
        (self.repo / "Fixture.lean").write_text("-- changed fixture\n")
        shell_git(self.repo, "commit", "-am", "second")
        update = self.base / "incremental.bundle"
        shell_git(self.repo, "bundle", "create", update, "HEAD", "^" + self.oid)
        with self.assertRaisesRegex(cp.Refusal, "external prerequisites"):
            cp.load_source(update, self.catalog, self.policy, self.base / "bad.git", self.base)
        changed = copy.deepcopy(self.catalog)
        changed["books"]["pfds"]["refs"][0]["object"] = shell_git(self.repo, "rev-parse", "HEAD")
        with self.assertRaisesRegex(cp.Refusal, "Immutable initial"):
            cp.load_source(self.root / "source/repository.bundle", changed, self.policy, self.base / "bad2.git", self.base)

    def test_dirty_untracked_and_ignored_math_capture_refuse_without_writes(self):
        original = self.snapshot()
        p = self.repo / "Untracked.lean"
        p.write_text("-- unsaved proof draft\n")
        with self.assertRaisesRegex(cp.Refusal, "Dirty/untracked"):
            cp.capture(self.root, "pfds", self.repo, "refs/heads/work")
        self.assertEqual(original, self.snapshot())
        self.assertTrue(p.exists())
        p.unlink()
        (self.repo / ".gitignore").write_text("ignored/\n")
        shell_git(self.repo, "add", ".gitignore")
        shell_git(self.repo, "commit", "-m", "fixture ignore rule")
        (self.repo / "ignored").mkdir()
        for filename in ("draft.lean", "unfinished-proof.txt", "theory.thy", "proof-data.json"):
            with self.subTest(ignored_file=filename):
                p = self.repo / "ignored" / filename
                content = "Ignored mathematical work in a format-independent capture fixture.\n"
                p.write_text(content)
                with self.assertRaisesRegex(cp.Refusal, "Ignored potential"):
                    cp.capture(self.root, "pfds", self.repo, "refs/heads/work")
                self.assertEqual(original, self.snapshot())
                self.assertEqual(p.read_text(), content)
                p.unlink()

    def test_clean_capture_preserves_full_ref_union_and_exact_new_source(self):
        (self.repo / "New.lean").write_text("-- new disposable fixture\n")
        shell_git(self.repo, "add", "New.lean")
        shell_git(self.repo, "commit", "-m", "new source fixture")
        new = shell_git(self.repo, "rev-parse", "HEAD")
        shell_git(self.repo, "branch", "other-history", self.oid)
        result = cp.capture(self.root, "pfds", self.repo, "refs/heads/work")
        self.assertEqual(result["candidate"], new)
        catalog = cp.read_json(self.root / "source/refs.json")
        refs = cp.refs_from_catalog(catalog)
        self.assertTrue(all(refs.get(k) == v for k, v in self.policy["initial_refs"].items()))
        store = self.base / "roundtrip.git"
        cp.load_source(self.root / "source/repository.bundle", catalog, self.policy, store, self.base)
        self.assertEqual(shell_git(store, "show", new + ":New.lean"), "-- new disposable fixture")
        self.assertEqual(shell_git(store, "show", self.oid + ":Fixture.lean"), "-- Disposable inert source fixture, not a proof.")
        self.assertTrue(any(x["original_ref"] == "refs/heads/other-history" for x in catalog["books"]["pfds"]["refs"]))

    def test_git_hidden_archive_and_cache_partial_rejected(self):
        for i, (name, data) in enumerate([("hidden.dat", b"PK\x03\x04payload"), ("transfer.partial", b"incomplete"), ("cache.olean", b"compiled")]):
            with self.subTest(name=name):
                source = self.base / f"badsource-{i}"
                shell_git(self.repo, "clone", "--no-hardlinks", self.repo, source)
                (source / name).write_bytes(data)
                shell_git(source, "add", name)
                shell_git(source, "commit", "-m", "prohibited fixture")
                before = self.snapshot()
                with self.assertRaises(cp.Refusal):
                    cp.capture(self.root, "pfds", source, "refs/heads/work")
                self.assertEqual(before, self.snapshot())

    def test_output_guard_and_failed_verification_do_not_publish(self):
        before = self.snapshot()
        with self.assertRaisesRegex(cp.Refusal, "outside"):
            cp.pack(self.root, self.root / "conaled-textbooks-001.tar.xz", False)
        output = self.base / "conaled-textbooks-001.tar.xz"
        output.write_text("existing owner bytes")
        with self.assertRaisesRegex(cp.Refusal, "overwrite"):
            cp.pack(self.root, output, False)
        self.assertEqual(output.read_text(), "existing owner bytes")
        output.unlink()
        with mock.patch.object(cp, "verify", side_effect=cp.Refusal("synthetic extracted verification failure")):
            with self.assertRaises(cp.Refusal):
                cp.pack(self.root, output, False)
        self.assertFalse(output.exists())
        self.assertEqual(before, self.snapshot())

    def test_publication_rolls_back_failed_output_and_recovers_interruption(self):
        old = (self.root / "checkpoint.json").read_bytes()
        output = self.base / "existing.tar.xz"
        output.write_text("existing")
        archive = self.base / "stage.tar.xz"
        archive.write_text("new")
        with self.assertRaises(OSError):
            cp.publish(self.root, {"checkpoint.json": b"new metadata"}, (archive, output))
        self.assertEqual((self.root / "checkpoint.json").read_bytes(), old)
        self.assertEqual(output.read_text(), "existing")
        self.assertFalse(cp.journal_path(self.root).exists())
        journal = cp.journal_path(self.root)
        journal.mkdir()
        (journal / "old").write_bytes(old)
        (journal / "new").write_bytes(b"interrupted new")
        (self.root / "checkpoint.json").write_bytes(b"interrupted new")
        state = {"root": str(self.root), "output": None, "files": [{"path": "checkpoint.json", "old": "old", "old_sha256": cp.digest(old), "new": "new", "new_sha256": cp.digest(b"interrupted new"), "mode": "0644"}]}
        (journal / "state.json").write_bytes(cp.json_bytes(state))
        cp.recover_publication(self.root)
        self.assertEqual((self.root / "checkpoint.json").read_bytes(), old)
        self.assertFalse(journal.exists())

    def test_missing_inputs_stop_and_cli_rejects_symlink_arguments(self):
        (self.root / "source/refs.json").unlink()
        with self.assertRaisesRegex(cp.Refusal, "STOP.*latest"):
            cp.inspect_payload(self.root, self.policy)
        link = self.base / "link"
        link.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(cp.Refusal, "Symlink argument"):
            cp.cli_path(link)

    def test_concurrent_edit_and_posix_lock_refuse_without_metadata_loss(self):
        output = self.base / "conaled-textbooks-001.tar.xz"
        original_checkpoint = (self.root / "checkpoint.json").read_bytes()
        real_verify = cp.verify
        def edit_after_verification(root, deep=False):
            result = real_verify(root, deep)
            self.write("books/pfds/work/concurrent.md", "Do not discard this concurrent proof draft.\n")
            return result
        with mock.patch.object(cp, "verify", side_effect=edit_after_verification):
            with self.assertRaisesRegex(cp.Refusal, "changed during packaging"):
                cp.pack(self.root, output, False)
        self.assertFalse(output.exists())
        self.assertFalse((self.root / "MANIFEST.json").exists())
        self.assertEqual((self.root / "checkpoint.json").read_bytes(), original_checkpoint)
        self.assertTrue((self.root / "books/pfds/work/concurrent.md").exists())
        with cp.locked(self.root):
            with self.assertRaisesRegex(cp.Refusal, "POSIX lock"):
                with cp.locked(self.root):
                    pass

    def test_growth_wrong_receipt_and_advanced_serial_are_blocked(self):
        self.policy["limits"].update(max_growth_ratio=1.0, max_growth_bytes=16)
        self.write_policy()
        archive, _ = self.first_pack()
        receipt = self.base / "wrong-receipt.json"
        receipt.write_bytes(cp.json_bytes({"method": "alternative_upload", "destination": "owner-root", "library_file_id": "libfile_fixture", "archive_sha256": cp.file_hash(archive), "archive_bytes": archive.stat().st_size}))
        with self.assertRaisesRegex(cp.Refusal, "Only an actual"):
            cp.record_delivery(self.root, archive, receipt=receipt)
        self.mark_uploaded(archive)
        self.write("books/pfds/work/excess.md", "x" * 64)
        with self.assertRaisesRegex(cp.Refusal, "Growth exceeds"):
            cp.pack(self.root, self.base / "conaled-textbooks-002.tar.xz", True)
        checkpoint = cp.read_json(self.root / "checkpoint.json")
        checkpoint["serial"] = 2
        self.write_json("checkpoint.json", checkpoint)
        with self.assertRaisesRegex(cp.Refusal, "already advanced"):
            cp.pack(self.root, self.base / "conaled-textbooks-003.tar.xz", True)

    def test_initial_archive_is_deterministic(self):
        other_parent = self.base / "second"
        other_parent.mkdir()
        other_root = other_parent / "conaled-textbooks"
        shutil.copytree(self.root, other_root)
        archive, _ = self.first_pack()
        other_archive = other_parent / "conaled-textbooks-001.tar.xz"
        cp.pack(other_root, other_archive, False)
        self.assertEqual(cp.file_hash(archive), cp.file_hash(other_archive))


if __name__ == "__main__":
    unittest.main(verbosity=2)

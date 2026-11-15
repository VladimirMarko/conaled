"""Recovery behavior through the public API, with only Lake's process substituted."""
import hashlib
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

import cache_companion as companion


HERE = Path(__file__).resolve().parent


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


class FixtureLake:
    """Independent literal hashes for synthetic byte fixtures, not Lean evidence."""
    values = {b"object fixture\n": "1111111111111111",
              b"interface fixture\n": "2222222222222222",
              b"C fixture\n": "3333333333333333"}

    def identity(self, repo):
        return {"version": "Lean (version 4.35.0, test fixture)",
                "platform": ["test-system", "test-machine", "little"]}

    def hashes(self, paths, scratch):
        return [self.values.get(path.read_bytes(), "0000000000000000")
                for path in paths]


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="companion-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "source"
        self.repo.mkdir()
        git(self.repo, "init", "--quiet")
        files = {".gitignore": ".lake\n", "One.lean": "def one := 1\n",
                 "ProofAudit.lean": "-- deliberately excluded cache target\n",
                 "lean-toolchain": "leanprover/lean4:v4.35.0\n",
                 "lakefile.toml": 'name = "fixture"\n',
                 "lake-manifest.json": '{"packagesDir":".lake/packages","packages":[]}\n',
                 "flake.nix": "fixture flake\n", "flake.lock": "{}\n",
                 "check.sh": "fixture check wrapper\n", "scripts/check.py": "# fixture\n"}
        for name, text in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        for name in ("lake_integrity.py", "lake-output-hashes.lean"):
            shutil.copyfile(HERE / "vendor" / name, self.repo / "scripts" / name)
        git(self.repo, "add", ".")
        git(self.repo, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "-m", "fixture")
        self.binding = {"filename": "source-checkpoint.tar.gz", "sha256": "a" * 64,
                        "size_bytes": 123, "library_file_id": "libfile_fixture",
                        "source_commit": git(self.repo, "rev-parse", "HEAD")}
        self.archive = self.root / "cache.tar.gz"
        self.runtime = FixtureLake()
        self.family()

    def family(self, name="One"):
        stem = name.replace(".", "/")
        for directory, extension, data in (
                ("lib/lean", "olean", b"object fixture\n"),
                ("lib/lean", "ilean", b"interface fixture\n"),
                ("ir", "c", b"C fixture\n")):
            path = self.repo / ".lake/build" / directory / (stem + "." + extension)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        trace = {"synthetic": False, "schemaVersion": "2025-09-10",
                 "outputs": {"m": False, "o": ["1111111111111111.olean"],
                             "i": "2222222222222222.ilean", "c": "3333333333333333.c"},
                 "log": [], "inputs": [], "depHash": "4444444444444444"}
        (self.repo / ".lake/build/lib/lean" / (stem + ".trace")).write_text(json.dumps(trace))

    def create(self):
        return companion.create_companion(self.repo, self.archive, self.binding,
                                          runtime=self.runtime, reserve_bytes=0)

    def clone(self):
        target = self.root / "restored"
        subprocess.run(["git", "clone", "--quiet", str(self.repo), str(target)], check=True)
        return target

    def second_family(self):
        (self.repo / "Two.lean").write_text("def two := 2\n")
        git(self.repo, "add", "Two.lean")
        git(self.repo, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "-m", "second module")
        self.binding["source_commit"] = git(self.repo, "rev-parse", "HEAD")
        self.family("Two")

    def verify(self, result):
        return companion.verify_companion(self.archive, result["sha256"], self.binding,
                                          repo=self.repo, runtime=self.runtime)

    def test_complete_family_survives_round_trip_without_excluded_files(self):
        build = self.repo / ".lake/build"
        (build / "ir/One.setup.json").write_text("do not save setup")
        (build / "lib/lean/One.olean.hash").write_text("do not save sidecar")
        (self.repo / ".lake/verification.json").write_text("not acceptance")
        self.family("ProofAudit")
        result = self.create()
        self.assertEqual(result["modules"], ["One"], result["omitted"])
        verified = companion.verify_companion(self.archive, result["sha256"], self.binding,
                                              repo=self.repo, runtime=self.runtime)
        target = self.clone()
        restored = companion.restore_companion(
            self.archive, target, result["sha256"], self.binding,
            runtime=self.runtime, idle=True)
        self.assertEqual((verified["modules"], restored["modules"]), (["One"], ["One"]))
        self.assertEqual(sorted(str(p.relative_to(target / ".lake/build"))
                                for p in (target / ".lake/build").rglob("*") if p.is_file()),
                         ["ir/One.c", "lib/lean/One.ilean", "lib/lean/One.olean", "lib/lean/One.trace"])
        self.assertFalse((target / ".lake/verification.json").exists())
        self.assertEqual((target / ".lake/build/lib/lean/One.olean").read_bytes(), b"object fixture\n")
        self.assertEqual((build / "ir/One.setup.json").read_text(), "do not save setup")
        self.assertEqual(hashlib.sha256(self.archive.read_bytes()).hexdigest(), result["sha256"])

    def test_restore_refuses_symlinked_cache_directory_without_external_writes(self):
        result = self.create()
        target = self.clone()
        elsewhere = self.root / "outside-cache"
        elsewhere.mkdir()
        (target / ".lake").symlink_to(elsewhere, target_is_directory=True)
        self.assertEqual(git(target, "status", "--porcelain"), "")
        with self.assertRaises(companion.CompanionError):
            companion.restore_companion(self.archive, target, result["sha256"], self.binding,
                                        runtime=self.runtime, idle=True)
        self.assertEqual(list(elsewhere.iterdir()), [])

    def test_no_verified_family_never_publishes_a_useless_archive(self):
        (self.repo / ".lake/build/ir/One.c").unlink()
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertFalse(self.archive.exists())

    def test_verification_rejects_an_incompatible_clean_checkout(self):
        result = self.create()
        target = self.clone()
        (target / "One.lean").write_text("def one := 2\n")
        git(target, "add", "One.lean")
        git(target, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "--quiet", "-m", "different source")
        with self.assertRaises(companion.CompanionError):
            companion.verify_companion(self.archive, result["sha256"], self.binding,
                                       repo=target, runtime=self.runtime)
        self.assertFalse((target / ".lake").exists())

    def test_cli_requires_explicit_idle_acknowledgement_before_any_runtime(self):
        result = subprocess.run(
            [sys.executable, "-B", str(HERE / "cache_companion.py"), "restore",
             "--repo", str(self.repo), "--archive", str(self.archive),
             "--binding", str(self.root / "not-read.json"), "--sha256", "a" * 64],
            capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--idle-checkout", result.stderr)
        self.assertFalse(self.archive.exists())

    def test_incomplete_or_untrusted_family_is_omitted_whole(self):
        self.second_family()
        c_file = self.repo / ".lake/build/ir/One.c"
        trace = self.repo / ".lake/build/lib/lean/One.trace"
        for problem in ("missing", "hash mismatch", "malformed trace", "symlink", "hardlink"):
            with self.subTest(problem=problem):
                c_file.unlink(missing_ok=True)
                self.family()
                self.archive = self.root / (problem.replace(" ", "-") + ".tar.gz")
                if problem == "missing":
                    c_file.unlink()
                elif problem == "hash mismatch":
                    c_file.write_bytes(b"wrong object bytes")
                elif problem == "malformed trace":
                    trace.write_text('{"schemaVersion":"unknown"}')
                else:
                    outside = self.root / (problem + "-target")
                    outside.write_bytes(b"C fixture\n")
                    c_file.unlink()
                    if problem == "symlink":
                        c_file.symlink_to(outside)
                    else:
                        import os
                        os.link(outside, c_file)
                result = self.create()
                self.assertEqual(result["modules"], ["Two"])
                self.assertIn("One", result["omitted"])
                self.assertEqual(self.verify(result)["modules"], ["Two"])

    def test_family_changed_during_hashing_is_omitted_whole(self):
        self.second_family()
        live = self.repo / ".lake/build/lib/lean/One.olean"

        class ChangingLake(FixtureLake):
            def hashes(self, paths, scratch):
                result = super().hashes(paths, scratch)
                live.write_bytes(b"a later build output")
                return result

        self.runtime = ChangingLake()
        result = self.create()
        self.assertEqual(result["modules"], ["Two"])
        self.assertIn("One", result["omitted"])
        self.assertEqual(live.read_bytes(), b"a later build output")

    def test_source_change_during_hashing_aborts_without_publication(self):
        source = self.repo / "One.lean"

        class ChangingLake(FixtureLake):
            def hashes(self, paths, scratch):
                result = super().hashes(paths, scratch)
                source.write_text("def one := 999\n")
                return result

        self.runtime = ChangingLake()
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertFalse(self.archive.exists())

    def test_archive_and_nonempty_cache_are_never_overwritten(self):
        result = self.create()
        original = self.archive.read_bytes()
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertEqual(self.archive.read_bytes(), original)
        target = self.clone()
        protected = target / ".lake/build/user-output"
        protected.parent.mkdir(parents=True)
        protected.write_bytes(b"keep this")
        with self.assertRaises(companion.CompanionError):
            companion.restore_companion(self.archive, target, result["sha256"], self.binding,
                                        runtime=self.runtime, idle=True)
        self.assertEqual(protected.read_bytes(), b"keep this")

    def test_source_checkpoint_binding_must_match(self):
        self.binding["source_commit"] = "b" * 40
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertFalse(self.archive.exists())

    def test_corrupt_extra_linked_and_duplicate_members_are_rejected(self):
        result = self.create()
        with tarfile.open(self.archive, "r:gz") as source:
            original = [(entry, source.extractfile(entry).read()) for entry in source.getmembers()]
        for problem in ("payload corruption", "extra", "traversal", "absolute", "symlink", "hardlink", "duplicate"):
            with self.subTest(problem=problem):
                forged = self.root / (problem.replace(" ", "-") + ".tar.gz")
                with tarfile.open(forged, "w:gz") as output:
                    for entry, data in original:
                        if problem == "payload corruption" and entry.name.endswith(".olean"):
                            data = b"x" * len(data)
                        output.addfile(entry, io.BytesIO(data))
                    if problem != "payload corruption":
                        name = {"extra": "unlisted", "traversal": "../escaped",
                                "absolute": "/escaped", "symlink": "link", "hardlink": "link",
                                "duplicate": "manifest.json"}[problem]
                        entry = tarfile.TarInfo(name)
                        if problem in ("symlink", "hardlink"):
                            entry.type = tarfile.SYMTYPE if problem == "symlink" else tarfile.LNKTYPE
                            entry.linkname = "../escaped"
                            output.addfile(entry)
                        else:
                            entry.size = 1
                            output.addfile(entry, io.BytesIO(b"x"))
                digest = hashlib.sha256(forged.read_bytes()).hexdigest()
                with self.assertRaises(companion.CompanionError):
                    companion.verify_companion(forged, digest, self.binding,
                                               repo=self.repo, runtime=self.runtime)
        self.assertFalse((self.root / "escaped").exists())
        with self.assertRaises(companion.CompanionError):
            companion.verify_companion(self.archive, "0" * 64, self.binding,
                                       repo=self.repo, runtime=self.runtime)

    def test_all_declared_module_parts_and_optional_outputs_round_trip(self):
        trace_path = self.repo / ".lake/build/lib/lean/One.trace"
        trace = json.loads(trace_path.read_text())
        trace["outputs"]["m"] = True
        additions = [("olean.server", "4", None), ("olean.private", "5", None),
                     ("ir.sig", "6", "rs"), ("ir", "7", "r"),
                     ("bc", "8", "b"), ("ltar", "9", "l")]
        self.runtime.values = dict(self.runtime.values)
        for extension, digit, key in additions:
            data = (extension + " fixture\n").encode()
            self.runtime.values[data] = digit * 16
            description = digit * 16 + "." + extension
            if key is None:
                trace["outputs"]["o"].append(description)
            else:
                trace["outputs"][key] = description
            directory = "ir" if extension in ("bc", "ltar") else "lib/lean"
            (self.repo / ".lake/build" / directory / ("One." + extension)).write_bytes(data)
        trace_path.write_text(json.dumps(trace))
        result = self.create()
        verified = self.verify(result)
        self.assertEqual(sorted(verified["manifest"]["families"]["One"]),
                         ["ir/One.bc", "ir/One.c", "ir/One.ltar", "lib/lean/One.ilean",
                          "lib/lean/One.ir", "lib/lean/One.ir.sig", "lib/lean/One.olean",
                          "lib/lean/One.olean.private", "lib/lean/One.olean.server", "lib/lean/One.trace"])

    def test_capture_never_stages_or_publishes_inside_the_source_checkout(self):
        self.archive = self.repo / ".lake/build/forbidden.tar.gz"
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertFalse(self.archive.exists())
        self.assertEqual(list((self.repo / ".lake/build").glob("cache-companion-*")), [])

    @unittest.skipUnless(Path("/proc/self/statm").exists(), "Linux address-space accounting test")
    def test_capture_streams_large_payload_with_bounded_python_memory(self):
        # A public resource contract: 16 MiB of payload fits in 24 MiB of
        # additional Python address space. Lake itself is the external boundary.
        with (self.repo / ".lake/build/lib/lean/One.olean").open("wb") as output:
            output.truncate(16 * 1024 * 1024)
        binding = self.root / "binding.json"
        binding.write_text(json.dumps(self.binding))
        program = r'''
import json, os, resource, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import cache_companion
from test_cache_companion import FixtureLake
class BoundedLake(FixtureLake):
    def hashes(self, paths, scratch):
        return [{'.olean':'1111111111111111', '.ilean':'2222222222222222',
                 '.c':'3333333333333333'}[path.suffix] for path in paths]
current = int(Path('/proc/self/statm').read_text().split()[0]) * os.sysconf('SC_PAGE_SIZE')
limit = current + 24 * 1024 * 1024
resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
result = cache_companion.create_companion(Path(sys.argv[2]), Path(sys.argv[3]),
    json.loads(Path(sys.argv[4]).read_text()), runtime=BoundedLake(), reserve_bytes=0)
assert result['modules'] == ['One']
print('bounded-memory capture and extraction passed')
'''
        result = subprocess.run([sys.executable, "-B", "-c", program, str(HERE), str(self.repo),
                                 str(self.archive), str(binding)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_oversized_family_is_omitted_without_reading_its_payload(self):
        self.second_family()
        with (self.repo / ".lake/build/lib/lean/One.olean").open("wb") as output:
            output.truncate(128 * 1024 * 1024 + 1)
        result = self.create()
        self.assertEqual(result["modules"], ["Two"])
        self.assertIn("One", result["omitted"])

    def test_malformed_hash_result_aborts_without_touching_live_files(self):
        live = self.repo / ".lake/build/lib/lean/One.olean"
        original = live.read_bytes()

        class BadLake(FixtureLake):
            def hashes(self, paths, scratch):
                return ["not a hash"]

        self.runtime = BadLake()
        with self.assertRaises(companion.CompanionError):
            self.create()
        self.assertFalse(self.archive.exists())
        self.assertEqual(live.read_bytes(), original)

    def test_fifo_family_is_omitted_promptly_while_a_good_family_survives(self):
        self.second_family()
        trace = self.repo / ".lake/build/lib/lean/One.trace"
        trace.unlink()
        os.mkfifo(trace)
        binding = self.root / "fifo-binding.json"
        binding.write_text(json.dumps(self.binding))
        program = r'''
import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import cache_companion
from test_cache_companion import FixtureLake
result = cache_companion.create_companion(Path(sys.argv[2]), Path(sys.argv[3]),
    json.loads(Path(sys.argv[4]).read_text()), runtime=FixtureLake(), reserve_bytes=0)
assert result['modules'] == ['Two'] and 'One' in result['omitted']
print('FIFO family omitted without blocking')
'''
        result = subprocess.run([sys.executable, "-B", "-c", program, str(HERE), str(self.repo),
                                 str(self.archive), str(binding)], capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(trace.is_fifo())

    def test_fifo_archive_is_rejected_promptly(self):
        os.mkfifo(self.archive)
        binding = self.root / "fifo-binding.json"
        binding.write_text(json.dumps(self.binding))
        program = r'''
import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
import cache_companion
from test_cache_companion import FixtureLake
try:
    cache_companion.verify_companion(Path(sys.argv[3]), 'a' * 64,
        json.loads(Path(sys.argv[4]).read_text()), repo=Path(sys.argv[2]), runtime=FixtureLake())
except cache_companion.CompanionError:
    print('FIFO archive rejected without blocking')
else:
    raise AssertionError('FIFO archive was accepted')
'''
        result = subprocess.run([sys.executable, "-B", "-c", program, str(HERE), str(self.repo),
                                 str(self.archive), str(binding)], capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(self.archive.is_fifo())


if __name__ == "__main__":
    unittest.main()

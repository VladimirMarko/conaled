#!/usr/bin/env python3
"""Optional, unaccepted project-cache data tied to a complete source checkpoint.

Public boundaries: create_companion, verify_companion, restore_companion.
Only the external Lake runtime is replaceable for synthetic tests. The CLI
always uses the pinned, byte-identified Lake helper.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
from datetime import datetime, timezone
from contextlib import contextmanager

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
GUARD_SHA = "293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f"
HELPER_SHA = "fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b"
INPUT_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "flake.nix",
               "flake.lock", "check.sh", "scripts/check.py", "scripts/lake_integrity.py",
               "scripts/lake-output-hashes.lean")
MODULE = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
MAX_FILE = 128 * 1024 * 1024
MAX_COHORT = 750_000_000
MAX_MANIFEST = 8 * 1024 * 1024


class CompanionError(RuntimeError):
    pass


class CaptureBudgetError(CompanionError):
    pass


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _git(repo, *args):
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


def _guard():
    path = HERE / "vendor/lake_integrity.py"
    if _sha(path.read_bytes()) != GUARD_SHA:
        raise CompanionError("The vendored integrity adapter changed")
    if _sha((HERE / "vendor/lake-output-hashes.lean").read_bytes()) != HELPER_SHA:
        raise CompanionError("The vendored Lake hash helper changed")
    spec = importlib.util.spec_from_file_location("companion_pinned_guard", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _identity(repo, runtime):
    if _git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise CompanionError("Source checkout is not clean")
    guard = _guard()
    guard.validate_layout(repo)
    files = {name: _sha((repo / name).read_bytes()) for name in INPUT_FILES}
    if files["scripts/lake_integrity.py"] != GUARD_SHA or files["scripts/lake-output-hashes.lean"] != HELPER_SHA:
        raise CompanionError("Project integrity adapter differs from this companion version")
    tracked = set(_git(repo, "ls-files", "-z").split("\0"))
    sources = list(repo.glob("*.lean"))
    for directory in ("SquareKit", "Applications", "Examples"):
        sources.extend((repo / directory).rglob("*.lean"))
    modules = {}
    for path in sorted(sources):
        name = path.relative_to(repo).as_posix()
        if name == "ProofAudit.lean":
            continue
        if name not in tracked or path.is_symlink() or not path.is_file():
            raise CompanionError("Untracked or nonregular integrated source: " + name)
        module = name[:-5].replace("/", ".")
        if not re.fullmatch(MODULE, module):
            raise CompanionError("Unsupported source module name: " + module)
        modules[module] = _sha(path.read_bytes())
    manifest = json.loads((repo / "lake-manifest.json").read_text())
    if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
        raise CompanionError("Unsupported dependency directory")
    dependencies = {}
    for package in manifest["packages"]:
        name, revision = package["name"], package["rev"]
        if (package.get("type") != "git" or not re.fullmatch(r"[A-Za-z0-9_-]+", name)
                or not re.fullmatch(r"[0-9a-f]{40}", revision)):
            raise CompanionError("Unsupported dependency pin")
        dependency = repo / ".lake/packages" / name
        if (_git(dependency, "rev-parse", "HEAD") != revision
                or _git(dependency, "status", "--porcelain=v1", "--untracked-files=all")):
            raise CompanionError("Dependency is dirty or differs from its pin: " + name)
        dependencies[name] = revision
    return {"commit": _git(repo, "rev-parse", "HEAD"),
            "tree": _git(repo, "rev-parse", "HEAD^{tree}"),
            "files": files, "sources": modules, "dependencies": dependencies,
            "runtime": runtime.identity(repo)}


def _signature(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
            info.st_ctime_ns, info.st_nlink)


def _free_bytes(path):
    info = os.statvfs(path)
    # Root can use the filesystem's reserved blocks; f_bavail alone reports
    # zero on this workspace while substantial root-writable space remains.
    blocks = info.f_bfree if os.geteuid() == 0 else info.f_bavail
    return blocks * info.f_frsize


@contextmanager
def _regular_file(root, relative, *, maximum=MAX_FILE):
    """Anchor a bounded regular file and check its identity across consumption."""
    parts = PurePosixPath(relative).parts
    if not parts or any(part in ("", ".", "..") for part in parts) or relative.startswith("/"):
        raise CompanionError("Unsafe relative path")
    directory = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in parts[:-1]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
            os.close(directory)
            directory = child
        # A FIFO must reach the descriptor type check without waiting for a
        # writer. O_NONBLOCK has no effect on ordinary regular-file reads.
        descriptor = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
        try:
            before = os.fstat(descriptor)
            if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or before.st_size > maximum:
                raise CompanionError("Not a singly linked, bounded regular file: " + relative)
            yield descriptor, before
            after = os.fstat(descriptor)
            current = os.stat(parts[-1], dir_fd=directory, follow_symlinks=False)
            if _signature(before) != _signature(after) or _signature(after) != _signature(current):
                raise CompanionError("File changed while being read: " + relative)
        finally:
            os.close(descriptor)
    finally:
        os.close(directory)


def _read(root, relative):
    """Small trace read; large artifact copying uses the streaming path below."""
    with _regular_file(root, relative, maximum=MAX_MANIFEST) as (descriptor, before):
        with os.fdopen(os.dup(descriptor), "rb") as source:
            data = source.read(MAX_MANIFEST + 1)
        if len(data) > MAX_MANIFEST:
            raise CompanionError("Trace grew beyond its bound")
    return data, _signature(before)


def _check_budget(total, size, directory, reserve):
    if total + size > MAX_COHORT:
        raise CaptureBudgetError("Cohort byte budget exceeded")
    if _free_bytes(directory) < 3 * (total + size) + reserve:
        raise CaptureBudgetError("Insufficient disk reserve for checked capture")


def _copy_artifact(root, relative, target, total, directory, reserve):
    """Independent copy and SHA256 in one bounded-memory pass."""
    created = False
    try:
        with _regular_file(root, relative) as (descriptor, before):
            _check_budget(total, before.st_size, directory, reserve)
            digest, count = hashlib.sha256(), 0
            with target.open("xb") as output:
                created = True
                while chunk := os.read(descriptor, 1024 * 1024):
                    count += len(chunk)
                    if count > MAX_FILE or total + count > MAX_COHORT:
                        raise CompanionError("Artifact grew beyond its byte bound")
                    digest.update(chunk)
                    output.write(chunk)
        return {"size_bytes": count, "sha256": digest.hexdigest()}, _signature(before)
    except BaseException:
        if created:
            target.unlink(missing_ok=True)
        raise


def _stream_sha(source):
    digest = hashlib.sha256()
    while chunk := source.read(1024 * 1024):
        digest.update(chunk)
    return digest.hexdigest()


def _file_sha(path):
    with path.open("rb") as source:
        return _stream_sha(source)


@contextmanager
def _checked_tar(archive, expected_sha256):
    """Hash and parse the same anchored file, with stable identity throughout."""
    archive = Path(archive).absolute()
    if not isinstance(expected_sha256, str) or not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
        raise CompanionError("Invalid independently recorded archive digest")
    with _regular_file(archive.parent, archive.name, maximum=MAX_COHORT + MAX_MANIFEST) as (descriptor, _):
        with os.fdopen(os.dup(descriptor), "rb") as source:
            if _stream_sha(source) != expected_sha256:
                raise CompanionError("Archive SHA256 mismatch")
            source.seek(0)
            with tarfile.open(fileobj=source, mode="r:gz") as contents:
                yield contents


def _descriptions(trace):
    """Preselect fixed paths; the unchanged guard independently checks copies."""
    data = json.loads(trace)
    if (not isinstance(data, dict) or data.get("schemaVersion") != "2025-09-10"
            or data.get("synthetic") is not False or not isinstance(data.get("inputs"), list)
            or not re.fullmatch(r"[0-9a-f]{16}", str(data.get("depHash", "")))):
        raise CompanionError("Unsupported or incomplete trace")
    outputs = data.get("outputs")
    if (not isinstance(outputs, dict) or type(outputs.get("m")) is not bool
            or set(outputs) - {"m", "o", "i", "rs", "r", "c", "b", "l"}):
        raise CompanionError("Unsupported output descriptions")
    parts = outputs.get("o")
    if not isinstance(parts, list) or len(parts) != (3 if outputs["m"] else 1):
        raise CompanionError("Unsupported olean parts")
    values = list(zip(("olean", "olean.server", "olean.private"), parts))
    values += [("ilean", outputs.get("i")), ("c", outputs.get("c"))]
    for key, extension in (("rs", "ir.sig"), ("r", "ir"), ("b", "bc"), ("l", "ltar")):
        if key in outputs or (outputs["m"] and key in ("rs", "r")):
            values.append((extension, outputs.get(key)))
    for extension, value in values:
        if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{16}\." + re.escape(extension), value):
            raise CompanionError("Unsupported artifact identity")
    return {extension: value[:16] for extension, value in values}


def _relative(name, extension):
    directory = "ir" if extension in ("c", "bc", "ltar") else "lib/lean"
    return directory + "/" + name.replace(".", "/") + "." + extension


def _binding(binding):
    if (set(binding) != {"filename", "sha256", "size_bytes", "library_file_id", "source_commit"}
            or not re.fullmatch(r"[A-Za-z0-9_.-]+\.tar\.gz", binding["filename"])
            or not re.fullmatch(r"[0-9a-f]{64}", binding["sha256"])
            or type(binding["size_bytes"]) is not int or binding["size_bytes"] <= 0
            or not re.fullmatch(r"libfile_[A-Za-z0-9_]+", binding["library_file_id"])
            or not re.fullmatch(r"[0-9a-f]{40}", binding["source_commit"])):
        raise CompanionError("Invalid complete source-checkpoint binding")


def create_companion(repo, archive, binding, *, runtime, reserve_bytes=500_000_000):
    """Capture complete stable families; publish only after an extraction check."""
    repo, archive = Path(repo).resolve(), Path(archive).absolute()
    _binding(binding)
    archive = archive.parent.resolve(strict=True) / archive.name
    if archive.parent.is_relative_to(repo):
        raise CompanionError("Recovery staging and archives must be outside the source checkout")
    if archive.exists() or archive.is_symlink():
        raise CompanionError("Refusing to overwrite an existing archive")
    if reserve_bytes < 0:
        raise CompanionError("Disk reserve cannot be negative")
    before = _identity(repo, runtime)
    if before["commit"] != binding["source_commit"]:
        raise CompanionError("Source checkpoint identifies a different commit")
    started = datetime.now(timezone.utc).isoformat()
    guard = _guard()
    with tempfile.TemporaryDirectory(prefix="cache-companion-", dir=archive.parent) as temporary:
        stage = Path(temporary) / "cohort"
        stage.mkdir()
        build = stage / ".lake/build"
        build.mkdir(parents=True)
        families, omitted, live = {}, {}, {}
        total = 0
        for name in before["sources"]:
            files, identities = {}, {}
            try:
                trace_path = _relative(name, "trace")
                trace, identity = _read(repo, ".lake/build/" + trace_path)
                descriptions = _descriptions(trace)
                for relative, expected in [(trace_path, None)] + [
                        (_relative(name, extension), value) for extension, value in descriptions.items()]:
                    target = build / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if expected is None:
                        _check_budget(total, len(trace), archive.parent, reserve_bytes)
                        with target.open("xb") as output:
                            output.write(trace)
                        info, signature = {"size_bytes": len(trace), "sha256": _sha(trace)}, identity
                    else:
                        info, signature = _copy_artifact(repo, ".lake/build/" + relative,
                                                         target, total, archive.parent, reserve_bytes)
                    files[relative] = {**info, "lake_hash": expected}
                    identities[relative] = signature
                    total += info["size_bytes"]
                actual = {str(path.relative_to(build)): expected
                          for path, expected in guard.expected_artifacts(stage, name)}
                if actual != {path: info["lake_hash"] for path, info in files.items()
                              if info["lake_hash"] is not None}:
                    raise CompanionError("Private guard and trace descriptions disagree")
                families[name], live[name] = files, identities
            except (OSError, ValueError, TypeError, CompanionError) as error:
                if isinstance(error, CaptureBudgetError):
                    raise
                omitted[name] = str(error)
                for relative, info in files.items():
                    (build / relative).unlink(missing_ok=True)
                    total -= info["size_bytes"]
        entries = [(name, relative, info["lake_hash"])
                   for name, files in families.items() for relative, info in files.items()
                   if info["lake_hash"] is not None]
        hash_sizes = [families[name][relative]["size_bytes"] for name, relative, _ in entries]
        if entries:
            hashes = runtime.hashes([build / path for _, path, _ in entries], Path(temporary) / "hash-check")
            if (not isinstance(hashes, list) or len(hashes) != len(entries)
                    or any(not isinstance(h, str) or not re.fullmatch(r"[0-9a-f]{16}", h) for h in hashes)):
                raise CompanionError("Pinned Lake helper returned malformed results")
            for (name, relative, expected), actual in zip(entries, hashes):
                if actual != expected:
                    omitted[name] = "Pinned Lake output hash mismatch: " + relative
        for name, files in list(families.items()):
            try:
                for relative, info in files.items():
                    if info["lake_hash"] is None:
                        data, signature = _read(repo, ".lake/build/" + relative)
                        if _sha(data) != info["sha256"]:
                            raise CompanionError("Live trace changed during capture: " + relative)
                    else:
                        with _regular_file(repo, ".lake/build/" + relative) as (_, current):
                            signature = _signature(current)
                    if signature != live[name][relative]:
                        raise CompanionError("Live family changed during capture: " + relative)
            except (OSError, CompanionError) as error:
                omitted[name] = str(error)
            if name in omitted:
                for relative, info in files.items():
                    (build / relative).unlink()
                    total -= info["size_bytes"]
                del families[name]
        if _identity(repo, runtime) != before:
            raise CompanionError("Source, configuration, dependency or compiler identity changed")
        if not families:
            raise CompanionError("No complete verified module families remain: " + json.dumps(omitted, sort_keys=True))
        manifest = {"schema_version": 1, "kind": "unaccepted-conaled-project-cache",
                    "source_checkpoint": binding, "inputs": before,
                    "capture_started_utc": started, "capture_completed_utc": datetime.now(timezone.utc).isoformat(),
                    "families": families, "omitted": omitted, "payload_bytes": total,
                    "guard_sha256": GUARD_SHA, "helper_sha256": HELPER_SHA,
                    "hash_check": {"artifact_count": len(entries), "total_bytes": sum(hash_sizes),
                                   "largest_artifact_bytes": max(hash_sizes, default=0),
                                   "runtime_evidence": getattr(runtime, "last_hash_evidence",
                                       {"test_boundary_substitute": type(runtime).__name__})},
                    "limitations": "Trace agreement is not source provenance or hostile-data authentication; all acceptance gates remain required."}
        manifest_path = stage / "manifest.json"
        _json(manifest_path, manifest)
        packed = Path(temporary) / "checked.tar.gz"
        with tarfile.open(packed, "w:gz", compresslevel=1) as output:
            output.add(manifest_path, arcname="manifest.json", recursive=False)
            for files in families.values():
                for relative in files:
                    output.add(build / relative, arcname="build/" + relative, recursive=False)
        digest = _file_sha(packed)
        verified = verify_companion(packed, digest, binding, repo=repo, runtime=runtime)
        # Atomic, no-clobber publication of the already checked archive. This
        # temporary archive link never shares a mutable project output inode.
        os.link(packed, archive)
        packed.unlink()
        return {"file": str(archive), "sha256": digest, "size_bytes": archive.stat().st_size,
                "modules": verified["modules"], "omitted": omitted,
                "payload_bytes": total, "archive_restore_check": "passed"}


def _extract_checked(archive, expected_sha256, binding, destination, expected_inputs):
    _binding(binding)
    with _checked_tar(archive, expected_sha256) as source:
        members, declared_bytes = [], 0
        for member in source:
            maximum = MAX_MANIFEST if member.name == "manifest.json" else MAX_FILE
            if (not member.isfile() or not 0 <= member.size <= maximum
                    or len(members) >= 10 * len(expected_inputs["sources"]) + 1):
                raise CompanionError("Archive has unbounded or nonregular members")
            declared_bytes += member.size
            if declared_bytes > MAX_COHORT + MAX_MANIFEST:
                raise CompanionError("Archive expands beyond the cohort byte bound")
            members.append(member)
        names = [member.name for member in members]
        if len(names) != len(set(names)) or any(not member.isfile() for member in members):
            raise CompanionError("Archive has duplicate or nonregular members")
        if "manifest.json" not in names:
            raise CompanionError("Archive has no manifest")
        stream = source.extractfile("manifest.json")
        manifest = json.load(stream)
        if (manifest.get("schema_version") != 1 or manifest.get("kind") != "unaccepted-conaled-project-cache"
                or manifest.get("source_checkpoint") != binding
                or manifest.get("guard_sha256") != GUARD_SHA or manifest.get("helper_sha256") != HELPER_SHA):
            raise CompanionError("Unsupported manifest or source-checkpoint mismatch")
        if (manifest.get("inputs") != expected_inputs
                or expected_inputs["commit"] != binding["source_commit"]):
            raise CompanionError("Source/configuration/dependency/compiler/platform identity mismatch")
        expected = {}
        for name, files in manifest["families"].items():
            if not re.fullmatch(MODULE, name) or name not in manifest["inputs"]["sources"]:
                raise CompanionError("Invalid source module in manifest")
            for relative, info in files.items():
                if relative not in {_relative(name, ext) for ext in
                                    ("trace", "olean", "olean.server", "olean.private", "ilean", "c", "ir", "ir.sig", "bc", "ltar")}:
                    raise CompanionError("Unsafe or undeclared archive path")
                expected["build/" + relative] = info
        if set(names) != {"manifest.json", *expected}:
            raise CompanionError("Archive members differ from manifest")
        payload_bytes = sum(member.size for member in members if member.name != "manifest.json")
        if (payload_bytes > MAX_COHORT or manifest.get("payload_bytes") != payload_bytes
                or not manifest["families"]):
            raise CompanionError("Invalid or empty payload byte inventory")
        if _free_bytes(destination) < payload_bytes + 500_000_000:
            raise CompanionError("Insufficient disk reserve for checked extraction")
        for member in members:
            if member.name == "manifest.json":
                continue
            info = expected[member.name]
            if (type(info["size_bytes"]) is not int or member.size != info["size_bytes"]
                    or not isinstance(info["sha256"], str)
                    or not re.fullmatch(r"[0-9a-f]{64}", info["sha256"])):
                raise CompanionError("Archive file size mismatch")
            target = destination / ".lake" / member.name
            target.parent.mkdir(parents=True, exist_ok=True)
            digest, count = hashlib.sha256(), 0
            with source.extractfile(member) as payload, target.open("xb") as output:
                while chunk := payload.read(1024 * 1024):
                    digest.update(chunk)
                    output.write(chunk)
                    count += len(chunk)
            if digest.hexdigest() != info["sha256"] or count != member.size:
                raise CompanionError("Archive payload SHA256 mismatch")
    guard = _guard()
    for name, files in manifest["families"].items():
        trace = (destination / ".lake/build" / _relative(name, "trace")).read_bytes()
        _descriptions(trace)
        actual = {str(path.relative_to(destination / ".lake/build")): value
                  for path, value in guard.expected_artifacts(destination, name)}
        described = {path: info["lake_hash"] for path, info in files.items() if info["lake_hash"] is not None}
        if actual != described or len(files) != len(actual) + 1:
            raise CompanionError("Archive does not contain a complete consistent module family")
    return manifest


def verify_companion(archive, expected_sha256, binding, *, repo, runtime):
    """Check the clean target identity and every archived byte and family."""
    archive = Path(archive)
    repo = Path(repo).resolve()
    before = _identity(repo, runtime)
    with tempfile.TemporaryDirectory(prefix="cache-verify-", dir=archive.parent) as temporary:
        manifest = _extract_checked(archive, expected_sha256, binding, Path(temporary), before)
        if _identity(repo, runtime) != before:
            raise CompanionError("Target inputs changed during verification")
    return {"modules": sorted(manifest["families"]), "manifest": manifest,
            "archive_restore_check": "passed"}


def restore_companion(archive, repo, expected_sha256, binding, *, runtime, idle=False):
    """Install verified ordinary files only into an explicitly idle empty cache."""
    repo = Path(repo).resolve()
    if not idle:
        raise CompanionError("Explicit idle-checkout acknowledgement is required")
    build = repo / ".lake/build"
    for directory in (build.parent, build):
        if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
            raise CompanionError("Restore destination contains a link or nondirectory")
    if build.exists() and any(build.iterdir()):
        raise CompanionError("Refusing a nonempty project build destination")
    before = _identity(repo, runtime)
    with tempfile.TemporaryDirectory(prefix="cache-restore-", dir=repo.parent) as temporary:
        stage = Path(temporary)
        manifest = _extract_checked(archive, expected_sha256, binding, stage, before)
        if before != manifest["inputs"] or _identity(repo, runtime) != before:
            raise CompanionError("Restore source/configuration/dependency/compiler/platform mismatch")
        # Anchor the installation to an ordinary .lake directory. Never let
        # shutil.move merge into a destination that appeared during checking.
        root_fd = os.open(repo, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            try:
                os.mkdir(".lake", dir_fd=root_fd)
            except FileExistsError:
                pass
            cache_fd = os.open(".lake", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=root_fd)
            try:
                try:
                    current = os.stat("build", dir_fd=cache_fd, follow_symlinks=False)
                except FileNotFoundError:
                    current = None
                if current is not None:
                    if not stat.S_ISDIR(current.st_mode):
                        raise CompanionError("Restore destination changed to a nondirectory")
                    os.rmdir("build", dir_fd=cache_fd)  # atomically refuses a nonempty directory
                os.rename(stage / ".lake/build", "build", dst_dir_fd=cache_fd)
            finally:
                os.close(cache_fd)
        except OSError as error:
            raise CompanionError("Idle cache installation failed: " + str(error)) from error
        finally:
            os.close(root_fd)
    return {"modules": sorted(manifest["families"]), "installed": str(build),
            "acceptance": False, "next": "Run the unchanged complete candidate validation and review sequence."}


class PinnedLake:
    """The installed compiler and unchanged helper; no project compilation."""
    def __init__(self, repo):
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=repo, text=True).strip()
        self.lean = str(Path(prefix).resolve() / "bin/lean")

    def identity(self, repo):
        toolchain = (Path(repo) / "lean-toolchain").read_text().strip()
        version = subprocess.check_output([self.lean, "--version"], cwd=repo, text=True).strip()
        if toolchain != "leanprover/lean4:v4.35.0" or "version 4.35.0," not in version:
            raise CompanionError("Companion requires the recorded pinned Lean 4.35.0 toolchain")
        return {"version": version, "platform": [platform.system(), platform.machine(), sys.byteorder]}

    def hashes(self, paths, scratch):
        scratch.mkdir()
        helper = scratch / "lake-output-hashes.lean"
        helper.write_bytes((HERE / "vendor/lake-output-hashes.lean").read_bytes())
        if _sha(helper.read_bytes()) != HELPER_SHA:
            raise CompanionError("Private helper identity mismatch")
        paths_file = scratch / "paths.json"
        _json(paths_file, [str(path) for path in paths])
        env = os.environ.copy()
        env.pop("LEAN_PATH", None)
        env["LEAN_NUM_THREADS"] = "1"
        command = [self.lean, "-j", "1", "--run", str(helper), str(paths_file)]
        started = time.monotonic()
        result = subprocess.run(command,
                                cwd=scratch, env=env, capture_output=True, text=True, timeout=60)
        self.last_hash_evidence = {"command": command, "working_directory": str(scratch),
                                   "returncode": result.returncode, "elapsed_seconds": time.monotonic() - started,
                                   "file_count": len(paths), "worker_count": 1, "timeout_seconds": 60,
                                   "helper_sha256": HELPER_SHA, "stdout_sha256": _sha(result.stdout.encode())}
        if result.returncode:
            raise CompanionError("Pinned Lake hashing failed: " + result.stdout + result.stderr)
        return json.loads(result.stdout)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("capture", "verify", "restore"):
        sub = commands.add_parser(command)
        sub.add_argument("--repo", type=Path, required=True, help="Clean isolated conaled checkout")
        sub.add_argument("--archive", type=Path, required=True)
        sub.add_argument("--binding", type=Path, required=True, help="Exact uploaded source-checkpoint binding JSON")
        if command != "capture":
            sub.add_argument("--sha256", required=True, help="Whole-archive digest from its independent receipt")
        if command == "restore":
            sub.add_argument("--idle-checkout", action="store_true", required=True,
                             help="Acknowledge that no build/editor process writes this isolated checkout")
    args = parser.parse_args(argv)
    try:
        binding = json.loads(args.binding.read_text())
        runtime = PinnedLake(args.repo)
        if args.command == "capture":
            result = create_companion(args.repo, args.archive, binding, runtime=runtime)
        elif args.command == "verify":
            result = verify_companion(args.archive, args.sha256, binding, repo=args.repo, runtime=runtime)
        else:
            result = restore_companion(args.archive, args.repo, args.sha256, binding,
                                       runtime=runtime, idle=args.idle_checkout)
        # Complete per-file/family evidence lives inside the checked archive.
        # Keep the terminal result small enough to expose/upload immediately.
        result.pop("manifest", None)
        result["module_count"] = len(result.pop("modules"))
        if "omitted" in result:
            result["omitted_count"] = len(result.pop("omitted"))
        print(json.dumps(result, sort_keys=True))
        return 0
    except (CompanionError, OSError, ValueError, TypeError, KeyError,
            subprocess.SubprocessError, tarfile.TarError) as error:
        print("Cache companion refused: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

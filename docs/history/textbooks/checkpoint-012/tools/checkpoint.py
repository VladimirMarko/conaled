#!/usr/bin/env python3
"""Checkpoint packaging and offline recovery; Python 3.9+ and Git, never Lean."""
import argparse
import contextlib
import copy
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile

TOP_DIRS = {"docs", "reference", "source", "books", "support", "provenance", "tools"}
TOP_FILES = {"README.md", "AGENTS.md", "checkpoint.json", "policy.json", "MANIFEST.json"}
BAD_PARTS = {".git", ".lake", ".cache", "__pycache__", "node_modules", "downloads", "download", "toolchains", "toolchain", "runtime-cache"}
ARCHIVE_SUFFIXES = (".zip", ".tar", ".tar.gz", ".tgz", ".gz", ".xz", ".bz2", ".7z", ".rar", ".zst", ".npz", ".whl", ".jar", ".bundle")
PARTIAL_SUFFIXES = (".part", ".partial", ".download", ".crdownload", ".tmp")
BUILD_SUFFIXES = (".olean", ".ilean", ".o", ".so", ".a", ".c.o.export", ".pyc")
BOOKS = {"vfa", "fdsa", "pfds"}
OID = re.compile(r"^[0-9a-f]{40}$")
STOP = "STOP: request the user's latest checkpoint archive before any project work, cleanup, or delegation; verify the supplied recovery inputs first."

class Refusal(Exception):
    pass

def need(ok, message):
    if not ok:
        raise Refusal(message)

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def read_json(path):
    need(path.is_file() and not path.is_symlink(), f"Missing regular JSON file: {path}. {STOP}")
    need(path.stat().st_size <= 20 * 1024 * 1024, f"Oversized metadata: {path}")
    return json.loads(path.read_text())

def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()

def safe_name(name):
    p = PurePosixPath(name)
    need(name and not p.is_absolute() and ".." not in p.parts and "\\" not in name, f"Unsafe path: {name!r}")
    need(p.as_posix() == name and all(c >= " " for c in name), f"Noncanonical path: {name!r}")
    return p

def archive_magic(data):
    return (data.startswith((b"PK\x03\x04", b"PK\x05\x06", b"PK\x07\x08", b"\x1f\x8b", b"\xfd7zXZ\x00", b"BZh", b"7z\xbc\xaf\x27\x1c", b"Rar!\x1a\x07", b"\x28\xb5\x2f\xfd", b"# v2 git bundle", b"# v3 git bundle"))
            or len(data) >= 262 and data[257:262] == b"ustar")

def metadata(path):
    before = path.lstat()
    need(stat.S_ISREG(before.st_mode) and before.st_nlink == 1, f"Not an independent regular file: {path}")
    value = {"bytes": before.st_size, "sha256": file_hash(path), "mode": format(before.st_mode & 0o777, "04o")}
    after = path.lstat()
    need((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns), f"Concurrent edit: {path}")
    return value

def policy_and_checkpoint(root):
    policy, checkpoint = read_json(root / "policy.json"), read_json(root / "checkpoint.json")
    need(policy.get("schema") == checkpoint.get("schema") == 1, "Unsupported schema")
    need(checkpoint.get("policy_sha256") == file_hash(root / "policy.json"), "Policy hash differs from checkpoint.json")
    need(re.fullmatch(r"[a-z0-9][a-z0-9-]*", checkpoint.get("series", "")), "Invalid series")
    need(isinstance(checkpoint.get("serial"), int) and checkpoint["serial"] >= 1, "Invalid serial")
    return policy, checkpoint

def inspect_payload(root, policy):
    need(root.is_dir() and not root.is_symlink() and root.name == "conaled-textbooks", f"Missing/wrong checkpoint root. {STOP}")
    limits, kit = policy["limits"], policy["native_kit"]
    kit_root, files = kit.get("root", "support/native-kit").rstrip("/"), {}
    for parent, dirs, names in os.walk(root, followlinks=False):
        for name in dirs:
            path = Path(parent) / name
            rel = path.relative_to(root).as_posix()
            parts = safe_name(rel).parts
            need(not path.is_symlink(), f"Symlink directory: {rel}")
            need(parts[0] in TOP_DIRS, f"Unexpected outer directory: {rel}")
            need(not any(x in BAD_PARTS for x in parts), f"Runtime/dependency directory prohibited: {rel}")
        for name in names:
            path = Path(parent) / name
            rel = path.relative_to(root).as_posix()
            parts = safe_name(rel).parts
            need(parts[0] in TOP_DIRS or len(parts) == 1 and parts[0] in TOP_FILES, f"Unexpected outer path: {rel}")
            need(not any(x in BAD_PARTS for x in parts), f"Runtime/dependency path prohibited: {rel}")
            need(not rel.lower().endswith(PARTIAL_SUFFIXES), f"Partial/temporary file prohibited: {rel}")
            value = metadata(path)
            need(value["mode"] in ("0644", "0755"), f"Unexpected file mode: {rel}")
            need(value["bytes"] <= limits["max_file_bytes"], f"File exceeds size limit: {rel}")
            if rel.startswith(kit_root + "/"):
                need(kit["files"].get(rel[len(kit_root)+1:]) == value, f"Native kit changed or gained a file: {rel}")
            else:
                need(not rel.lower().endswith(BUILD_SUFFIXES), f"Build/cache artifact prohibited: {rel}")
            if rel != "source/repository.bundle":
                need(not rel.lower().endswith(ARCHIVE_SUFFIXES), f"Nested archive prohibited: {rel}")
                with path.open("rb") as stream:
                    need(not archive_magic(stream.read(512)), f"Archive magic hidden in file: {rel}")
            if rel != "MANIFEST.json":
                files[rel] = value
    need(len(files) <= limits["max_files"], "Payload file-count limit exceeded")
    need(sum(v["bytes"] for v in files.values()) <= limits["max_total_bytes"], "Payload size limit exceeded")
    actual_kit = {p[len(kit_root)+1:]: v for p, v in files.items() if p.startswith(kit_root + "/")}
    need(actual_kit == kit["files"], "Native kit file set differs from fixed policy")
    for name, expected in policy.get("protected_files", {}).items():
        safe_name(name)
        need(name in files and files[name]["sha256"] == expected, f"Protected file changed/missing: {name}")
    for prefix, expected in policy.get("frozen_trees", {}).items():
        safe_name(prefix)
        prefix = prefix.rstrip("/") + "/"
        contents = {p[len(prefix):]: v for p, v in files.items() if p.startswith(prefix)}
        need(contents and digest(canonical(contents)) == expected, f"Frozen tree changed/missing: {prefix}")
    for name in TOP_FILES - {"MANIFEST.json"} | {"docs/DURABILITY.md", "source/repository.bundle", "source/refs.json", "source/saved-worktrees.json"}:
        need(name in files, f"Required file missing: {name}. {STOP}")
    for book in BOOKS:
        for name in (f"books/{book}/README.md", f"books/{book}/STATE.json"):
            need(name in files, f"Required book navigation/state missing: {name}. {STOP}")
        need(isinstance(read_json(root / "books" / book / "STATE.json"), dict), f"Book STATE.json must be an object: {book}")
    return files

def git_environment():
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_TERMINAL_PROMPT="0", GIT_NO_REPLACE_OBJECTS="1")
    return env

def git(repo, *args, raw=False):
    command = ["git", "-C", str(repo), "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false", "-c", "protocol.file.allow=always", "-c", "protocol.ext.allow=never", *map(str, args)]
    result = subprocess.run(command, capture_output=True, env=git_environment())
    need(result.returncode == 0, f"Git {' '.join(map(str,args[:3]))} failed: {result.stderr.decode(errors='replace')[-2000:]}")
    return result.stdout if raw else result.stdout.decode().strip()

def refs_from_catalog(catalog):
    need(catalog.get("schema") == 1 and catalog.get("external_archive_dependencies") == [], "Source catalog must be self-contained schema 1")
    need(set(catalog.get("books", {})) == BOOKS, "Source catalog must contain VFA, FDSA and PFDS")
    entries, expected = list(catalog.get("baseline_refs", [])), {}
    for book in sorted(BOOKS):
        entries += catalog["books"][book]["refs"]
    for item in entries:
        ref, oid = item["stored_ref"], item["object"]
        need(ref.startswith("refs/checkpoint/") and not any(c in ref for c in "\n\r\0"), f"Unsafe stored ref: {ref}")
        need(OID.fullmatch(oid), f"Invalid Git identity: {oid}")
        need(ref not in expected or expected[ref] == oid, f"Conflicting stored ref: {ref}")
        expected[ref] = oid
    for book in BOOKS:
        for role in ("main", "candidate"):
            need(catalog["books"][book]["roles"].get(role) in expected, f"Missing {book} {role} ref")
    return expected

def check_git_objects(repo, policy, temp):
    ids = sorted({line.split(" ", 1)[0] for line in git(repo, "rev-list", "--objects", "--all").splitlines()})
    object_list = temp / "object-list.txt"
    object_list.write_text("\n".join(ids) + "\n")
    archives, named, total = {}, {}, 0
    with object_list.open("rb") as source:
        proc = subprocess.Popen(["git", "-C", str(repo), "cat-file", "--batch"], stdin=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=git_environment())
        try:
            for oid in ids:
                header = proc.stdout.readline().decode().strip().split()
                need(len(header) == 3 and header[0] == oid, "Invalid Git object stream")
                kind, length = header[1], int(header[2])
                total += length
                need(length <= policy["limits"].get("max_git_object_bytes", 128 * 1024 * 1024), f"Git object too large: {oid}")
                need(total <= policy["limits"].get("max_git_expanded_bytes", 2 * 1024**3), "Git object expansion exceeds limit")
                head, tree, h, left = b"", bytearray(), hashlib.sha256(), length
                while left:
                    chunk = proc.stdout.read(min(left, 1024 * 1024))
                    need(chunk, "Truncated Git object stream")
                    head += chunk[:max(0, 512-len(head))]
                    if kind == "tree":
                        tree.extend(chunk)
                    h.update(chunk)
                    left -= len(chunk)
                need(proc.stdout.read(1) == b"\n", "Malformed Git object terminator")
                if kind == "blob" and archive_magic(head):
                    archives[oid] = {"bytes": length, "sha256": h.hexdigest()}
                if kind == "tree":
                    pos = 0
                    while pos < len(tree):
                        end = tree.index(0, pos)
                        mode, name = bytes(tree[pos:end]).split(b" ", 1)
                        child = bytes(tree[end+1:end+21]).hex()
                        name = name.decode("utf-8", errors="replace")
                        need(name not in BAD_PARTS and not name.lower().endswith(PARTIAL_SUFFIXES + BUILD_SUFFIXES), f"Dependency/cache/partial entry in Git history: {name} ({child})")
                        if name.lower().endswith(ARCHIVE_SUFFIXES):
                            named[child] = name
                        pos = end + 21
            need(proc.wait() == 0, "Git object inspection failed")
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
            proc.stdout.close()
            proc.stderr.close()
    allowed = policy.get("inherited_archive_blobs", {})
    for oid in set(archives) | set(named):
        need(oid in allowed, f"New/unapproved archive in Git history: {oid} {named.get(oid,'hidden extension')}")
        need(oid in archives and archives[oid] == {k: allowed[oid][k] for k in ("bytes", "sha256")}, f"Inherited archive identity changed: {oid}")
    need(set(allowed).issubset(archives), "Immutable inherited archive blob missing")

def load_source(bundle, catalog, policy, destination, temp):
    expected = refs_from_catalog(catalog)
    for ref, oid in policy.get("initial_refs", {}).items():
        need(expected.get(ref) == oid, f"Immutable initial source ref changed/missing: {ref}")
    with bundle.open("rb") as stream:
        need(stream.readline() in (b"# v2 git bundle\n", b"# v3 git bundle\n"), "Not a Git bundle")
        for _ in range(50000):
            line = stream.readline()
            need(line, "Truncated Git bundle header")
            if line == b"\n":
                break
            need(not line.startswith(b"-"), f"Bundle has external prerequisites. {STOP}")
        else:
            raise Refusal("Oversized Git bundle header")
    destination.mkdir()
    git(destination, "init", "--bare", ".")
    git(destination, "config", "gc.auto", "0")
    git(destination, "bundle", "verify", bundle)
    heads = {}
    for line in git(destination, "bundle", "list-heads", bundle).splitlines():
        oid, ref = line.split(" ", 1)
        if ref != "HEAD":
            need(ref not in heads, f"Duplicate advertised ref: {ref}")
            heads[ref] = oid
    need(heads == expected, "Bundle refs differ from source/refs.json")
    git(destination, "bundle", "unbundle", bundle)
    for ref, oid in expected.items():
        git(destination, "check-ref-format", ref)
        git(destination, "update-ref", ref, oid)
    git(destination, "update-ref", "--no-deref", "HEAD", expected[catalog["books"]["vfa"]["roles"]["candidate"]])
    for oid in set(policy.get("required_commits", [])) | {catalog["base_commit"]}:
        need(OID.fullmatch(oid), "Invalid required commit")
        git(destination, "cat-file", "-e", oid + "^{commit}")
    git(destination, "fsck", "--full", "--strict", "--no-reflogs")
    check_git_objects(destination, policy, temp)
    return expected

def verify(root, deep=False):
    policy, checkpoint = policy_and_checkpoint(root)
    files = inspect_payload(root, policy)
    manifest = read_json(root / "MANIFEST.json")
    need(manifest.get("schema") == 1 and manifest.get("series") == checkpoint["series"] and manifest.get("serial") == checkpoint["serial"], "Manifest/checkpoint identity mismatch")
    need(manifest.get("files") == files, "Manifest file set/hash/size/mode mismatch")
    if deep:
        with tempfile.TemporaryDirectory(prefix=".checkpoint-verify-", dir=root.parent) as tmp:
            temp = Path(tmp)
            load_source(root / "source/repository.bundle", read_json(root / "source/refs.json"), policy, temp / "repository.git", temp)
    return {"verified": True, "deep_source": deep, "serial": checkpoint["serial"], "files": len(files), "bytes": sum(v["bytes"] for v in files.values()), "durable_upload_verified": False}

def atomic_bytes(path, data, mode=0o644):
    fd, name = tempfile.mkstemp(prefix=".checkpoint-write-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(name, mode)
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)

def journal_path(root):
    return root.parent / ("." + root.name + ".transaction")

def recover_publication(root):
    journal = journal_path(root)
    if not journal.exists():
        return
    need(journal.is_dir() and not journal.is_symlink(), "Unsafe publication journal")
    state_file = journal / "state.json"
    if not state_file.exists():
        # No payload mutation occurs until this marker is written.
        shutil.rmtree(journal)
        return
    state = read_json(state_file)
    need(state.get("root") == str(root), "Publication journal belongs to a different root")
    allowed = {"checkpoint.json", "MANIFEST.json", "source/repository.bundle", "source/refs.json"}
    output = state.get("output")
    forward = bool(output and Path(output["path"]).is_file() and file_hash(Path(output["path"])) == output["sha256"])
    for entry in state["files"]:
        name = entry["path"]
        need(name in allowed, "Unexpected journal target")
        current = root / name
        if current.exists():
            need(not current.is_symlink() and file_hash(current) in {entry.get("old_sha256"), entry["new_sha256"]}, f"Concurrent edit after interrupted publication: {name}; preserve it before recovery")
        source = journal / entry["new"] if forward else journal / entry["old"] if entry.get("old") else None
        if source is None:
            current.unlink(missing_ok=True)
        else:
            expected = entry["new_sha256"] if forward else entry["old_sha256"]
            need(file_hash(source) == expected, "Damaged publication journal; recover from the verified release archive")
            replacement = journal / "replacement"
            shutil.copyfile(source, replacement)
            replacement.chmod(int(entry["mode"], 8))
            os.replace(replacement, current)
    shutil.rmtree(journal)

@contextlib.contextmanager
def locked(root):
    lock_path = root.parent / ("." + root.name + ".lock")
    need(not lock_path.is_symlink(), "Unsafe lock path")
    with lock_path.open("a+b") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise Refusal("Another checkpoint operation holds the POSIX lock") from exc
        recover_publication(root)
        yield

def publish(root, updates, output=None):
    """Journal publication; interruption is completed/rolled back by the next locked operation."""
    journal = journal_path(root)
    need(not journal.exists(), "Unresolved publication journal")
    journal.mkdir()
    state = {"schema": 1, "root": str(root), "files": [], "output": None}
    for number, (name, value) in enumerate(updates.items()):
        safe_name(name)
        target = root / name
        new = f"new-{number}"
        if isinstance(value, bytes):
            (journal / new).write_bytes(value)
        else:
            shutil.copyfile(value, journal / new)
        entry = {"path": name, "new": new, "new_sha256": file_hash(journal / new), "mode": "0644"}
        if target.exists():
            entry.update(old=f"old-{number}", old_sha256=file_hash(target))
            shutil.copyfile(target, journal / entry["old"])
        state["files"].append(entry)
    if output:
        archive, destination = output
        state["output"] = {"path": str(destination), "sha256": file_hash(archive)}
    atomic_bytes(journal / "state.json", json_bytes(state))
    created = False
    try:
        for entry in state["files"]:
            replacement = journal / "replacement"
            shutil.copyfile(journal / entry["new"], replacement)
            replacement.chmod(0o644)
            os.replace(replacement, root / entry["path"])
        if output:
            # Exclusive publication: an existing path is never replaced.
            os.link(output[0], output[1])
            created = True
        shutil.rmtree(journal)
    except BaseException:
        if created and output and output[1].exists() and file_hash(output[1]) == state["output"]["sha256"]:
            output[1].unlink()
        state["output"] = None
        atomic_bytes(journal / "state.json", json_bytes(state))
        recover_publication(root)
        raise

def outside(root, destination):
    need(not destination.is_relative_to(root), "Output/destination must be outside the checkpoint payload")
    need(not destination.exists() and not destination.is_symlink(), f"Refusing to overwrite: {destination}")
    need(destination.parent.is_dir(), "Destination parent directory must exist")

def safe_extract(archive, destination, expected_root, limits):
    seen, total = set(), 0
    with tarfile.open(archive, "r:xz") as tar:
        for index, member in enumerate(tar):
            need(index < limits["max_files"] * 4 + 100, "Too many archive members")
            raw = member.name[:-1] if member.isdir() and member.name.endswith("/") else member.name
            path = safe_name(raw)
            need(path.parts[0] == expected_root, "Archive has wrong/multiple roots")
            need(raw not in seen, f"Duplicate archive path: {raw}")
            seen.add(raw)
            need(member.isdir() or member.isreg(), f"Archive link/special file prohibited: {raw}")
            target = destination.joinpath(*path.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                target.chmod(0o755)
                continue
            total += member.size
            need(member.size <= limits["max_file_bytes"] and total <= limits["max_total_bytes"] + 20 * 1024 * 1024, "Extracted size limit exceeded")
            need(member.mode in (0o644, 0o755), f"Unexpected archived mode: {raw}")
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open("xb") as output, tar.extractfile(member) as source:
                shutil.copyfileobj(source, output, 1024 * 1024)
            target.chmod(member.mode)
    return destination / expected_root

def restore(root, destination, saved):
    outside(root, destination)
    verify(root)
    policy, _ = policy_and_checkpoint(root)
    catalog = read_json(root / "source/refs.json")
    with tempfile.TemporaryDirectory(prefix=".checkpoint-restore-", dir=destination.parent) as tmp:
        temp = Path(tmp)
        bare = temp / "repository.git"
        refs = load_source(root / "source/repository.bundle", catalog, policy, bare, temp)
        destination.mkdir()
        try:
            shutil.move(str(bare), destination / "repository.git")
            bare = destination / "repository.git"
            for book in sorted(BOOKS):
                oid = refs[catalog["books"][book]["roles"]["candidate"]]
                git(bare, "worktree", "add", "--detach", destination / "worktrees" / book, oid)
            if saved:
                for i, entry in enumerate(read_json(root / "source/saved-worktrees.json")["worktrees"]):
                    need(entry["book"] in BOOKS and OID.fullmatch(entry["commit"]), "Invalid saved worktree identity")
                    name = re.sub(r"[^a-zA-Z0-9_-]", "_", entry["name"])
                    git(bare, "worktree", "add", "--detach", destination / "saved-worktrees" / f"{i:03}-{entry['book']}-{name}", entry["commit"])
        except BaseException:
            shutil.rmtree(destination)
            raise
    return {"restored": str(destination), "historical_refs": len(refs), "candidate_worktrees": sorted(BOOKS), "acceptance_changed": False}

def delivery_path(root):
    return root.parent / ("." + root.name + ".delivery.json")

def delivery_matches(root, checkpoint, manifest_bytes):
    path = delivery_path(root)
    if not path.is_file():
        return False
    record = read_json(path)
    return (record.get("durable_uploaded") is True and record.get("serial") == checkpoint["serial"]
            and record.get("series") == checkpoint["series"] and record.get("manifest_sha256") == digest(manifest_bytes)
            and record.get("method") in ("create_library_file", "user-supplied-library-archive") and record.get("library_file_id"))

CONTRACT_UPDATE_FILES = {
    "README.md", "AGENTS.md", "docs/RESUME.md", "docs/WORKFLOW.md",
    "docs/INTEGRATION.md", "docs/CHECKPOINTS.md", "support/README.md",
    "source/README.md", "tools/checkpoint.py", "tools/test_checkpoint.py",
    "tools/README.md", "policy.json", "checkpoint.json",
    "source/refs.json", "source/repository.bundle",
}

def contract_update(root, archive, prior_bytes, before, policy, current):
    """Verify the user-directed 001 -> 002 upstream/setup amendment, never a generic bypass."""
    need(current["serial"] == 1, "Contract update is restricted to the recorded 001 -> 002 amendment")
    need(archive.is_file() and not archive.is_symlink() and not archive.is_relative_to(root), "Contract update needs the actual previous archive outside the payload")
    amendment = policy.get("source_import_amendment", {})
    fields = {"schema", "from_serial", "to_serial", "previous_manifest_sha256", "previous_archive_sha256", "master_commit", "source_bundle", "added_archive_blobs", "rationale_path"}
    need(set(amendment) == fields and amendment["schema"] == 1 and amendment["from_serial"] == 1 and amendment["to_serial"] == 2, "Missing/extraneous source-import amendment fields")
    record = read_json(delivery_path(root))
    sha = file_hash(archive)
    need(sha == amendment["previous_archive_sha256"] == record.get("archive_sha256") and archive.stat().st_size == record.get("archive_bytes"), "Previous archive differs from the recorded durable input")
    need(amendment["previous_manifest_sha256"] == digest(prior_bytes), "Amendment names a different previous manifest")
    pin = amendment["master_commit"]
    need(isinstance(pin, str) and OID.fullmatch(pin), "Invalid pinned master identity")
    source = amendment["source_bundle"]
    need(source == {k: before["source/repository.bundle"][k] for k in ("bytes", "sha256")}, "Imported source bundle differs from the exact amendment")
    reason = safe_name(amendment["rationale_path"])
    need(reason.parts[0] in {"books", "provenance"} and reason.suffix == ".md" and (root / reason).is_file(), "Amendment needs its preserved user-direction/rationale document")
    # Fixed extraction bounds precede reading the previous archive's own policy.
    caps = {"max_files": 12000, "max_file_bytes": 128 * 1024**2, "max_total_bytes": 256 * 1024**2}
    with tempfile.TemporaryDirectory(prefix=".checkpoint-contract-", dir=root.parent) as tmp:
        previous = safe_extract(archive, Path(tmp), root.name, caps)
        need((previous / "MANIFEST.json").read_bytes() == prior_bytes, "Previous archive is not the retained release manifest")
        verify(previous, deep=True)
        old_policy, old_checkpoint = policy_and_checkpoint(previous)
        need({k: v for k, v in current.items() if k != "policy_sha256"} == {k: v for k, v in old_checkpoint.items() if k != "policy_sha256"}, "Contract update changed checkpoint identity before packing")
        prior = read_json(previous / "MANIFEST.json")["files"]
        for name, expected in prior.items():
            need(name in before, f"Contract update removed prior payload: {name}")
            if name in CONTRACT_UPDATE_FILES:
                continue
            if name in {f"books/{book}/STATE.json" for book in BOOKS}:
                old_state, new_state = read_json(previous / name), read_json(root / name)
                need(all(new_state.get(k) == v and k in new_state for k, v in old_state.items()) and set(new_state) - set(old_state) <= {"integration"}, f"Contract update changed historical book state/acceptance: {name}")
                continue
            need(before[name] == expected, f"Contract update changed preserved mathematical/evidence payload: {name}")
        need(policy.get("native_kit") == old_policy.get("native_kit"), "Contract update changed the fixed native kit")
        need(policy.get("durability") == old_policy.get("durability"), "Contract update weakened durability policy")
        need(all(policy.get("initial_refs", {}).get(k) == v for k, v in old_policy.get("initial_refs", {}).items()), "Contract update lost an initial ref")
        need(set(old_policy.get("required_commits", [])) <= set(policy.get("required_commits", [])) and pin in policy.get("required_commits", []), "Contract update lost a required commit or pinned master")
        old_catalog, new_catalog = read_json(previous / "source/refs.json"), read_json(root / "source/refs.json")
        old_refs, new_refs = refs_from_catalog(old_catalog), refs_from_catalog(new_catalog)
        need(all(new_refs.get(k) == v for k, v in old_refs.items()) and new_catalog.get("base_commit") == old_catalog.get("base_commit"), "Contract update lost original source history/base")
        need(pin in new_refs.values(), "Pinned master lacks a retained source ref")
        for name, expected in old_policy.get("protected_files", {}).items():
            need(name in policy.get("protected_files", {}) and (name in CONTRACT_UPDATE_FILES or policy["protected_files"][name] == expected), f"Contract update removed/weakened a protected file: {name}")
        for prefix, expected in old_policy.get("frozen_trees", {}).items():
            need(prefix in policy.get("frozen_trees", {}) and (prefix in {"docs", "tools", "support"} or policy["frozen_trees"][prefix] == expected), f"Contract update changed a frozen mathematical/reference tree: {prefix}")
        old_limits, new_limits = old_policy["limits"], policy["limits"]
        need({k: v for k, v in new_limits.items() if k != "max_archive_bytes"} == {k: v for k, v in old_limits.items() if k != "max_archive_bytes"}, "Contract update changed normal payload/source/growth limits")
        need(old_limits["max_archive_bytes"] <= new_limits["max_archive_bytes"] <= 128 * 1024**2, "Contract archive limit exceeds the bounded 128 MiB amendment")
        old_archives, new_archives = old_policy.get("inherited_archive_blobs", {}), policy.get("inherited_archive_blobs", {})
        need(all(new_archives.get(k) == v for k, v in old_archives.items()), "Contract update changed an existing inherited archive identity")
        added = amendment["added_archive_blobs"]
        need(isinstance(added, dict) and set(new_archives) - set(old_archives) == set(added), "Archive exceptions differ from the exact upstream amendment")
        for oid, value in added.items():
            need(OID.fullmatch(oid) and set(value) == {"bytes", "sha256"} and value == {k: new_archives[oid][k] for k in ("bytes", "sha256")}, "Changed/unbound added archive identity")
        return max(0, source["bytes"] - prior["source/repository.bundle"]["bytes"])

def pack(root, output, next_serial, contract_update_from=None):
    outside(root, output)
    need(next_serial or contract_update_from is None, "--contract-update-from requires --next")
    policy, current = policy_and_checkpoint(root)
    before = inspect_payload(root, policy)
    checkpoint = copy.deepcopy(current)
    prior_bytes = (root / "MANIFEST.json").read_bytes() if (root / "MANIFEST.json").exists() else None
    if next_serial:
        need(prior_bytes is not None, f"--next requires the last release MANIFEST.json. {STOP}")
        prior = json.loads(prior_bytes)
        need(prior.get("series") == current["series"] and prior.get("serial") == current["serial"], "Checkpoint metadata already advanced or series changed")
        need(delivery_matches(root, current, prior_bytes), "Current release has no recorded durable delivery. Upload via create_library_file to the owner's root and record the real receipt; if unavailable report promptly and stop. After a wipe, adopt the user's reattached saved archive and server-provided Library ID.")
        exempt_source_growth = 0
        if contract_update_from is None:
            need(prior["files"]["checkpoint.json"] == before["checkpoint.json"], "Checkpoint metadata changed since last release")
        else:
            exempt_source_growth = contract_update(root, contract_update_from, prior_bytes, before, policy, current)
        checkpoint["serial"] += 1
        checkpoint["parent_manifest_sha256"] = digest(prior_bytes)
        old_bytes = sum(v["bytes"] for v in prior["files"].values())
        allowed = max(old_bytes * policy["limits"]["max_growth_ratio"], old_bytes + policy["limits"]["max_growth_bytes"])
        need(sum(v["bytes"] for v in before.values()) - exempt_source_growth <= allowed, "Growth exceeds policy; summarize operational growth before packaging")
    else:
        need(prior_bytes is None and current["serial"] == 1 and current.get("parent_manifest_sha256") is None, "Initial pack requires serial 1 and no MANIFEST; later use --next")
    need(output.name == f"{checkpoint['series']}-{checkpoint['serial']:03}.tar.xz", "Output filename must match series and exact next serial")
    checkpoint_bytes = json_bytes(checkpoint)
    files = copy.deepcopy(before)
    files["checkpoint.json"] = {"bytes": len(checkpoint_bytes), "sha256": digest(checkpoint_bytes), "mode": "0644"}
    manifest_bytes = json_bytes({"schema": 1, "series": checkpoint["series"], "serial": checkpoint["serial"], "files": files})
    with tempfile.TemporaryDirectory(prefix=".checkpoint-pack-", dir=output.parent) as tmp:
        temp = Path(tmp)
        load_source(root / "source/repository.bundle", read_json(root / "source/refs.json"), policy, temp / "source-check.git", temp)
        if contract_update_from is not None:
            amendment = policy["source_import_amendment"]
            upstream = {line.split(" ", 1)[0] for line in git(temp / "source-check.git", "rev-list", "--objects", amendment["master_commit"]).splitlines()}
            need(set(amendment["added_archive_blobs"]) <= upstream, "Added archive exception is not in the exact pinned master history")
        archive = temp / "release.tar.xz"
        replacements = {"checkpoint.json": checkpoint_bytes, "MANIFEST.json": manifest_bytes}
        with tarfile.open(archive, "w:xz", preset=6, format=tarfile.PAX_FORMAT) as tar:
            for name in sorted(set(files) | {"MANIFEST.json"}):
                entry = tarfile.TarInfo(root.name + "/" + name)
                entry.mtime, entry.uid, entry.gid = 0, 0, 0
                entry.uname = entry.gname = ""
                entry.mode = int(files[name]["mode"], 8) if name in files else 0o644
                if name in replacements:
                    data = replacements[name]
                    entry.size = len(data)
                    tar.addfile(entry, io.BytesIO(data))
                else:
                    entry.size = files[name]["bytes"]
                    with (root / name).open("rb") as stream:
                        tar.addfile(entry, stream)
        need(archive.stat().st_size <= policy["limits"]["max_archive_bytes"], "Compressed archive exceeds limit")
        extraction = temp / "extracted"
        extraction.mkdir()
        restored = safe_extract(archive, extraction, root.name, policy["limits"])
        verify(restored, deep=True)
        need(inspect_payload(root, policy) == before, "Payload changed during packaging; no release written")
        now = (root / "MANIFEST.json").read_bytes() if (root / "MANIFEST.json").exists() else None
        need(now == prior_bytes, "Manifest changed during packaging")
        publish(root, replacements, (archive, output))
    pending = {"schema": 1, "series": checkpoint["series"], "serial": checkpoint["serial"], "manifest_sha256": digest(manifest_bytes), "archive_sha256": file_hash(output), "archive_bytes": output.stat().st_size, "durable_uploaded": False}
    atomic_bytes(delivery_path(root), json_bytes(pending))
    return {**pending, "archive": str(output), "offline_roundtrip_verified": True, "completed": False, "acceptance_changed": False, "contract_update_applied": contract_update_from is not None, "next": "Upload using create_library_file to the owner's root, then record the actual receipt. If that route fails, report promptly and stop."}

def record_delivery(root, archive, receipt=None, library_id=None):
    verify(root, deep=True)
    policy, checkpoint = policy_and_checkpoint(root)
    need(archive.is_file() and not archive.is_symlink(), "Expected an actual supplied/released archive")
    need(archive.stat().st_size <= policy["limits"]["max_archive_bytes"], "Archive exceeds limit")
    sha, size = file_hash(archive), archive.stat().st_size
    if receipt is not None:
        value = read_json(receipt)
        need(value.get("method") == "create_library_file" and value.get("destination") == "owner-root", "Only an actual create_library_file owner-root receipt is accepted; report upload failure and stop")
        need(value.get("archive_sha256") == sha and value.get("archive_bytes") == size, "Receipt archive identity differs")
        library_id, method = value.get("library_file_id"), "create_library_file"
    else:
        method = "user-supplied-library-archive"
    need(isinstance(library_id, str) and re.fullmatch(r"libfile_[A-Za-z0-9_-]+", library_id), "Use the server-provided Library file ID, never an invented receipt")
    with tempfile.TemporaryDirectory(prefix=".checkpoint-adopt-", dir=root.parent) as tmp:
        restored = safe_extract(archive, Path(tmp), root.name, policy["limits"])
        verify(restored)
        need((restored / "MANIFEST.json").read_bytes() == (root / "MANIFEST.json").read_bytes(), "Supplied archive is not this exact checkpoint release")
    value = {"schema": 1, "series": checkpoint["series"], "serial": checkpoint["serial"], "manifest_sha256": file_hash(root / "MANIFEST.json"), "archive_sha256": sha, "archive_bytes": size, "library_file_id": library_id, "method": method, "durable_uploaded": True}
    atomic_bytes(delivery_path(root), json_bytes(value))
    return {**value, "completed": True, "note": "Delivery bookkeeping uses the supplied real connector receipt or user attachment identity; it does not call or authenticate a remote upload."}

def clean_worktrees(repo):
    blocks = git(repo, "worktree", "list", "--porcelain", "-z", raw=True).split(b"\0\0")
    for block in blocks:
        fields = block.split(b"\0")
        paths = [x[9:].decode() for x in fields if x.startswith(b"worktree ")]
        if not paths or b"bare" in fields:
            continue
        path = Path(paths[0])
        need(path.is_dir(), f"Registered worktree missing: {path}; reconcile it explicitly first")
        dirty = git(path, "status", "--porcelain=v1", "--untracked-files=all")
        need(not dirty, f"Dirty/untracked work would be lost in {path}:\n{dirty[:3000]}\nPreserve every draft/source/patch under books/BOOK/work or finish the normal repository workflow before retrying. Do not reset or delete work to satisfy this check.")
        ignored = git(path, "ls-files", "--others", "--ignored", "--exclude-standard", "-z", raw=True).split(b"\0")
        for raw in ignored:
            if not raw:
                continue
            name = raw.decode()
            # Only known dependency/build installations are exempt, never a generic build/cache directory.
            if any(x in {".lake", ".git", "toolchains", "runtime-cache"} for x in PurePosixPath(name).parts):
                continue
            raise Refusal(f"Ignored potential mathematical/source work: {path / name}; all ignored files outside the named dependency/build locations must be preserved explicitly before capture")

def capture(root, book, repo, candidate_ref):
    need(book in BOOKS, "Unknown book")
    need(repo.is_dir() and not repo.is_relative_to(root), "Source repository must be outside checkpoint payload")
    if candidate_ref != "HEAD":
        need(candidate_ref.startswith("refs/"), "Use a full Git candidate ref, or explicit HEAD")
        git(repo, "check-ref-format", candidate_ref)
    policy, checkpoint = policy_and_checkpoint(root)
    if (root / "MANIFEST.json").is_file():
        need(delivery_matches(root, checkpoint, (root / "MANIFEST.json").read_bytes()), "Prior release is not recorded as durable. Stop further accumulation, resolve the required owner-root upload or adopt the user's saved input archive before capture.")
    before = inspect_payload(root, policy)
    catalog = read_json(root / "source/refs.json")
    old_expected = refs_from_catalog(catalog)
    clean_worktrees(repo)
    incoming_text = git(repo, "for-each-ref", "--format=%(refname) %(objectname)")
    incoming = dict(line.split(" ", 1) for line in incoming_text.splitlines())
    candidate = git(repo, "rev-parse", "--verify", candidate_ref + "^{commit}")
    need(OID.fullmatch(candidate), "Candidate must resolve to a commit")
    with tempfile.TemporaryDirectory(prefix=".checkpoint-capture-", dir=root.parent) as tmp:
        temp = Path(tmp)
        store = temp / "repository.git"
        load_source(root / "source/repository.bundle", catalog, policy, store, temp)
        git(store, "fetch", "--no-tags", "--no-write-fetch-head", repo, "+refs/*:refs/capture-temporary/*")
        git(store, "fetch", "--no-tags", "--no-write-fetch-head", repo, candidate)
        sequence = int(catalog.get("capture_count", 0)) + 1
        updates = catalog["books"][book]["refs"]
        source_map = {}
        for ref, oid in incoming.items():
            if old_expected.get(ref) == oid:
                source_map[ref] = ref
                continue
            prior = next((x for x in reversed(updates) if x["original_ref"] == ref and x["object"] == oid), None)
            if prior:
                source_map[ref] = prior["stored_ref"]
                continue
            saved = f"refs/checkpoint/{book}/captures/{sequence:03}/" + ref.removeprefix("refs/")
            need(saved not in old_expected, "Capture namespace collision")
            git(store, "update-ref", saved, oid)
            updates.append({"original_ref": ref, "stored_ref": saved, "object": oid})
            source_map[ref] = saved
        matched = next((saved for ref, saved in source_map.items() if incoming[ref] == candidate and ref == candidate_ref), None)
        if matched is None:
            matched = f"refs/checkpoint/{book}/captures/{sequence:03}/candidate"
            git(store, "update-ref", matched, candidate)
            updates.append({"original_ref": candidate_ref, "stored_ref": matched, "object": candidate})
        catalog["books"][book]["roles"]["candidate"] = matched
        catalog["capture_count"] = sequence
        for ref in git(store, "for-each-ref", "--format=%(refname)", "refs/capture-temporary/").splitlines():
            git(store, "update-ref", "-d", ref)
        new_expected = refs_from_catalog(catalog)
        need(all(new_expected.get(ref) == oid for ref, oid in old_expected.items()), "Capture would lose historical refs")
        git(store, "update-ref", "--no-deref", "HEAD", new_expected[catalog["books"]["vfa"]["roles"]["candidate"]])
        bundle = temp / "new.bundle"
        git(store, "bundle", "create", bundle, "--all")
        load_source(bundle, catalog, policy, temp / "verification.git", temp)
        clean_worktrees(repo)
        need(git(repo, "for-each-ref", "--format=%(refname) %(objectname)") == incoming_text and git(repo, "rev-parse", "--verify", candidate_ref + "^{commit}") == candidate, "Source refs changed during capture")
        need(inspect_payload(root, policy) == before, "Checkpoint payload changed during capture")
        publish(root, {"source/repository.bundle": bundle, "source/refs.json": json_bytes(catalog)})
    return {"captured_book": book, "candidate": candidate, "historical_refs": len(new_expected), "previous_refs_preserved": len(old_expected), "acceptance_changed": False, "durable_uploaded": False, "next": "Update book progress notes truthfully; pack --next and the required owner-root upload make this work durable."}

def cli_path(path):
    need(not path.is_symlink(), f"Symlink argument prohibited: {path}")
    return path.resolve()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    commands = parser.add_subparsers(dest="command", required=True)
    p = commands.add_parser("verify")
    p.add_argument("--deep", action="store_true")
    p = commands.add_parser("restore-source")
    p.add_argument("--to", type=Path, required=True)
    p.add_argument("--all-saved-worktrees", action="store_true")
    p = commands.add_parser("pack")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--next", action="store_true", dest="next_serial")
    p.add_argument("--contract-update-from", type=Path)
    p = commands.add_parser("capture-source")
    p.add_argument("--book", choices=sorted(BOOKS), required=True)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--candidate-ref", required=True)
    p = commands.add_parser("record-upload")
    p.add_argument("--archive", type=Path, required=True)
    p.add_argument("--receipt", type=Path, required=True)
    p = commands.add_parser("adopt-input")
    p.add_argument("--archive", type=Path, required=True)
    p.add_argument("--library-file-id", required=True)
    args = parser.parse_args()
    try:
        root = cli_path(args.root)
        need(root.parent.is_dir(), STOP)
        with locked(root):
            if args.command == "verify":
                result = verify(root, args.deep)
            elif args.command == "restore-source":
                result = restore(root, cli_path(args.to), args.all_saved_worktrees)
            elif args.command == "pack":
                result = pack(root, cli_path(args.output), args.next_serial, cli_path(args.contract_update_from) if args.contract_update_from else None)
            elif args.command == "capture-source":
                result = capture(root, args.book, cli_path(args.repo), args.candidate_ref)
            elif args.command == "record-upload":
                result = record_delivery(root, cli_path(args.archive), receipt=cli_path(args.receipt))
            else:
                result = record_delivery(root, cli_path(args.archive), library_id=args.library_file_id)
        print(json.dumps(result, indent=2, sort_keys=True))
    except (Refusal, OSError, KeyError, ValueError, tarfile.TarError) as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 2
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

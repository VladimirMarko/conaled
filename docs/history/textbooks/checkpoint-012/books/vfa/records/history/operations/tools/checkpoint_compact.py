#!/usr/bin/env python3
"""Two-artifact recovery: one immutable Git base plus any latest snapshot.

No earlier rolling snapshot is needed. Source/tracker writers must be paused.
Explicit active validation directories may be captured as uncoordinated prefixes;
their captured records are not acceptance evidence. This tool never uploads.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile


FORMAT = 1
OMIT_DIRS = {"__pycache__", ".lake", ".cache", "checkpoints"}
SECRET_NAMES = {".env", ".netrc", ".npmrc", ".ssh", ".aws", "id_rsa", "id_ed25519"}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, cwd=None, input=None):
    env = os.environ.copy()
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_OPTIONAL_LOCKS="0", PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(argv, cwd=cwd, input=input, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {argv!r}\n"
                           + result.stderr.decode(errors="replace"))
    return result.stdout


def git(repo, *args):
    return run(["git", "-c", "core.fsmonitor=false", *args], cwd=repo)


def relative(name):
    path = PurePosixPath(name)
    require(name and not path.is_absolute() and ".." not in path.parts
            and str(path) == name and "\\" not in name,
            "Unsafe archive/source path: " + repr(name))
    return path


def file_state(path):
    if path.is_symlink():
        return {"kind": "symlink", "target": os.readlink(path)}
    if path.is_file():
        return {"kind": "file", "sha256": sha(path),
                "executable": bool(path.stat().st_mode & stat.S_IXUSR)}
    if path.is_dir():
        return {"kind": "directory"}
    require(not path.exists(), "Unsupported source entry: " + str(path))
    return {"kind": "missing"}


def source_file_state(repo, name):
    # A tracked descendant behind a replaced directory is missing, even if a
    # new symlink at that directory happens to lead to a file elsewhere.
    parts = relative(name).parts
    require(".git" not in parts, "Source path enters Git metadata")
    require(not any(part in SECRET_NAMES for part in parts),
            "Credential-like source path is not checkpointable: " + name)
    for i in range(1, len(parts)):
        parent = repo.joinpath(*parts[:i])
        if parent.is_symlink() or not parent.is_dir():
            return {"kind": "missing"}
    return file_state(repo.joinpath(*parts))


def patch(repo, cached=False):
    return git(repo, "diff", *(["--cached"] if cached else []), "HEAD",
               "--no-ext-diff", "--no-textconv", "--full-index", "--binary")


def source_state(repo):
    require(not git(repo, "ls-files", "-u"), "Unmerged indexes are unsupported")
    entries = git(repo, "ls-files", "--stage", "-z")
    require(not any(x.startswith(b"160000 ") for x in entries.split(b"\0")),
            "Submodule work trees require separate capture")
    flags = git(repo, "ls-files", "-v", "-z").split(b"\0")
    require(all(not x or x.startswith(b"H ") for x in flags),
            "Special index flags are unsupported; preserve them separately")
    names = set(git(repo, "ls-files", "-z", "--cached", "--others",
                    "--exclude-standard").decode().split("\0")) - {""}
    return {
        "head": git(repo, "rev-parse", "HEAD").decode().strip(),
        "status": git(repo, "status", "--porcelain=v1", "--untracked-files=all").decode(),
        "index_patch_sha256": digest(patch(repo, True)),
        "working_patch_sha256": digest(patch(repo)),
        "index_entries_sha256": digest(entries),
        "files": {name: source_file_state(repo, name) for name in sorted(names)},
    }


def refs(repo):
    rows = git(repo, "for-each-ref", "--format=%(refname) %(objectname) %(symref)")
    return [line.decode().split(" ", 2) for line in rows.splitlines()]


def tree_entries(repo):
    result = {}
    for entry in git(repo, "ls-tree", "-r", "-z", "HEAD").split(b"\0"):
        if entry:
            header, name = entry.split(b"\t", 1)
            mode, kind, oid = header.decode().split()
            require(kind == "blob", "Unsupported Git tree entry")
            result[name.decode()] = (mode, oid)
    return result


def same_as_git(repo, name, info, entry):
    if entry is None or info["kind"] not in {"file", "symlink"}:
        return False
    if info["kind"] == "symlink":
        data = os.fsencode(info["target"])
        mode = "120000"
    else:
        data = (repo / name).read_bytes()
        mode = "100755" if info["executable"] else "100644"
    # This project and its immutable base use Git's SHA-1 object format.
    oid = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
    return (mode, oid) == entry


def state_files(root):
    require(not root.is_symlink(),
            "Work-state/kit root symlinks need an explicit recovery design")
    require(root.is_dir(), "Required work-state/kit root is not a directory: " + str(root))
    def enumeration_error(error):
        raise error
    result = []
    for directory, dirs, files in os.walk(root, followlinks=False, onerror=enumeration_error):
        dirs[:] = sorted(d for d in dirs if d not in OMIT_DIRS)
        for name in dirs + files:
            require(name not in SECRET_NAMES, "Credential-like path is not checkpointable: "
                    + str(Path(directory) / name))
            require(not (Path(directory) / name).is_symlink(),
                    "Work-state/kit symlinks need an explicit recovery design")
        for name in sorted(files):
            if name.endswith(".pyc"):
                continue
            path = Path(directory) / name
            require(path.is_file(), "Special work-state file: " + str(path))
            result.append(path)
    return sorted(result)


def is_active(name, active):
    return any(name == prefix or name.startswith(prefix + "/") for prefix in active)


def workflow_state(root, active=()):
    return {str(p.relative_to(root)): file_state(p) for p in state_files(root)
            if not is_active(str(p.relative_to(root)), active)}


def copy_tree(root, target):
    target.mkdir(parents=True)
    for path in state_files(root):
        destination = target / path.relative_to(root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Bound reads at the opened file's size; an active append-only log is
        # therefore a prefix, not an attempt to chase a running writer.
        with path.open("rb") as src, destination.open("xb") as dst:
            remaining = os.fstat(src.fileno()).st_size
            while remaining:
                data = src.read(min(1024 * 1024, remaining))
                require(data, "File shortened during capture: " + str(path))
                dst.write(data)
                remaining -= len(data)
        # Executable bits are recovery-relevant. Normalize ordinary permissions
        # to the same safe modes used by tar's data extraction filter, including
        # read-only Git object files inside operational evidence repositories.
        destination.chmod(0o755 if path.stat().st_mode & stat.S_IXUSR else 0o644)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def manifest(root, write=False):
    actual = {}
    for path in sorted(root.rglob("*")):
        require(not path.is_symlink(), "Archive links are unsupported")
        if path.is_file() and path != root / "MANIFEST.json":
            name = str(path.relative_to(root))
            actual[name] = {"sha256": sha(path), "mode": stat.S_IMODE(path.stat().st_mode)}
    if write:
        write_json(root / "MANIFEST.json", actual)
    else:
        require(actual == json.loads((root / "MANIFEST.json").read_text()),
                "Archive manifest mismatch")


def pack(root, output):
    with tarfile.open(output, "w:gz", compresslevel=6) as archive:
        archive.add(root, arcname=root.name)


def unpack(archive_path, target, prefix):
    with tarfile.open(archive_path) as archive:
        seen = set()
        for member in archive.getmembers():
            name = str(relative(member.name))
            require(name == prefix or name.startswith(prefix + "/"), "Wrong archive root")
            require(name not in seen, "Duplicate archive member")
            require(member.isdir() or member.isfile(), "Archive links/special files rejected")
            seen.add(name)
        archive.extractall(target, filter="data")
    root = target / prefix
    manifest(root)
    return root


def initialize(bundle_root, repo):
    repo.mkdir()
    run(["git", "init", "--quiet", str(repo)])
    git(repo, "bundle", "verify", str(bundle_root / "conaled-base.bundle"))
    git(repo, "bundle", "unbundle", str(bundle_root / "conaled-base.bundle"))


def remove_source_path(repo, name):
    parts = relative(name).parts
    for i in range(1, len(parts)):
        parent = repo.joinpath(*parts[:i])
        if parent.is_symlink() or not parent.is_dir():
            return
    path = repo / name
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)
    else:
        require(not path.exists(), "Unsupported existing source path")


def restore(base_archive, snapshot_archive, destination):
    require(not destination.exists(), "Restore destination already exists")
    with tempfile.TemporaryDirectory(prefix="compact-read-", dir=destination.parent) as temp:
        base = unpack(base_archive, Path(temp) / "b", "base")
        snap = unpack(snapshot_archive, Path(temp) / "s", "checkpoint")
        meta = json.loads((snap / "metadata.json").read_text())
        binding = meta["base"]
        require(meta["format"] == FORMAT and meta["required_artifacts"] == 2,
                "Unsupported checkpoint format")
        require(base_archive.stat().st_size == binding["size_bytes"]
                and sha(base_archive) == binding["sha256"], "Wrong immutable base archive")
        require(json.loads((base / "metadata.json").read_text())["base_commit"]
                == binding["base_commit"], "Base commit mismatch")
        destination.mkdir()
        repo = destination / "conaled"
        initialize(base, repo)
        if (snap / "conaled-update.bundle").exists():
            git(repo, "bundle", "verify", str(snap / "conaled-update.bundle"))
            git(repo, "bundle", "unbundle", str(snap / "conaled-update.bundle"))
        for name, oid, symbolic in meta["refs"]:
            git(repo, "check-ref-format", name)
            if not symbolic:
                git(repo, "update-ref", name, oid)
        for name, oid, symbolic in meta["refs"]:
            if symbolic:
                git(repo, "check-ref-format", symbolic)
                git(repo, "symbolic-ref", name, symbolic)
        git(repo, "checkout", "--quiet", "--detach", meta["source"]["head"])
        if meta["symbolic_head"]:
            git(repo, "symbolic-ref", "HEAD", meta["symbolic_head"])
        index_patch = (snap / "index.patch").read_bytes()
        if index_patch:
            run(["git", "apply", "--cached", "--binary", "-"], cwd=repo, input=index_patch)
        overlay = meta["overlay"]
        for name in sorted(overlay, key=lambda n: len(PurePosixPath(n).parts), reverse=True):
            remove_source_path(repo, name)
        for name in sorted(overlay, key=lambda n: (len(PurePosixPath(n).parts), n)):
            info = overlay[name]
            path = repo / relative(name)
            if info["kind"] == "missing":
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            if info["kind"] == "directory":
                path.mkdir(exist_ok=True)
            elif info["kind"] == "file":
                shutil.copyfile(snap / "overlay" / info["sha256"], path)
                path.chmod(0o755 if info["executable"] else 0o644)
            else:
                require(info["kind"] == "symlink", "Unknown source state")
                os.symlink(info["target"], path)
        require(source_state(repo) == meta["source"], "Restored source/index/status mismatch")
        require(refs(repo) == meta["refs"], "Restored Git references mismatch")
        git(repo, "fsck", "--full")
        copy_tree(snap / "work-state", destination / "work-state")
        copy_tree(snap / "native-kit", destination / "native-kit")
        require(workflow_state(snap / "work-state") == workflow_state(destination / "work-state"),
                "Restored workflow differs from archived bytes")
        require(workflow_state(snap / "native-kit") == workflow_state(destination / "native-kit"),
                "Restored kit differs from archived bytes")
        shutil.copy2(snap / "RESTORE.md", destination / "RESTORE.md")
        shutil.copy2(snap / "metadata.json", destination / "recovery-metadata.json")
        run([sys.executable, "-B", str(destination / "native-kit/conaled_native.py"), "verify"])
    return meta


def publish(temp_archive, output):
    # Same-filesystem hard link is an atomic no-overwrite publication.
    os.link(temp_archive, output)
    return {"file": str(output), "size_bytes": output.stat().st_size, "sha256": sha(output)}


def create_base(args):
    output = args.output.resolve()
    require(not output.exists(), "Output already exists")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="compact-base-", dir=output.parent) as temp:
        temp = Path(temp)
        root = temp / "base"
        root.mkdir()
        shutil.copyfile(args.bundle, root / "conaled-base.bundle")
        repo = temp / "verify-repo"
        initialize(root, repo)
        git(repo, "cat-file", "-e", args.base_commit + "^{commit}")
        git(repo, "update-ref", "refs/heads/recovery-base", args.base_commit)
        git(repo, "fsck", "--full")
        write_json(root / "metadata.json", {"format": FORMAT, "base_commit": args.base_commit,
                   "bundle_sha256": sha(root / "conaled-base.bundle"),
                   "purpose": "Immutable companion; pair with any latest compact checkpoint."})
        manifest(root, write=True)
        packed = temp / "base.tar.gz"
        pack(root, packed)
        unpack(packed, temp / "smoke", "base")
        receipt = publish(packed, output)
    return {**receipt, "base_commit": args.base_commit, "bundle_verify": "passed",
            "git_fsck": "passed", "archive_manifest": "passed"}


def capture(args):
    require(not args.kit.is_symlink(),
            "Work-state/kit root symlinks need an explicit recovery design")
    ws, kit, base_archive, output = (p.resolve() for p in
                                    (args.workspace, args.kit, args.base, args.output))
    repo, state = ws / "conaled", ws / "work-state"
    require(not output.exists(), "Output already exists")
    require(not output.is_relative_to(state) and not output.is_relative_to(kit),
            "Checkpoint output must be outside work-state and kit")
    require(not kit.is_relative_to(state) and not state.is_relative_to(kit),
            "Kit and work-state must be separate trees")
    require(git(repo, "rev-parse", "--show-object-format").strip() == b"sha1",
            "This checkpoint format supports the project's SHA-1 Git objects")
    active = sorted(set(args.active_attempt))
    for name in active:
        parts = relative(name).parts
        require(len(parts) >= 2 and parts[0] == "validation" and (state / name).is_dir(),
                "Active attempt must be an existing validation subdirectory")
    output.parent.mkdir(parents=True, exist_ok=True)
    before, workflow_before = source_state(repo), workflow_state(state, active)
    refs_before, kit_before = refs(repo), workflow_state(kit)
    symbolic = subprocess.run(["git", "symbolic-ref", "-q", "HEAD"], cwd=repo,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(symbolic.returncode in {0, 1}, "Cannot read symbolic HEAD")
    symbolic_head = symbolic.stdout.decode().strip() if symbolic.returncode == 0 else None
    with tempfile.TemporaryDirectory(prefix="compact-capture-", dir=output.parent) as temp:
        temp = Path(temp)
        base = unpack(base_archive, temp / "base-input", "base")
        base_meta = json.loads((base / "metadata.json").read_text())
        base_commit = base_meta["base_commit"]
        git(repo, "merge-base", "--is-ancestor", base_commit, before["head"])
        root = temp / "checkpoint"
        root.mkdir()
        objects = git(repo, "rev-list", "--objects", "--all", "HEAD", "^" + base_commit)
        if objects:
            git(repo, "bundle", "create", str(root / "conaled-update.bundle"),
                "--all", "HEAD", "^" + base_commit)
        (root / "index.patch").write_bytes(patch(repo, True))
        (root / "working-tree.patch").write_bytes(patch(repo))
        entries = tree_entries(repo)
        overlay = {}
        (root / "overlay").mkdir()
        for name in sorted(set(entries) | set(before["files"])):
            info = before["files"].get(name, {"kind": "missing"})
            if same_as_git(repo, name, info, entries.get(name)):
                continue
            overlay[name] = info
            if info["kind"] == "file":
                shutil.copyfile(repo / name, root / "overlay" / info["sha256"])
        copy_tree(state, root / "work-state")
        copy_tree(kit, root / "native-kit")
        require(workflow_state(root / "work-state", active) == workflow_before,
                "Copied stable workflow differs from captured state")
        require(workflow_state(root / "native-kit") == kit_before,
                "Copied kit differs from captured state")
        binding = {"file_name": base_archive.name, "sha256": sha(base_archive),
                   "size_bytes": base_archive.stat().st_size, "base_commit": base_commit,
                   "library_file_id": args.base_library_id}
        metadata = {"format": FORMAT, "required_artifacts": 2, "base": binding,
                    "source": before, "refs": refs_before, "symbolic_head": symbolic_head,
                    "overlay": overlay, "active_attempts": active,
                    "active_attempt_semantics": "Captured files may be uncoordinated prefixes; "
                    "they do not establish a terminal outcome or acceptance.",
                    "no_previous_checkpoint_required": True}
        write_json(root / "metadata.json", metadata)
        shutil.copyfile(Path(__file__), root / "restore.py")
        (root / "RESTORE.md").write_text("""# Restore this latest recovery checkpoint

Exactly two archives are required: this checkpoint and the immutable base named
by `metadata.json` (exact SHA-256, size and available Library identity). No earlier
rolling checkpoint is needed. Keep both archives available for recovery.

Extract this checkpoint, then run its included tool against the original archives:

    python3 checkpoint/restore.py restore --base /path/to/base.tar.gz \\
      --checkpoint /path/to/latest.tar.gz --destination /path/to/new-empty-location

The destination must not exist. The tool verifies both manifests and the base
binding, restores exact source/index/status and Git refs, runs Git fsck, copies
all saved task state and the supplied native kit, and verifies the kit. It does
not install a compiler or restore build caches or successful validation records
into `.lake`. Historical records remain evidence with their recorded limitations.

Read work-state/STATUS.md, REQUIREMENTS.md, AMENDMENTS.md, tickets.json, reviews,
and tooling/UNIFIED-NATIVE.md before resuming. The kit is at native-kit/; follow
its README for exact setup. No GitHub writes are authorized. Active attempt files
may be uncoordinated prefixes; saved PIDs and execution handles are historical.
Source/index/tracker writers were held stable during capture except the explicitly
listed active validation directories. A checkpoint itself accepts no chapter.
""")
        manifest(root, write=True)
        packed = temp / "checkpoint.tar.gz"
        pack(root, packed)
        restore(base_archive, packed, temp / "restore-smoke")
        require(source_state(repo) == before and refs(repo) == refs_before,
                "Source/index/refs changed during capture")
        final_symbolic = subprocess.run(["git", "symbolic-ref", "-q", "HEAD"], cwd=repo,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require((final_symbolic.returncode, final_symbolic.stdout)
                == (symbolic.returncode, symbolic.stdout), "Symbolic HEAD changed during capture")
        require(workflow_state(state, active) == workflow_before,
                "Stable workflow files changed during capture")
        require(workflow_state(kit) == kit_before, "Kit changed during capture")
        receipt = publish(packed, output)
    return {**receipt, "head": before["head"], "base": binding,
            "restore_smoke": "passed", "source_index_workflow_stability": "passed",
            "active_attempts": active, "required_artifacts": 2}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    base = commands.add_parser("create-base")
    base.add_argument("--bundle", type=Path, required=True)
    base.add_argument("--base-commit", required=True)
    base.add_argument("--output", type=Path, required=True)
    cap = commands.add_parser("capture")
    cap.add_argument("--workspace", type=Path, required=True)
    cap.add_argument("--kit", type=Path, required=True)
    cap.add_argument("--base", type=Path, required=True)
    cap.add_argument("--base-library-id")
    cap.add_argument("--output", type=Path, required=True)
    cap.add_argument("--active-attempt", action="append", default=[])
    res = commands.add_parser("restore")
    res.add_argument("--base", type=Path, required=True)
    res.add_argument("--checkpoint", type=Path, required=True)
    res.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "create-base":
        result = create_base(args)
    elif args.command == "capture":
        result = capture(args)
    else:
        meta = restore(args.base.resolve(), args.checkpoint.resolve(), args.destination.resolve())
        result = {"destination": str(args.destination.resolve()), "head": meta["source"]["head"],
                  "restore": "passed", "active_attempts": meta["active_attempts"]}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

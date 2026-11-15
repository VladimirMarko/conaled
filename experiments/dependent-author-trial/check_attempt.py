#!/usr/bin/env python3
"""Preserve a single-file attempt and check it against a frozen public handoff.

Run from the handoff root: python3 check_attempt.py attempts/Attempt01.lean
The coordinator separately checks declaration coverage, statements, and axioms.
This is an experimental access contract, not an operating-system sandbox.
"""

from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import time


MANIFEST = "public-manifest.json"
EXCLUDED = {".git", ".lake", ".direnv", "attempts", "__pycache__"}


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return sha256(data).hexdigest()


def save_json(path, value):
    with path.open("x", encoding="utf-8") as output:
        json.dump(value, output, indent=2, sort_keys=True)
        output.write("\n")


def check_public(root, manifest, manifest_bytes):
    if (root / MANIFEST).read_bytes() != manifest_bytes:
        raise ValueError("Public manifest changed during this attempt")
    files = manifest["files"]
    for name, expected in files.items():
        path = Path(name)
        if (path.is_absolute() or ".." in path.parts or not path.parts
                or path.parts[0] in EXCLUDED or name == MANIFEST):
            raise ValueError(f"Invalid frozen public path: {name}")
        source = root / path
        if source.resolve() != source.absolute() or not source.is_file():
            raise ValueError(f"Missing or linked frozen input: {name}")
        if digest(source.read_bytes()) != expected:
            raise ValueError(f"Frozen input changed: {name}")
    # Skip dependency/build infrastructure: its provenance is coordinator-owned.
    for directory, subdirs, names in os.walk(root, followlinks=False):
        relative = Path(directory).relative_to(root)
        if relative == Path("."):
            subdirs[:] = [name for name in subdirs if name not in EXCLUDED]
        for name in subdirs:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"Linked public directory: {relative / name}")
        for name in names:
            public = str(relative / name)
            if public != MANIFEST and public not in files:
                raise ValueError(f"Unlisted public file: {public}")


def run_command(root, archive, label, argv):
    record = {"argv": argv, "cwd": str(root), "start": now()}
    save_json(archive / f"{label}.command.json", record)
    started = time.monotonic()
    try:
        with (archive / f"{label}.stdout.log").open("xb") as stdout:
            with (archive / f"{label}.stderr.log").open("xb") as stderr:
                result = subprocess.run(argv, cwd=root, stdout=stdout, stderr=stderr)
        record["exit"] = result.returncode
    except (OSError, KeyboardInterrupt) as error:
        record.update(exit=None, error=str(error))
        raise
    finally:
        record.update(finish=now(), elapsed_seconds=time.monotonic() - started)
        save_json(archive / f"{label}.result.json", record)
    return result.returncode


def check_imports(root, archive, allowed):
    libdir = Path((archive / "libdir.stdout.log").read_text().strip()).resolve()
    project = root / ".lake/build/lib/lean"
    packages = root / ".lake/packages"
    dependencies = []
    for line in (archive / "deps.stdout.log").read_text().splitlines():
        path = Path(line).resolve()
        if path.suffix != ".olean":
            raise ValueError(f"Unexpected Lean dependency output: {line}")
        if path.is_relative_to(project):
            module = ".".join(path.relative_to(project).with_suffix("").parts)
            if module not in allowed:
                raise ValueError(f"Project import outside frozen allowlist: {module}")
        elif not (path.is_relative_to(libdir) or path.is_relative_to(packages)):
            raise ValueError(f"Dependency outside handoff/toolchain: {line}")
        dependencies.append(str(path))
    save_json(archive / "imports.json", dependencies)


def main():
    if len(sys.argv) != 2:
        raise ValueError("Usage: python3 check_attempt.py attempts/Attempt01.lean")
    root = Path.cwd().resolve()
    source = root / sys.argv[1]
    # One self-contained module per attempt; use a new filename for every revision.
    if (source.resolve().parent != root / "attempts"
            or source.suffix != ".lean" or source.is_symlink() or not source.is_file()):
        raise ValueError("Expected an unlinked .lean file directly inside attempts/")
    archive = root / "attempts/checks" / source.stem
    if archive.parent.resolve() != archive.parent.absolute():
        raise ValueError("Attempt archive path must not contain symlinks")
    archive.mkdir(parents=True, exist_ok=False)
    source_bytes = source.read_bytes()
    snapshot = archive / "Source.lean"
    snapshot.write_bytes(source_bytes)
    snapshot.chmod(0o444)
    record = {
        "schema": 1, "source": str(source.relative_to(root)),
        "source_sha256": digest(source_bytes), "start": now(),
        "invocation": sys.argv, "cwd": str(root),
        "environment": {key: os.environ.get(key)
                        for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT")},
        "acceptance": "pending coordinator declaration/statement/axiom checks",
    }
    save_json(archive / "attempt.json", record)
    started = time.monotonic()
    exit_code = 2
    try:
        manifest_bytes = (root / MANIFEST).read_bytes()
        (archive / MANIFEST).write_bytes(manifest_bytes)
        record["manifest_sha256"] = digest(manifest_bytes)
        manifest = json.loads(manifest_bytes)
        if not isinstance(manifest, dict) or manifest.get("schema") != 1:
            raise ValueError("Unsupported public manifest schema")
        if not isinstance(manifest.get("files"), dict):
            raise ValueError("files must map public relative paths to SHA256")
        allowed = manifest["allowed_imports"]
        if not isinstance(allowed, list) or not all(isinstance(x, str) for x in allowed):
            raise ValueError("allowed_imports must list project module names")
        for module in allowed:
            if module.replace(".", "/") + ".lean" not in manifest["files"]:
                raise ValueError(f"Allowed module has no frozen source: {module}")
        check_public(root, manifest, manifest_bytes)
        record["public_inputs_before"] = "verified"
        relative_snapshot = str(snapshot.relative_to(root))
        commands = [
            ("libdir", ["lake", "env", "lean", "--print-libdir"]),
            ("deps", ["lake", "env", "lean", "--deps", relative_snapshot]),
        ]
        for label, command in commands:
            exit_code = run_command(root, archive, label, command)
            if exit_code:
                break
        else:
            check_imports(root, archive, allowed)
            exit_code = run_command(root, archive, "lean",
                                    ["lake", "env", "lean", relative_snapshot])
            record["lean_exit"] = exit_code
        check_public(root, manifest, manifest_bytes)
        record["public_inputs_after"] = "verified"
        if snapshot.read_bytes() != source_bytes:
            raise ValueError("Archived source changed during checking")
        if source.read_bytes() != source_bytes:
            raise ValueError("Authored source changed during checking")
        record["status"] = "lean-passed" if exit_code == 0 else "lean-failed"
    except (OSError, ValueError, KeyError, TypeError) as error:
        record.update(status="wrapper-rejected", error=str(error))
        exit_code = 2
    except KeyboardInterrupt:
        record.update(status="interrupted", error="Checking interrupted")
        exit_code = 130
    finally:
        record.update(finish=now(), elapsed_seconds=time.monotonic() - started,
                      exit=exit_code)
        record["evidence_sha256"] = {
            str(path.relative_to(archive)): digest(path.read_bytes())
            for path in sorted(archive.iterdir()) if path.is_file()
        }
        save_json(archive / "result.json", record)
        for path in archive.iterdir():
            if path.is_file():
                path.chmod(0o444)
        archive.chmod(0o555)
    for label in ("libdir", "deps", "lean"):
        for stream in ("stdout", "stderr"):
            path = archive / f"{label}.{stream}.log"
            if path.exists() and label != "libdir":
                sys.stdout.buffer.write(path.read_bytes())
    if "error" in record:
        print(record["error"])
    print(f"Exit {exit_code}; archived at {archive.relative_to(root)}")
    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        sys.exit(str(error))

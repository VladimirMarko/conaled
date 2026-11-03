#!/usr/bin/env python3
"""Create, inspect, or use an exact Lean profile with native executable metadata.

Use --create once in a recovered workspace, --describe for read-only identity,
or -- COMMAND ... to execute a normal command. The original release is unchanged.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


ORIGINAL_HASHES = {
    "lean": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
    "lake": "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
    "leanir": "5908f2917dcda5ed840e1ff5d6cdac5d104f9f6ca1ab1dc9f11d1c9fe220487e",
}
REJECT_SELECTORS = (
    "LEAN", "LEAN_PATH", "LEAN_CC", "LEAN_AR", "LEAN_WORKER_PATH",
    "LEAN_GITHASH", "LAKE_HOME", "LAKE_OVERRIDE_LEAN",
)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def create(root, profile):
    original = root / "toolchains/lean-4.35.0-linux"
    source = root / "session/environment/native-own-exe.c"
    require(not profile.exists() and not profile.is_symlink(),
            f"Refusing to replace an existing native profile: {profile}")
    for name, expected in ORIGINAL_HASHES.items():
        path = original / "bin" / name
        require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                f"Original release executable does not match the exact pin: {path}")
    compiler_name = shutil.which("cc")
    require(compiler_name is not None, "A native C compiler is required to build the compatibility library.")
    compiler = Path(compiler_name).resolve()
    staging = Path(tempfile.mkdtemp(prefix=".lean-native-", dir=profile.parent))
    try:
        for item in original.iterdir():
            if item.name != "bin":
                (staging / item.name).symlink_to(item, target_is_directory=item.is_dir())
        (staging / "bin").mkdir()
        (staging / "support").mkdir()
        library = staging / "support/native-own-exe.so"
        build = [str(compiler), "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
                 "-fPIC", "-fvisibility=hidden", "-shared", str(source),
                 "-o", str(library), "-ldl", "-pthread"]
        subprocess.run(build, check=True)
        binaries = {}
        for item in (original / "bin").iterdir():
            target = staging / "bin" / item.name
            if item.name in ORIGINAL_HASHES:
                real = target.with_name(item.name + ".real")
                shutil.copy2(item, real)
                require(digest(real) == ORIGINAL_HASHES[item.name], "Copied release executable changed.")
                final = profile / "bin" / real.name
                target.write_text("#!/bin/sh\nexport PFDS_NATIVE_EXECUTABLE=" +
                                  shlex.quote(str(final)) + "\nexec " +
                                  shlex.quote(str(final)) + ' "$@"\n')
                target.chmod(0o755)
                binaries[item.name] = {
                    "original_sha256": digest(item), "real_sha256": digest(real),
                    "launcher_sha256": digest(target),
                }
            else:
                target.symlink_to(item)
        receipt = {
            "schema": 1, "execution": "native", "original": str(original),
            "profile": str(profile), "wrapped_binaries": binaries,
            "compatibility_source_sha256": digest(source),
            "compatibility_library_sha256": digest(library),
            "profile_helper_sha256": digest(Path(__file__).resolve()),
            "build_command": build, "c_compiler": str(compiler),
            "c_compiler_sha256": digest(compiler),
            "c_compiler_version": subprocess.check_output([str(compiler), "--version"], text=True),
            "lean_release_archive_sha256":
                "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d",
            "launch_contract": "Direct exec of frozen canonical absolute regular ELF; per-exec marker equals AT_EXECFN; original readlink first; only missing own link may fall back.",
        }
        (staging / "profile-identity.json").write_text(json.dumps(receipt, indent=2) + "\n")
        staging.rename(profile)
        return receipt
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def describe(root, profile):
    receipt_path = profile / "profile-identity.json"
    receipt = json.loads(receipt_path.read_text())
    original = root / "toolchains/lean-4.35.0-linux"
    require(receipt["schema"] == 1 and receipt["execution"] == "native" and
            receipt["profile"] == str(profile) and receipt["original"] == str(original),
            "Native profile location or format differs; reconstruct after relocation.")
    identities = {str(receipt_path): digest(receipt_path)}
    sources = {
        root / "session/environment/native-own-exe.c": receipt["compatibility_source_sha256"],
        profile / "support/native-own-exe.so": receipt["compatibility_library_sha256"],
        Path(__file__).resolve(): receipt["profile_helper_sha256"],
    }
    for name, original_hash in ORIGINAL_HASHES.items():
        entry = receipt["wrapped_binaries"][name]
        require(entry["original_sha256"] == entry["real_sha256"] == original_hash,
                f"Native profile has a different compiler identity: {name}")
        sources[original / "bin" / name] = original_hash
        sources[profile / "bin" / (name + ".real")] = original_hash
        sources[profile / "bin" / name] = entry["launcher_sha256"]
    for path, expected in sources.items():
        require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                f"Native toolchain input differs: {path}")
        identities[str(path)] = expected
    unexpected = [key for key in REJECT_SELECTORS if os.environ.get(key)]
    require(not unexpected, "Unexpected inherited Lean/Lake selectors; use a clean launch shell: " +
            ", ".join(unexpected))
    library = str(profile / "support/native-own-exe.so")
    inherited_preload = os.environ.get("LD_PRELOAD", "")
    # Existing runtime machinery keeps precedence and exact relative order.
    preload = inherited_preload + (" " if inherited_preload else "") + library
    inherited_libraries = os.environ.get("LD_LIBRARY_PATH", "")
    libraries = os.pathsep.join(str(profile / p) for p in ("lib/lean", "lib"))
    if inherited_libraries:
        libraries += os.pathsep + inherited_libraries
    settings = {
        "PATH": str(profile / "bin") + os.pathsep + os.environ.get("PATH", ""),
        "LD_LIBRARY_PATH": libraries, "LD_PRELOAD": preload,
        "LEAN_SYSROOT": str(profile), "LEAN_NUM_THREADS": "1",
        "LAKE_CACHE_DIR": str(root / "runtime-cache/lake"),
        "MATHLIB_CACHE_DIR": str(root / "runtime-cache/mathlib"),
        "TMPDIR": str(root / "runtime-cache/tmp"),
    }
    return {"workspace": str(root), "profile": str(profile), "execution": "native",
            "environment": settings, "identities": identities,
            "launcher_sha256": digest(Path(__file__).resolve()),
            "marker_policy": "Each compiler wrapper sets its own exact ELF path; direct workspace ELF commands receive their own marker; unrelated child exec inherits a mismatched marker."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[2])
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--create", action="store_true")
    actions.add_argument("--describe", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = args.workspace.resolve()
    profile = root / "toolchains/lean-4.35.0-native"
    if args.create or args.describe:
        if args.command:
            parser.error("--create/--describe does not run a command")
        result = create(root, profile) if args.create else describe(root, profile)
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("supply a command after --")
    description = describe(root, profile)
    settings = description["environment"]
    for key in ("LAKE_CACHE_DIR", "MATHLIB_CACHE_DIR", "TMPDIR"):
        Path(settings[key]).mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(settings)
    env.pop("PFDS_NATIVE_EXECUTABLE", None)
    target = Path(command[0])
    if target.is_absolute() and target.is_file() and target.resolve() == target and target.is_relative_to(root):
        with target.open("rb") as stream:
            if stream.read(4) == b"\x7fELF":
                env["PFDS_NATIVE_EXECUTABLE"] = str(target)
    os.execvpe(command[0], command, env)


if __name__ == "__main__":
    main()

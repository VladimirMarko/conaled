#!/usr/bin/env python3
"""Create a separate profile around unchanged official Lean release executables."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import shutil
import tempfile


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    root = args.workspace.resolve()
    original = root / "toolchains/lean-4.35.0-linux"
    emulator = root / "toolchains/qemu-7.2-deb12u18/qemu-x86_64-static"
    profile = root / "toolchains/lean-4.35.0-profile"
    wrapped = ("lean", "lake", "leanir")
    if not original.is_dir() or not emulator.is_file():
        raise SystemExit("Restore the digest-verified official Lean and QEMU distributions first.")
    if profile.exists():
        raise SystemExit(f"Refusing to replace an existing profile: {profile}")
    staging = Path(tempfile.mkdtemp(prefix=".lean-profile-", dir=profile.parent))
    try:
        for item in original.iterdir():
            if item.name != "bin":
                (staging / item.name).symlink_to(item, target_is_directory=item.is_dir())
        (staging / "bin").mkdir()
        binaries = {}
        for item in (original / "bin").iterdir():
            target = staging / "bin" / item.name
            if item.name in wrapped:
                real = target.with_name(item.name + ".real")
                shutil.copy2(item, real)
                if sha256(real) != sha256(item):
                    raise RuntimeError(f"Executable copy differs: {item}")
                target.write_text("#!/bin/sh\nexec " + shlex.quote(str(emulator)) + " " +
                                  shlex.quote(str(profile / "bin" / real.name)) + ' "$@"\n')
                target.chmod(0o755)
                binaries[item.name] = {"original_sha256": sha256(item),
                                      "real_sha256": sha256(real),
                                      "launcher_sha256": sha256(target)}
            else:
                target.symlink_to(item)
        manifest = {"schema": 1, "original": str(original), "profile": str(profile),
                    "emulator": str(emulator), "emulator_sha256": sha256(emulator),
                    "wrapped_binaries": binaries,
                    "lean_release_archive_sha256":
                    "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d",
                    "qemu_deb_sha256":
                    "c3e3ba2bd87f8c5b9a5da5ef21b5a3b82d7c63b89dd448d9ddaa4eabc5b6e402"}
        (staging / "profile-identity.json").write_text(json.dumps(manifest, indent=2) + "\n")
        staging.rename(profile)
        print(json.dumps(manifest, indent=2))
    finally:
        if staging.exists():
            shutil.rmtree(staging)


if __name__ == "__main__":
    main()

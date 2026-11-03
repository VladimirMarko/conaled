#!/usr/bin/env python3
"""Run an ordinary project command in the pinned workspace-local Lean profile."""
import argparse
import hashlib
import json
import os
from pathlib import Path


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--describe", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = args.workspace.resolve()
    profile = root / "toolchains/lean-4.35.0-profile"
    receipt = profile / "profile-identity.json"
    manifest = json.loads(receipt.read_text())
    identities = {str(receipt): digest(receipt)}
    emulator = Path(manifest["emulator"])
    if digest(emulator) != manifest["emulator_sha256"]:
        raise SystemExit("QEMU executable differs from the recorded profile.")
    identities[str(emulator)] = manifest["emulator_sha256"]
    for name, expected in manifest["wrapped_binaries"].items():
        for path, key in ((profile / "bin" / name, "launcher_sha256"),
                          (profile / "bin" / (name + ".real"), "real_sha256"),
                          (Path(manifest["original"]) / "bin" / name, "original_sha256")):
            actual = digest(path)
            if actual != expected[key]:
                raise SystemExit(f"Toolchain executable differs from the recorded profile: {path}")
            identities[str(path)] = actual
    settings = {
        "PATH": str(profile / "bin") + os.pathsep + os.environ.get("PATH", ""),
        "LD_LIBRARY_PATH": os.pathsep.join(str(profile / p) for p in ("lib/lean", "lib")),
        "LEAN_SYSROOT": str(profile),
        "LEAN_NUM_THREADS": "1",
        "LAKE_CACHE_DIR": str(root / "runtime-cache/lake"),
        "MATHLIB_CACHE_DIR": str(root / "runtime-cache/mathlib"),
        "TMPDIR": str(root / "runtime-cache/tmp"),
    }
    description = {"workspace": str(root), "profile": str(profile), "environment": settings,
                   "launcher_sha256": digest(Path(__file__)), "identities": identities}
    if args.describe:
        if args.command:
            parser.error("--describe does not run a command")
        print(json.dumps(description, indent=2, sort_keys=True))
        return
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("supply a command after --")
    for key in ("LAKE_CACHE_DIR", "MATHLIB_CACHE_DIR", "TMPDIR"):
        Path(settings[key]).mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(settings)
    os.execvpe(command[0], command, env)


if __name__ == "__main__":
    main()

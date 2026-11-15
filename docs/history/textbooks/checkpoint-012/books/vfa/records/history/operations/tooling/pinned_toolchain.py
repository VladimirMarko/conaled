#!/usr/bin/env python3
"""Launch the pinned, unmodified Lean distribution on this host via QEMU.

This is recovery-environment tooling outside the conaled source tree. The
official distribution stays immutable. Lake's supported installation override
selects an overlay whose Lean entry point explicitly invokes user-mode QEMU.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import sys


WORKSPACE = Path(__file__).resolve().parents[2]
TOOLCHAINS = WORKSPACE / "toolchains"
OFFICIAL = TOOLCHAINS / "lean-4.35.0-linux"
OVERLAY = TOOLCHAINS / "lean-4.35.0-host"
QEMU = TOOLCHAINS / "qemu-user/bin/qemu-x86_64-static"
EXPECTED = {
    QEMU: "90181b5552cd1a0b60d8edcc9f1cf8e38647579ef697d3155e2b6150e8fbcee0",
    OFFICIAL / "bin/lean": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
    OFFICIAL / "bin/lake": "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
}
UNSET = ("LEAN", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH", "LAKE_HOME", "LAKE_OVERRIDE_LEAN")


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def link(target: Path, source: Path) -> None:
    relative = os.path.relpath(source, target.parent)
    if target.is_symlink() and os.readlink(target) == relative:
        return
    if target.exists() or target.is_symlink():
        raise RuntimeError(f"Refusing to replace unexpected overlay entry: {target}")
    target.symlink_to(relative, target_is_directory=source.is_dir())


def prepare_overlay() -> None:
    for path, expected in EXPECTED.items():
        if digest(path) != expected:
            raise RuntimeError(f"Pinned executable digest mismatch: {path}")
    (OVERLAY / "bin").mkdir(parents=True, exist_ok=True)
    (OVERLAY / "libexec").mkdir(parents=True, exist_ok=True)
    for source in sorted(OFFICIAL.iterdir()):
        if source.name != "bin":
            link(OVERLAY / source.name, source)
    for source in sorted((OFFICIAL / "bin").iterdir()):
        target = OVERLAY / "bin" / source.name
        if source.name in ("lean", "lake"):
            # Lake prepends its own bin directory in `lake env`. Keeping both
            # real executables in this root makes its joint-home discovery
            # agree with the compiler overlay. A symlink would canonicalize
            # back to the original root and bypass the child Lean launcher.
            payload = OVERLAY / "libexec" / source.name
            if not payload.exists():
                shutil.copyfile(source, payload)
                payload.chmod(0o755)
            if digest(payload) != EXPECTED[source]:
                raise RuntimeError(f"Relocated executable digest mismatch: {payload}")
            script = "#!/bin/sh\nexec " + shlex.quote(str(QEMU)) + " " + shlex.quote(str(payload)) + ' "$@"\n'
            if target.is_symlink():
                raise RuntimeError(f"Unexpected launcher symlink: {target}")
            if target.exists() and target.read_text() != script:
                raise RuntimeError(f"Refusing to replace changed launcher: {target}")
            if not target.exists():
                target.write_text(script)
                target.chmod(0o755)
        else:
            link(target, source)


def environment() -> tuple[dict[str, str], dict[str, str]]:
    prepare_overlay()
    env = dict(os.environ)
    for name in UNSET:
        env.pop(name, None)
    overrides = {
        "PATH": str(OVERLAY / "bin") + os.pathsep + env.get("PATH", os.defpath),
        "LEAN_SYSROOT": str(OVERLAY),
        "LAKE_OVERRIDE_LEAN": "true",
        "LD_LIBRARY_PATH": os.pathsep.join((str(OFFICIAL / "lib"), str(OFFICIAL / "lib/lean"))),
        "TMPDIR": str(WORKSPACE / "runtime-tmp"),
        "MATHLIB_CACHE_DIR": str(WORKSPACE / "dependency-cache/mathlib"),
        "XDG_CACHE_HOME": str(WORKSPACE / "dependency-cache/xdg"),
        "XDG_CONFIG_HOME": str(WORKSPACE / "runtime-config"),
        "XDG_STATE_HOME": str(WORKSPACE / "runtime-state"),
        "LEAN_NUM_THREADS": "1",
    }
    for name in ("TMPDIR", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME", "XDG_CONFIG_HOME", "XDG_STATE_HOME"):
        Path(overrides[name]).mkdir(parents=True, exist_ok=True)
    env.update(overrides)
    return env, overrides


def main() -> None:
    env, overrides = environment()
    args = sys.argv[1:]
    if args == ["--describe"]:
        print(json.dumps({
            "workspace": str(WORKSPACE),
            "official_distribution": str(OFFICIAL),
            "overlay": str(OVERLAY),
            "environment_overrides": overrides,
            "cleared_inherited_selectors": UNSET,
            "executables": {str(path): digest(path) for path in EXPECTED},
            "relocated_executables": {name: digest(OVERLAY / "libexec" / name)
                                      for name in ("lean", "lake")},
            "launchers": {name: {"sha256": digest(OVERLAY / "bin" / name),
                                   "content": (OVERLAY / "bin" / name).read_text()}
                          for name in ("lean", "lake")},
        }, indent=2))
        return
    if args[:1] == ["--"]:
        args.pop(0)
    if not args:
        raise SystemExit("Usage: pinned_toolchain.py --describe | -- COMMAND [ARG ...]")
    os.execvpe(args[0], args, env)


if __name__ == "__main__":
    main()

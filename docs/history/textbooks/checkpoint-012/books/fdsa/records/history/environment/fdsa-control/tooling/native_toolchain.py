#!/usr/bin/env python3
"""Run the exact official Lean release natively with scoped path compatibility.

The added library supplies only an absent own-executable pathname from the
process's ELF startup data. It does not emulate instructions, modify the
official executables, alter project pins, or replace proof checking.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import sys


WORKSPACE = Path(__file__).resolve().parents[3]
OFFICIAL = WORKSPACE / "bootstrap/direct-lean/lean-4.35.0-linux"
NATIVE = Path(__file__).resolve().parent / "native"
SHIM = NATIVE / "libapp_path_compat.so"
EXPECTED = {
    OFFICIAL / "bin/lean": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
    OFFICIAL / "bin/lake": "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
    NATIVE / "app_path_compat.c": "80c1d0e92d7c5c258f32ce3709736bf969c6a24148287f99b238324d7bfbcfb6",
    SHIM: "65910335cb5a2a4359e9ebf7dae4de1da7a48cdbf9dee5eabe82c3e4b02d88a9",
}
UNSET = ("LEAN", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH",
         "LAKE_HOME", "LAKE_OVERRIDE_LEAN")


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def environment() -> tuple[dict[str, str], dict[str, str]]:
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("This native compatibility artifact is verified for x86-64 Linux.")
    for path, expected in EXPECTED.items():
        if digest(path) != expected:
            raise RuntimeError(f"Verified executable/source digest mismatch: {path}")
    env = dict(os.environ)
    if env.get("LD_PRELOAD", "") not in ("", str(SHIM)) or env.get("LD_AUDIT"):
        raise RuntimeError("Refusing to replace or mix an existing loader instrumentation setting.")
    for name in UNSET:
        env.pop(name, None)
    overrides = {
        "PATH": str(OFFICIAL / "bin") + os.pathsep + env.get("PATH", os.defpath),
        "LEAN_SYSROOT": str(OFFICIAL),
        "LD_PRELOAD": str(SHIM),
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
            "mode": "native execution with own-executable-path compatibility",
            "workspace": str(WORKSPACE), "official_distribution": str(OFFICIAL),
            "compatibility_library": str(SHIM), "environment_overrides": overrides,
            "cleared_inherited_selectors": UNSET,
            "verified_files": {str(path): digest(path) for path in EXPECTED},
            "thread_note": "LEAN_NUM_THREADS controls compiled-tool task-manager defaults; Lean CLI has its own -j option.",
        }, indent=2))
        return
    if args[:1] == ["--"]:
        args.pop(0)
    if not args:
        raise SystemExit("Usage: native_toolchain.py --describe | -- COMMAND [ARG ...]")
    executable = shutil.which(args[0], path=env["PATH"])
    if executable is None:
        raise FileNotFoundError(f"Command not found: {args[0]}")
    # Normal exec with an absolute path supplies the AT_EXECFN contract used by
    # the compatibility library. Lake's compiler and explicit cache paths are
    # separately checked in the retained native smoke evidence.
    executable = str(Path(executable).absolute())
    os.execve(executable, args, env)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Run the pinned native tools with an initial one-worker Lean CLI setting.

This separate overlay leaves the accepted native and QEMU routes unchanged.
It reuses the same executable-path shim and official payloads; only the Lean
launcher prepends -j1. Later explicit CLI arguments may override that setting.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shlex
import shutil
import sys

import pinned_toolchain as pinned


WORKSPACE = pinned.WORKSPACE
OFFICIAL = pinned.OFFICIAL
OVERLAY = pinned.TOOLCHAINS / "lean-4.35.0-native-j1"
SHIM = pinned.TOOLCHAINS / "native-compat/libconaled_app_path.so"
SOURCE = Path(__file__).with_name("native_app_path.c")
EXPECTED = {
    OFFICIAL / "bin/lean": pinned.EXPECTED[OFFICIAL / "bin/lean"],
    OFFICIAL / "bin/lake": pinned.EXPECTED[OFFICIAL / "bin/lake"],
    SOURCE: "0798e7e0d6b71510dd3f68778af1e487aaa9093af5f7cb1666c22b8605f5fd76",
    SHIM: "8bb82334a2888e37a18b657a16f498cba239aaf3935bf24cc5b59728f6df5a18",
}
UNSET = (*pinned.UNSET, "LD_PRELOAD", "CONALED_SELF_EXE")


def prepare_overlay() -> None:
    for path, expected in EXPECTED.items():
        if pinned.digest(path) != expected:
            raise RuntimeError(f"Pinned execution-input digest mismatch: {path}")
    (OVERLAY / "bin").mkdir(parents=True, exist_ok=True)
    (OVERLAY / "libexec").mkdir(parents=True, exist_ok=True)
    for source in sorted(OFFICIAL.iterdir()):
        if source.name != "bin":
            pinned.link(OVERLAY / source.name, source)
    for source in sorted((OFFICIAL / "bin").iterdir()):
        target = OVERLAY / "bin" / source.name
        if source.name in ("lean", "lake"):
            payload = OVERLAY / "libexec" / source.name
            if not payload.exists():
                shutil.copyfile(source, payload)
                payload.chmod(0o755)
            if pinned.digest(payload) != EXPECTED[source]:
                raise RuntimeError(f"Relocated executable digest mismatch: {payload}")
            compiler_args = " -j1" if source.name == "lean" else ""
            script = (
                "#!/bin/sh\n"
                + "export LD_PRELOAD=" + shlex.quote(str(SHIM)) + "\n"
                + "export CONALED_SELF_EXE=" + shlex.quote(str(payload)) + "\n"
                + "exec " + shlex.quote(str(payload)) + compiler_args + ' "$@"\n'
            )
            if target.is_symlink():
                raise RuntimeError(f"Unexpected launcher symlink: {target}")
            if target.exists() and target.read_text() != script:
                raise RuntimeError(f"Refusing to replace changed launcher: {target}")
            if not target.exists():
                target.write_text(script)
                target.chmod(0o755)
        else:
            pinned.link(target, source)


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
            "execution_inputs": {str(p): pinned.digest(p) for p in EXPECTED},
            "relocated_executables": {name: pinned.digest(OVERLAY / "libexec" / name)
                                      for name in ("lean", "lake")},
            "launchers": {name: {"sha256": pinned.digest(OVERLAY / "bin" / name),
                                  "content": (OVERLAY / "bin" / name).read_text()}
                          for name in ("lean", "lake")},
        }, indent=2))
        return
    if args[:1] == ["--"]:
        args.pop(0)
    if not args:
        raise SystemExit("Usage: pinned_native_j1_toolchain.py --describe | -- COMMAND [ARG ...]")
    os.execvpe(args[0], args, env)


if __name__ == "__main__":
    main()

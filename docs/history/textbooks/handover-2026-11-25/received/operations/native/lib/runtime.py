#!/usr/bin/env python3
"""Small, relocatable per-tool launcher. Copied into a source-only profile.

Only the selected ELF receives the adapter, through ld.so --preload. The outer
environment and the inner Lake child environment are deliberately separate.
"""
from __future__ import annotations

import errno
import hashlib
import json
import os
from pathlib import Path
import platform
import sys

SELECTORS = (
    "LEAN", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_AR", "LEAN_CC",
    "LEAN_GITHASH", "LEAN_WORKER_PATH", "LAKE", "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "ELAN_TOOLCHAIN",
    "LD_PRELOAD", "LD_AUDIT", "LD_LIBRARY_PATH", "CONALED_APP_PATH_PID",
    "CONALED_APP_PATH_EXE", "CONALED_SELF_EXE", "CONALED_NATIVE_EXE",
    "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_BASE_URL", "MATHLIB_CACHE_FROM", "MATHLIB_CACHE_REPO_SCOPE",
    "MATHLIB_CACHE_DEBUG_USE_LEGACY",
)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def host_mode() -> str:
    """Do not turn permission failures or mixed proc behavior into compatibility."""
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise RuntimeError("This kit supports Linux x86-64 only.")
    states = []
    for path in (f"/proc/{os.getpid()}/exe", "/proc/self/exe"):
        try:
            os.readlink(path)
            states.append("available")
        except OSError as error:
            if error.errno != errno.ENOENT:
                raise RuntimeError(f"Executable discovery failed with {error.strerror}: {path}") from error
            states.append("missing")
    if states == ["available", "available"]:
        return "native"
    if states == ["missing", "missing"]:
        return "compat"
    raise RuntimeError("Mixed executable-discovery results; inspect the host before using this profile.")


def load_config(profile: Path) -> dict:
    config = json.loads((profile / "config.json").read_text())
    if config.get("schema") != 2:
        raise RuntimeError("Unsupported profile; prepare a fresh source-only profile.")
    return config


def toolchain_path(profile: Path, config: dict) -> Path:
    return (profile / config["toolchain"]).resolve(strict=True)


def check_watched_files(profile: Path, config: dict) -> None:
    official = toolchain_path(profile, config)
    for relative, recorded in config.get("official_watch", {}).items():
        status = (official / relative).stat()
        if status.st_size != recorded["bytes"] or status.st_mtime_ns != recorded["mtime_ns"]:
            raise RuntimeError(f"Official runtime file changed: {relative}. Run verify --full and prepare a fresh profile.")


def child_environment(profile: Path, config: dict, inherited: dict | None = None) -> dict:
    """Retain every search path established by Lake or a project checker."""
    env = dict(os.environ if inherited is None else inherited)
    for name in ("LD_PRELOAD", "LD_AUDIT", "CONALED_APP_PATH_PID", "CONALED_APP_PATH_EXE", "LEAN_NUM_THREADS"):
        env.pop(name, None)
    official = toolchain_path(profile, config)
    check_watched_files(profile, config)
    additions = [str(official / "lib"), str(official / "lib/lean")]
    existing = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = os.pathsep.join(dict.fromkeys(additions + ([existing] if existing else [])))
    return env


def outer_environment(profile: Path, config: dict, state: Path,
                      inherited: dict | None = None) -> dict:
    env = dict(os.environ if inherited is None else inherited)
    for name in SELECTORS:
        env.pop(name, None)
    env.update({
        "PATH": str(profile / "bin") + os.pathsep + env.get("PATH", os.defpath),
        "LEAN_SYSROOT": str(profile),
        "LAKE_OVERRIDE_LEAN": "true",
        "MATHLIB_CACHE_DIR": str(state / "cache/mathlib"),
        "XDG_CACHE_HOME": str(state / "cache/xdg"),
        "XDG_CONFIG_HOME": str(state / "config"),
        "XDG_STATE_HOME": str(state / "runtime-state"),
        "TMPDIR": str(state / "tmp"),
    })
    return child_environment(profile, config, env)


def checked_file(path: Path, expected: str, label: str) -> None:
    if path.is_symlink() or not path.is_file() or digest(path) != expected:
        raise RuntimeError(f"{label} changed or is missing: {path}; run verify, do not change the expected hash.")


def launch_payload(profile: Path, payload: Path, expected: str,
                   arguments: list[str], env: dict | None = None) -> None:
    profile = profile.resolve(strict=True)
    config = load_config(profile)
    checked_file(payload, expected, "Executable")
    if payload.resolve(strict=True) != payload:
        raise RuntimeError("Executable must use its canonical absolute path.")
    with payload.open("rb") as stream:
        if stream.read(4) != b"\x7fELF":
            raise RuntimeError("The native launcher accepts ELF executables only.")
    current = child_environment(profile, config, env)
    mode = host_mode()
    if mode == "native":
        os.execve(str(payload), [str(payload), *arguments], current)
    shim = profile / "app_path.so"
    checked_file(shim, config["adapter_sha256"], "Adapter")
    loader = Path(config["loader"])
    # Host loader identity is recorded at setup, rather than frozen to ADWH's host.
    if not loader.is_file() or digest(loader) != config["loader_sha256"]:
        raise RuntimeError("Host loader changed; create a new profile and rerun smoke.")
    current["CONALED_APP_PATH_PID"] = str(os.getpid())
    current["CONALED_APP_PATH_EXE"] = str(payload)
    os.execve(str(loader), [str(loader), "--preload", str(shim), str(payload), *arguments], current)


def main() -> None:
    profile = Path(__file__).resolve().parent
    args = sys.argv[1:]
    config = load_config(profile)
    if not args or args[0] not in config["tools"]:
        raise RuntimeError("Call a generated lean/lake/leanir/leanc wrapper.")
    name = args[0]
    launch_payload(profile, profile / "libexec" / name, config["tools"][name], args[1:])


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"conaled-native: {error}", file=sys.stderr)
        raise SystemExit(2)

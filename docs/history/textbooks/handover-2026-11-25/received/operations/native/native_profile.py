#!/usr/bin/env python3
"""Prepare and run a source-only profile for the exact Lean 4.35.0 distribution."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "lib"))
import runtime


def pins() -> dict:
    value = json.loads((HERE / "PINS.json").read_text())
    if value.get("schema") != 1:
        raise RuntimeError("Unsupported native input pins.")
    return value


def project_pins(project: Path) -> Path:
    project = project.resolve(strict=True)
    for name, expected in pins()["project_files"].items():
        runtime.checked_file(project / name, expected, "Project pin")
    return project


def official_inputs(official: Path) -> dict:
    official = official.resolve(strict=True)
    data = pins()
    for name in data["required_directories"]:
        path = official / name
        if not path.is_dir() or not path.resolve().is_relative_to(official):
            raise RuntimeError(f"Missing or externally linked toolchain directory: {name}")
    for record in data["official_files"]:
        path = official / record["path"]
        if not path.is_file() or not path.resolve().is_relative_to(official):
            raise RuntimeError(f"Missing or externally linked official input: {record['path']}")
        if path.stat().st_size != record["bytes"] or runtime.digest(path) != record["sha256"]:
            raise RuntimeError(f"Official input differs: {record['path']}")
    return {"files_checked": len(data["official_files"]), "scope": data["verification_scope"]}


def profile_at(state: Path) -> Path:
    state = state.expanduser().absolute()
    if state.is_symlink() or state != state.resolve():
        raise RuntimeError("State must be a canonical path without symlink components.")
    if any(c.isspace() or c == ":" for c in str(state)):
        raise RuntimeError("State path must contain no whitespace or colon.")
    return state / "profile"


def verify_profile(state: Path) -> tuple[Path, dict]:
    profile = profile_at(state)
    for directory in (profile, profile / "bin", profile / "libexec"):
        if directory.is_symlink() or not directory.is_dir():
            raise RuntimeError(f"Missing or changed profile directory: {directory}")
    cfg = runtime.load_config(profile)
    if cfg["pins_sha256"] != runtime.digest(HERE / "PINS.json"):
        raise RuntimeError("Profile input pins differ; prepare a fresh state.")
    for name in ("runtime.py", "app_path.c"):
        expected = runtime.digest(HERE / "lib" / name)
        runtime.checked_file(profile / name, expected, "Profile source")
    runtime.checked_file(profile / "app_path.so", cfg["adapter_sha256"], "Adapter")
    expected_tools = {r["path"][4:]: r["sha256"] for r in pins()["official_files"]
                      if r["path"] in {"bin/" + t for t in pins()["tools"]}}
    if cfg["tools"] != expected_tools:
        raise RuntimeError("Profile tool identities differ from the exact pins.")
    for name, expected in expected_tools.items():
        runtime.checked_file(profile / "libexec" / name, expected, "Profile executable")
        runtime.checked_file(profile / "bin" / name, cfg["wrappers"][name], "Tool wrapper")
    for name, expected in cfg["links"].items():
        path = profile / name
        if not path.is_symlink() or os.readlink(path) != expected or not path.exists():
            raise RuntimeError(f"Missing or changed profile link: {name}")
    if runtime.digest(Path(cfg["loader"])) != cfg["loader_sha256"]:
        raise RuntimeError("Host loader changed; prepare a fresh state.")
    runtime.check_watched_files(profile, cfg)
    return profile, cfg


def prepare(state: Path, official: Path, project: Path) -> dict:
    project = project_pins(project)
    profile = profile_at(state)
    state = profile.parent
    if state.exists():
        raise RuntimeError("Prepare requires a new state directory; existing state was preserved.")
    if state.is_relative_to(project) or state.is_relative_to(HERE.parent.parent):
        raise RuntimeError("Place state outside the project and checkpoint.")
    official = official.resolve(strict=True)
    verification = official_inputs(official)
    compiler = shutil.which("cc") or shutil.which("gcc")
    if compiler is None:
        raise RuntimeError("A host C compiler (cc or gcc) is required.")
    mode = runtime.host_mode()
    env = dict(os.environ)
    for name in (*runtime.SELECTORS, "LEAN_NUM_THREADS"):
        env.pop(name, None)
    # Use the loader belonging to the compiler that builds the adapter. On
    # NixOS /lib64 can name nix-ld, a trampoline rather than the glibc loader.
    compiler_loader = subprocess.run(
        [compiler, "-print-file-name=ld-linux-x86-64.so.2"],
        env=env, capture_output=True, text=True)
    reported = Path(compiler_loader.stdout.strip())
    candidates = ([reported] if compiler_loader.returncode == 0 and reported.is_absolute() else [])
    candidates += [Path("/lib64/ld-linux-x86-64.so.2"),
                   Path("/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2")]
    loader = next((p.resolve() for p in candidates if p.is_file()), None)
    if loader is None:
        raise RuntimeError("A glibc Linux x86-64 loader is required.")
    help_result = subprocess.run([str(loader), "--help"], env=env, capture_output=True, text=True)
    if help_result.returncode or "--preload" not in help_result.stdout:
        raise RuntimeError("The glibc loader must support per-program --preload.")
    state.mkdir()
    for name in ("tmp", "cache/mathlib", "cache/xdg", "config", "runtime-state"):
        (state / name).mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".profile-", dir=state))
    try:
        (stage / "bin").mkdir()
        (stage / "libexec").mkdir()
        for source in official.iterdir():
            if source.name != "bin":
                (stage / source.name).symlink_to(os.path.relpath(source, profile),
                                               target_is_directory=source.is_dir())
        records = {r["path"]: r for r in pins()["official_files"]}
        tools = {}
        wrappers = {}
        for source in sorted((official / "bin").iterdir()):
            target = stage / "bin" / source.name
            if source.name in pins()["tools"]:
                expected = records["bin/" + source.name]["sha256"]
                runtime.checked_file(source, expected, "Official executable")
                shutil.copy2(source, stage / "libexec" / source.name)
                (stage / "libexec" / source.name).chmod(0o755)
                target.write_text('#!/bin/sh\nset -eu\nprofile=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)\n'
                                  'exec python3 "$profile/runtime.py" ' + source.name + ' "$@"\n')
                target.chmod(0o755)
                tools[source.name] = expected
                wrappers[source.name] = runtime.digest(target)
            else:
                target.symlink_to(os.path.relpath(source, profile / "bin"))
        for name in ("runtime.py", "app_path.c"):
            shutil.copy2(HERE / "lib" / name, stage / name)
        command = [compiler, "-std=c11", "-O2", "-fPIC", "-shared", "-Wall", "-Wextra",
                   "-Werror", "-Wl,-z,relro,-z,now", "-o", str(stage / "app_path.so"),
                   str(stage / "app_path.c")]
        built = subprocess.run(command, env=env, capture_output=True, text=True)
        if built.returncode:
            raise RuntimeError("Adapter compilation failed: " + built.stderr)
        cfg = {"schema": 2, "toolchain": os.path.relpath(official, profile),
               "pins_sha256": runtime.digest(HERE / "PINS.json"), "tools": tools,
               "wrappers": wrappers, "adapter_sha256": runtime.digest(stage / "app_path.so"),
               "loader": str(loader), "loader_sha256": runtime.digest(loader),
               "initial_host_mode": mode,
               "links": {str(p.relative_to(stage)): os.readlink(p)
                         for p in [*stage.iterdir(), *(stage / "bin").iterdir()] if p.is_symlink()},
               "official_watch": {r["path"]: {"bytes": (official / r["path"]).stat().st_size,
                                                "mtime_ns": (official / r["path"]).stat().st_mtime_ns}
                                  for r in pins()["official_files"]}}
        (stage / "config.json").write_text(json.dumps(cfg, indent=2) + "\n")
        stage.rename(profile)
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    verify_profile(state)
    return {"passed": True, "profile": str(profile), "project": str(project),
            "toolchain": str(official), "host_mode": mode,
            "official_inputs": verification, "dependencies_checked": False,
            "project_acceptance": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", required=True, type=Path)
    sub = parser.add_subparsers(dest="command", required=True)
    setup = sub.add_parser("prepare", help="Create a new profile from an existing exact complete distribution.")
    setup.add_argument("--toolchain", required=True, type=Path)
    setup.add_argument("--project", required=True, type=Path)
    run = sub.add_parser("run", help="Run a project command without imposed resource limits.")
    run.add_argument("--project", required=True, type=Path)
    run.add_argument("args", nargs=argparse.REMAINDER)
    verify = sub.add_parser("verify", help="Check profile integrity and optional project/full official inputs.")
    verify.add_argument("--project", type=Path)
    verify.add_argument("--full", action="store_true")
    checked = sub.add_parser("exec", help="Launch a caller-hashed ELF, retaining Lake's child search paths.")
    checked.add_argument("--executable", required=True, type=Path)
    checked.add_argument("--sha256", required=True)
    checked.add_argument("args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command == "prepare":
        print(json.dumps(prepare(args.state, args.toolchain, args.project), indent=2))
        return 0
    if args.command == "verify":
        profile, cfg = verify_profile(args.state)
        project = project_pins(args.project) if args.project else None
        report = {"passed": True, "profile": str(profile),
                  "host_mode": runtime.host_mode(),
                  "project": str(project) if project else None,
                  "project_acceptance": False, "dependencies_checked": False}
        if args.full:
            report["official_inputs"] = official_inputs(runtime.toolchain_path(profile, cfg))
        print(json.dumps(report, indent=2))
        return 0
    if args.command == "exec":
        profile, _ = verify_profile(args.state)
        if re.fullmatch(r"[0-9a-f]{64}", args.sha256) is None:
            raise RuntimeError("Expected SHA-256 must be 64 lowercase hexadecimal digits.")
        command = args.args[1:] if args.args[:1] == ["--"] else args.args
        runtime.launch_payload(profile, args.executable.absolute(), args.sha256, command)
        return 2
    project = project_pins(args.project)
    profile, cfg = verify_profile(args.state)
    command = args.args[1:] if args.args[:1] == ["--"] else args.args
    if not command:
        parser.error("run needs -- COMMAND [ARG ...]")
    if command[:2] == ["lake", "update"]:
        raise RuntimeError("This route is pinned; lake update is not a repair.")
    os.chdir(project)
    os.execvpe(command[0], command, runtime.outer_environment(profile, cfg, profile.parent))
    return 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"conaled-native: {error}", file=sys.stderr)
        raise SystemExit(2)

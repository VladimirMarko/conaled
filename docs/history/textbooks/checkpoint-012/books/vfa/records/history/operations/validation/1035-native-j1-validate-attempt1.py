#!/usr/bin/env python3
"""Validate a captured native-j1 operational candidate in a separate checkout."""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = "0afe0faa014512a0375bb158b6c8a56817075319"
SOURCE_SHA = "2556c4c895a747bc0092239b5dc5b220e8a6d4d6cf8a6f9fe66ab96fa2462dc7"
OUTPUT_SHA = "133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c"
RECORDER_SHA = "8e5211cd4fd0e6a2eff593af32bea41409675e3165a86946d36dc4156640614a"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True)
    args = parser.parse_args()
    repo = ROOT / "work-state/native-environment-review"
    isolated = ROOT / "native-j1-environment-validation"
    evidence = ROOT / "work-state/validation/1035-native-j1-isolated"
    evidence.mkdir(mode=0o700)
    recorder_path = ROOT / "work-state/validation-recorder/recorder.py"
    assert sha(recorder_path) == RECORDER_SHA
    spec = importlib.util.spec_from_file_location("accepted_recorder", recorder_path)
    recorder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recorder)
    record = {"started_utc": now(), "base": BASE, "candidate": args.candidate,
              "isolated_checkout": str(isolated), "commands": [],
              "state": "running", "formal_validation": False,
              "scope": "Separate operational candidate checks; no chapter credit."}

    def save():
        (evidence / "result.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(name, command, cwd, timeout=60):
        item = {"name": name, "command": command, "cwd": str(cwd),
                "started_utc": now(), "timeout_seconds": timeout}
        record["commands"].append(item)
        save()
        started = time.monotonic()
        stdout_path, stderr_path = evidence / (name + ".stdout.log"), evidence / (name + ".stderr.log")
        with stdout_path.open("xb", buffering=0) as out, stderr_path.open("xb", buffering=0) as err:
            child = subprocess.Popen(command, cwd=cwd, stdin=subprocess.DEVNULL,
                                     stdout=out, stderr=err, start_new_session=True)
            item["owned_child_pid"] = child.pid
            item["timed_out"] = False
            try:
                item["returncode"] = child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                item["timed_out"] = True
                item["cleanup"] = recorder.stop_owned_child(child, 5)
                item["returncode"] = child.returncode
            os.fsync(out.fileno())
            os.fsync(err.fileno())
        item.update({"finished_utc": now(), "elapsed_seconds": time.monotonic() - started,
                     "stdout_log": str(stdout_path.relative_to(ROOT)),
                     "stderr_log": str(stderr_path.relative_to(ROOT)),
                     "child_reaped": child.returncode is not None,
                     "descendant_quiescence_verified": False})
        save()
        print(name, item["returncode"], round(item["elapsed_seconds"], 3), flush=True)
        if item["timed_out"] or item["returncode"] != 0:
            raise RuntimeError("Operational check failed: " + name)
        return stdout_path.read_text()

    try:
        assert not isolated.exists()
        run("clone", ["git", "clone", "--quiet", "--no-hardlinks", str(repo), str(isolated)], ROOT)
        run("checkout", ["git", "checkout", "--quiet", "--detach", args.candidate], isolated)
        assert run("head", ["git", "rev-parse", "HEAD"], isolated).strip() == args.candidate
        run("base-ancestor", ["git", "merge-base", "--is-ancestor", BASE, args.candidate], isolated)
        assert run("initial-status", ["git", "status", "--porcelain=v1", "--untracked-files=all"], isolated) == ""
        paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=isolated).decode().split("\0")
        initial = {p: sha(isolated / p) for p in paths if p}
        record["initial_source_hashes"] = initial
        protected = [ROOT / "work-state/tooling/pinned_native_toolchain.py",
                     ROOT / "work-state/tooling/NATIVE.md",
                     ROOT / "work-state/tooling/native_app_path.c",
                     ROOT / "toolchains/native-compat/libconaled_app_path.so",
                     ROOT / "toolchains/lean-4.35.0-native/bin/lean",
                     ROOT / "toolchains/lean-4.35.0-native/bin/lake"]
        protected_before = {str(p): sha(p) for p in protected}
        record["protected_input_hashes"] = protected_before
        toolchains = isolated / "toolchains"
        toolchains.mkdir()
        official = ROOT / "toolchains/lean-4.35.0-linux"
        (toolchains / "lean-4.35.0-linux").symlink_to(official, target_is_directory=True)
        compat = toolchains / "native-compat"
        compat.mkdir()
        original_shim = ROOT / "toolchains/native-compat/libconaled_app_path.so"
        shutil.copyfile(original_shim, compat / original_shim.name)
        assert sha(compat / original_shim.name) == "8bb82334a2888e37a18b657a16f498cba239aaf3935bf24cc5b59728f6df5a18"
        helper = isolated / "work-state/tooling/pinned_native_j1_toolchain.py"
        prefix = [sys.executable, "-B", str(helper)]
        description = json.loads(run("describe", prefix + ["--describe"], isolated))
        record["launcher_description"] = description
        overlay = toolchains / "lean-4.35.0-native-j1"
        lean_wrapper = (overlay / "bin/lean").read_text()
        lake_wrapper = (overlay / "bin/lake").read_text()
        assert ' -j1 "$@"' in lean_wrapper and "-j1" not in lake_wrapper
        assert "mmap" not in lean_wrapper and "mmap" not in lake_wrapper
        assert "libconaled_app_path.so" in lean_wrapper
        lean_version = run("lean-version", prefix + ["--", "lean", "--version"], isolated)
        assert "version 4.35.0" in lean_version and "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in lean_version
        lake_version = run("lake-version", prefix + ["--", "lake", "--version"], isolated)
        assert "5.0.0-src+eb6cafb" in lake_version
        prior = json.loads((ROOT / "work-state/validation/1033-native-environment/isolated-validation.json").read_text())
        fixture = isolated / "runtime-tmp/minimal-lake-fixture"
        fixture.mkdir()
        data = prior["fixture"]
        (fixture / "lakefile.toml").write_text(data["lakefile_toml"] + '\n[[lean_lib]]\nname = "Smoke"\n')
        (fixture / "lean-toolchain").write_text(data["lean_toolchain"])
        (fixture / "Smoke.lean").write_text(data["source"])
        assert sha(fixture / "Smoke.lean") == data["source_sha256"]
        child_path = run("lake-child-path", prefix + ["--", "lake", "env", sys.executable,
                         "-B", "-c", 'import shutil; print(shutil.which("lean"))'], fixture).strip()
        assert child_path == str(overlay / "bin/lean")
        axioms = "'smoke_zero_add' does not depend on any axioms\n'smoke_map_length' does not depend on any axioms\n"
        for name, route in [("bare-kernel", ["lean"]), ("lake-kernel", ["lake", "env", "lean"])]:
            out = run(name, prefix + ["--"] + route + ["--root", str(fixture), "-o",
                      str(fixture / (name + ".olean")), str(fixture / "Smoke.lean")], fixture)
            assert out == axioms
        assert sha(fixture / "bare-kernel.olean") == sha(fixture / "lake-kernel.olean")
        run("lake-build", prefix + ["--", "lake", "--no-cache", "--rehash", "-v", "build", "+Smoke"], fixture)
        build_log = (evidence / "lake-build.stdout.log").read_text() + (evidence / "lake-build.stderr.log").read_text()
        assert str(overlay / "bin/lean") in build_log
        assert (fixture / ".lake/build/lib/lean/Smoke.olean").is_file()
        private_imports = fixture / "private-imports"
        private_imports.mkdir()
        shutil.copyfile(fixture / "bare-kernel.olean", private_imports / "Smoke.olean")
        runner_source = 'import Smoke\n\ndef main (args : List String) : IO Unit :=\n  IO.println (String.intercalate "|" args)\n'
        (fixture / "Runner.lean").write_text(runner_source)
        args_output = run("private-path-run-args", prefix + ["--", "env", "LEAN_PATH=" + str(private_imports),
                          "lean", "--root", str(fixture), "--run", str(fixture / "Runner.lean"),
                          "space value", "--literal=kept", "plain"], fixture)
        assert args_output == "space value|--literal=kept|plain\n"
        record["route_fixtures"] = {
            "lakefile_toml": (fixture / "lakefile.toml").read_text(),
            "init_source": data["source"], "runner_source": runner_source,
            "private_path_set_after_outer_helper": str(private_imports),
            "literal_args_preserved": True,
            "lake_internal_build_compiler_path": str(overlay / "bin/lean"),
            "lake_built_olean_sha256": sha(fixture / ".lake/build/lib/lean/Smoke.olean")}
        original = ROOT / "runtime-tmp/1035-original-squares-probe/Squares.lean"
        assert sha(original) == SOURCE_SHA
        shutil.copyfile(original, fixture / "Squares.lean")
        run("original-squares", prefix + ["--", "lean", "--root", str(fixture), "-o",
             str(fixture / "Squares.olean"), str(fixture / "Squares.lean")], fixture)
        assert sha(fixture / "Squares.olean") == OUTPUT_SHA
        record["proof_outputs"] = {name: sha(fixture / name) for name in
                                   ("Smoke.lean", "bare-kernel.olean", "lake-kernel.olean", "Squares.lean", "Squares.olean")}
        run("tracked-source-unchanged", ["git", "diff", "--exit-code", "HEAD", "--"], isolated)
        assert {p: sha(isolated / p) for p in initial} == initial
        assert all(sha(Path(p)) == h for p, h in protected_before.items())
        record["protected_inputs_unchanged"] = True
        record["tracked_source_unchanged"] = True
        record["reused_validation"] = {
            "accepted_native_candidate": "e41336d46dffd7bddd42b242a7ea7484a6055e43",
            "readlink_source_sha256": "0798e7e0d6b71510dd3f68778af1e487aaa9093af5f7cb1666c22b8605f5fd76",
            "readlink_binary_sha256": sha(compat / original_shim.name),
            "basis": "Unchanged source/binary and official payloads. Reuse #1033 shim boundaries; current checks exercise new helper and generated wrappers from captured candidate."}
        record["state"] = "passed"
    except BaseException as exc:
        record["state"] = "failed"
        record["error"] = repr(exc)
        raise
    finally:
        record["finished_utc"] = now()
        save()
    print(json.dumps({"state": record["state"], "candidate": args.candidate,
                      "commands": len(record["commands"]), "evidence": str(evidence / "result.json")}))


if __name__ == "__main__":
    main()

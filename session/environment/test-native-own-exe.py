#!/usr/bin/env python3
"""Record bounded public readlink contract checks against an existing native profile.

This runner compiles only its owned C fixtures. It never builds the adapter,
creates a toolchain profile, or invokes Lean/Lake/project gates. Every run uses
a new output record and fixture directory; earlier evidence is never replaced.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def append_preload(inherited, *paths):
    suffix = " ".join(str(path) for path in paths)
    return inherited + (" " if inherited and suffix else "") + suffix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--profile-identity", type=Path)
    parser.add_argument("--record", type=Path, required=True)
    args = parser.parse_args()
    root = args.workspace.resolve()
    record_path = args.record.resolve()
    require(record_path.parent == root / "session/validation",
            "Records must be in this workspace's session/validation directory.")
    require(record_path.name.startswith("native-own-exe-contract-042-r") and
            record_path.suffix == ".json", "Use a new native-own-exe-contract-042-r*.json record.")
    require(not record_path.exists(), "Refusing to replace earlier validation evidence.")
    receipt_path = (args.profile_identity or
                    root / "session/environment/native-profile-identity-042-r2.json").resolve()
    profile = root / "toolchains/lean-4.35.0-native"
    adapter = profile / "support/native-own-exe.so"
    environment = root / "session/environment"
    helper = environment / "run-native-toolchain.py"
    probe_source = environment / "test-native-own-exe.c"
    layer_source = environment / "native-readlink-fixture.c"
    adapter_source = environment / "native-own-exe.c"
    baseline = root / "session/validation/native-own-exe-red-042.json"
    receipt = json.loads(receipt_path.read_text())
    require(receipt["execution"] == "native" and receipt["profile"] == str(profile),
            "The supplied identity is not this native profile.")
    require(json.loads((profile / "profile-identity.json").read_text()) == receipt,
            "Profile identity differs from the supplied frozen receipt.")
    require(sha(adapter) == receipt["compatibility_library_sha256"],
            "Native compatibility library differs from its frozen receipt.")
    require(sha(adapter_source) == receipt["compatibility_source_sha256"],
            "Native adapter source differs from its frozen receipt.")
    require(sha(helper) == receipt["profile_helper_sha256"],
            "Native helper differs from its frozen receipt.")
    compiler = Path(receipt["c_compiler"])
    require(sha(compiler) == receipt["c_compiler_sha256"],
            "The C compiler differs from the native profile's recorded compiler.")

    inputs = [Path(__file__).resolve(), probe_source, layer_source, adapter_source,
              helper, adapter, receipt_path, profile / "profile-identity.json",
              compiler, baseline]
    before = {str(path): sha(path) for path in inputs}
    fixture_dir = root / "session/tools" / record_path.stem
    require(not fixture_dir.exists(), "Refusing to reuse an earlier fixture directory.")
    fixture_dir.mkdir(parents=True)
    probe = fixture_dir / "probe"
    child = fixture_dir / "different-probe"
    layer = fixture_dir / "controlled-readlink.so"
    target = fixture_dir / "target.txt"
    target.write_text("owned public test fixture\n")
    link = fixture_dir / "ordinary-link"
    link.symlink_to("target.txt")
    missing = fixture_dir / "absent"
    changed_cwd = fixture_dir / "changed-cwd"
    changed_cwd.mkdir()
    inherited_preload = os.environ.get("LD_PRELOAD", "")
    base_env = os.environ.copy()
    for key in ("PFDS_NATIVE_EXECUTABLE", "PFDS_NATIVE_FIXTURE_MODE",
                "PFDS_NATIVE_REQUIRE_FIXTURE", "PFDS_PROBE_CTOR_EXPECTED"):
        base_env.pop(key, None)
    record = {
        "schema": 1,
        "scope": "Public native readlink ABI and actual launcher fixture tests only",
        "started_at": now(),
        "status": "running",
        "formal_acceptance": False,
        "review_status": "unreviewed implementation evidence",
        "profile": str(profile),
        "fixture_directory": str(fixture_dir),
        "inputs_before": before,
        "inherited_preload": {
            "present": bool(inherited_preload),
            "sha256": hashlib.sha256(inherited_preload.encode()).hexdigest(),
            "contents_recorded": False,
            "preservation": "Existing entries remain first and retain their exact relative order.",
        },
        "tdd_context": {
            "existing_actual_red_record": str(baseline),
            "sha256": before[str(baseline)],
            "scope": "Earlier genuine own-path failure remains unchanged; new tests are not retroactively described as earlier red outcomes.",
        },
        "unsupported": [
            "scripts", "direct dynamic-loader invocation", "descriptor execution",
            "mutable or renamed executable images", "asynchronous signal handlers",
            "invalid pointers", "other libc/architecture ABIs", "static or secure execution",
            "readlinkat and fortified alternate entry points",
        ],
        "commands": [],
        "cases": [],
    }

    def save():
        record_path.write_text(json.dumps(record, indent=2) + "\n")

    def run_command(argv, env, *, case=None, labels=(), context=None):
        started = time.monotonic()
        try:
            result = subprocess.run(argv, cwd=root, env=env, text=True,
                                    capture_output=True, timeout=30, check=False)
            outcome = {
                "argv": [str(item) for item in argv],
                "returncode": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "seconds": time.monotonic() - started,
                "timed_out": False,
            }
        except subprocess.TimeoutExpired as exc:
            def as_text(value):
                return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
            outcome = {
                "argv": [str(item) for item in argv], "returncode": None,
                "stdout": as_text(exc.stdout), "stderr": as_text(exc.stderr),
                "seconds": time.monotonic() - started, "timed_out": True,
            }
        if context:
            outcome["controlled_environment"] = context
        record["commands"].append(outcome)
        passed = outcome["returncode"] == 0
        if case:
            observed = [line.split("=", 1)[0] for line in outcome["stdout"].splitlines()
                        if "=passed" in line]
            absent = [label for label in labels if label not in observed]
            passed = passed and not absent and "=failed" not in outcome["stdout"]
            record["cases"].append({
                "name": case, "command_index": len(record["commands"]) - 1,
                "expected_labels": list(labels), "missing_labels": absent, "passed": passed,
            })
        save()
        return passed

    save()
    try:
        common = [str(compiler), "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2"]
        require(run_command(common + [str(probe_source), "-o", str(probe), "-ldl", "-pthread"],
                            base_env), "Public executable fixture did not compile.")
        require(run_command(common + ["-fPIC", "-fvisibility=hidden", "-shared",
                                      str(layer_source), "-o", str(layer), "-ldl", "-pthread"],
                            base_env), "Controlled downstream fixture did not compile.")
        shutil.copy2(probe, child)
        require(probe.resolve() == probe and child.resolve() == child,
                "Fixture executables must have canonical absolute paths.")
        require(sha(probe) == sha(child), "Copied child fixture differs from the built fixture.")
        record["fixture_binaries"] = {str(path): sha(path) for path in (probe, child, layer)}
        ordinary = ["zero-size", "ordinary-link", "ordinary-link-truncated",
                    "regular-file", "missing-file"]
        successful = ["own-pid", "self", "one-byte", "truncation",
                      "exact-buffer", "larger-buffer"] + ordinary
        refused = ["own-pid-refused", "self-refused"] + ordinary

        def command(executable, mode, expected, extra=()):
            return [str(executable), mode, str(expected), str(link), "target.txt",
                    str(target), str(missing), *map(str, extra)]

        def launcher_case(name, mode="check", expected=None, *, executable=probe,
                          extra=(), env=None, labels=successful, context=None):
            argv = [sys.executable, str(helper), "--",
                    *command(executable, mode, expected if expected is not None else executable, extra)]
            return run_command(argv, env or base_env, case=name, labels=labels,
                               context=context or {
                                   "launch": "Actual run-native-toolchain.py CLI",
                                   "preload_order": ["inherited entries", "native adapter"],
                                   "marker": "Assigned by actual launcher to this canonical fixture ELF",
                               })

        launcher_case("actual-launcher-buffer-and-filesystem-contract")
        launcher_case("changed-argv0", "reexec-argv0",
                      labels=["changed-argv0"] + successful)
        launcher_case("changed-working-directory", "cwd", extra=[changed_cwd],
                      labels=["changed-cwd"] + successful)
        launcher_case("fork-current-pid", "fork", labels=["before-fork", "fork-current-pid"] + successful)
        launcher_case("concurrent-first-calls", "concurrent",
                      labels=[f"concurrent-first-{i}" for i in range(4)] + successful)
        ctor_env = base_env | {"PFDS_PROBE_CTOR_EXPECTED": str(probe)}
        launcher_case("constructor-first-call", "constructor", env=ctor_env,
                      labels=["constructor-first"] + successful)
        launcher_case("child-exec-stale-parent-marker", "exec-child", "ENOENT",
                      extra=[child], labels=refused)
        launcher_case("child-own-launcher-marker", executable=child)

        native_env = base_env | {"LD_PRELOAD": append_preload(inherited_preload, adapter)}
        for name, marker in (("unset", None), ("empty", ""),
                             ("relative", "probe"), ("stale", str(child))):
            env = native_env.copy()
            if marker is not None:
                env["PFDS_NATIVE_EXECUTABLE"] = marker
            run_command(command(probe, "check", "ENOENT"), env,
                        case=f"marker-{name}-inactive", labels=refused,
                        context={"launch": "Direct public fixture", "marker": marker,
                                 "preload_order": ["inherited entries", "native adapter"]})

        for mode, expected in (("success", "fixture-own-executable"),
                               ("eacces", "EACCES"), ("eperm", "EPERM"),
                               ("eio", "EIO"), ("enoent", str(probe))):
            env = base_env | {
                "LD_PRELOAD": append_preload(inherited_preload, adapter, layer),
                "PFDS_NATIVE_EXECUTABLE": str(probe),
                "PFDS_NATIVE_FIXTURE_MODE": mode,
                "PFDS_NATIVE_REQUIRE_FIXTURE": "1",
            }
            labels = successful if mode in ("success", "enoent") else refused
            run_command(command(probe, "check" if mode == "enoent" else "controlled", expected),
                        env, case=f"controlled-downstream-{mode}",
                        labels=labels + ["controlled-layer-reached"],
                        context={"launch": "Explicit controlled fixture chain",
                                 "preload_order": ["inherited entries", "native adapter", "owned downstream fixture"],
                                 "marker": str(probe), "fixture_mode": mode,
                                 "host_protected_path_observation": False})

        upstream_env = base_env | {
            "LD_PRELOAD": append_preload(inherited_preload, layer),
            "PFDS_NATIVE_FIXTURE_MODE": "eacces",
            "PFDS_NATIVE_REQUIRE_FIXTURE": "1",
        }
        launcher_case("actual-launcher-retains-upstream-layer", "controlled", "EACCES",
                      env=upstream_env, labels=refused + ["controlled-layer-reached"],
                      context={"launch": "Actual launcher with an explicit inherited owned test layer",
                               "preload_order": ["inherited entries", "owned upstream fixture", "native adapter"],
                               "fixture_mode": "eacces", "host_protected_path_observation": False})
    except Exception as exc:
        record["fatal_error"] = f"{type(exc).__name__}: {exc}"
    finally:
        after = {str(path): sha(path) if path.is_file() else None for path in inputs}
        record["inputs_after"] = after
        record["inputs_unchanged"] = before == after
        record["case_count"] = len(record["cases"])
        record["passed_cases"] = sum(case["passed"] for case in record["cases"])
        record["completed_at"] = now()
        passed = (not record.get("fatal_error") and record["case_count"] == 18 and
                  record["passed_cases"] == record["case_count"] and record["inputs_unchanged"])
        record["status"] = "passed" if passed else "failed"
        save()
        print(json.dumps({"record": str(record_path), "status": record["status"],
                          "case_count": record["case_count"], "passed_cases": record["passed_cases"],
                          "inputs_unchanged": record["inputs_unchanged"]}, indent=2))
    return 0 if record["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

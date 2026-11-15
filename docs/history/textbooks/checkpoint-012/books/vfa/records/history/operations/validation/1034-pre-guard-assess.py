#!/usr/bin/env python3
"""Prospective #1025 evidence collector; never builds, invalidates, or repairs.

Run ONLY after the fresh attempt ended and the coordinator established idle
inputs. Use the external timeout/recorder command in the adjacent handoff.
Exit 0 means a completed assessment, including one reporting discrepancies.
It does not authorize repair or accept a chapter. Exit 2 means incomplete.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import traceback

sys.dont_write_bytecode = True
WORKSPACE = Path(__file__).resolve().parents[2]
GUARD_SHA = "293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f"
HASH_HELPER_SHA = "fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b"
KNOWN = (
    "Applications.Resources.BoundedSummary", "Examples.BoundedSummary",
    "Applications.Sequences.ByteBuffer", "Examples.ByteBuffer",
)
LIB = ("olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig", "trace")
IR = ("c", "bc", "ltar")
TREES = (".lake/build/lib/lean", ".lake/build/ir")
SUFFIXES = sorted((*LIB, *IR, "setup.json"), key=len, reverse=True)


def utc():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def journal(state, kind, value):
    if state.get("journal_directory"):
        with (Path(state["journal_directory"]) / (kind + ".jsonl")).open("a") as stream:
            stream.write(json.dumps({"recorded_utc": utc(), **value}, sort_keys=True) + "\n")


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def metadata(path):
    info = path.lstat()
    kind = ("file" if stat.S_ISREG(info.st_mode) else
            "directory" if stat.S_ISDIR(info.st_mode) else
            "symlink" if stat.S_ISLNK(info.st_mode) else "special")
    result = {"kind": kind, "size": info.st_size, "mode": stat.S_IMODE(info.st_mode),
              "device": info.st_dev, "inode": info.st_ino,
              "mtime_ns": info.st_mtime_ns, "ctime_ns": info.st_ctime_ns}
    if kind == "symlink":
        result["link_target"] = os.readlink(path)
    return result


def scan(root, limit, result):
    """No directory symlinks are traversed; retain partial results on a limit."""
    def visit(path):
        relative = str(path.relative_to(root))
        item = metadata(path)
        result[relative] = item
        if len(result) > limit:
            raise RuntimeError(f"Inventory entry limit exceeded: {limit}")
        if item["kind"] == "directory":
            for child in sorted(path.iterdir()):
                visit(child)
    for tree in TREES:
        path = root / tree
        if path.exists() or path.is_symlink():
            visit(path)


def copy_raw(source, destination, state, limit):
    """Read source bytes once; independently hash the copy; never copy links."""
    item = {"source": str(source), "destination": str(destination),
            "status": "started", "before": metadata(source)}
    state["copies"].append(item)
    journal(state, "copies", item)
    if item["before"]["kind"] != "file":
        raise RuntimeError(f"Refusing nonregular preservation input: {source}")
    if state["copied_bytes"] + item["before"]["size"] > limit:
        raise RuntimeError(f"Preservation byte limit exceeded: {limit}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    total = 0
    with os.fdopen(os.open(source, os.O_RDONLY | os.O_NOFOLLOW), "rb") as src:
        with destination.open("xb") as dst:
            while block := src.read(1024 * 1024):
                if state["copied_bytes"] + len(block) > limit:
                    raise RuntimeError(f"Preservation byte limit exceeded: {limit}")
                dst.write(block)
                digest.update(block)
                total += len(block)
                state["copied_bytes"] += len(block)
    item.update(after=metadata(source), copied_size=total,
                source_read_sha256=digest.hexdigest(), copy_sha256=sha(destination))
    item["observed_changed"] = (item["before"] != item["after"] or
                                total != item["before"]["size"])
    item["status"] = "copied"
    journal(state, "copies", item)
    if item["observed_changed"] or item["source_read_sha256"] != item["copy_sha256"]:
        raise RuntimeError(f"Changed input or copy digest mismatch: {source}")
    return item


def command(argv, root, env, state):
    result = subprocess.run(argv, cwd=root, env=env, stdin=subprocess.DEVNULL,
                            capture_output=True, text=True)
    state["commands"].append({"argv": argv, "cwd": str(root),
                              "returncode": result.returncode,
                              "stdout": result.stdout, "stderr": result.stderr})
    journal(state, "commands", state["commands"][-1])
    if result.returncode:
        raise RuntimeError(f"Identity command failed: {argv!r}")
    return result.stdout.strip()


def assessment_environment(out):
    env = dict(os.environ)
    env.pop("LEAN", None)
    env.pop("LEAN_PATH", None)
    temporary = str(out / "tmp")
    Path(temporary).mkdir()
    # inspect_outputs uses tempfile in THIS process, before it launches Lean.
    os.environ["TMPDIR"] = temporary
    tempfile.tempdir = temporary
    env.update(LEAN_NUM_THREADS="1", LAKE_ARTIFACT_CACHE="false", GIT_OPTIONAL_LOCKS="0",
               TMPDIR=temporary)
    return env


def dependency_paths(root, dependency_root, manifest):
    """Accept only the nine-package layout explicitly selected by the caller.

    The command entry point binds dependency_root to this recovery's approved
    vfa-validation/.lake/packages directory. Each candidate package must be an
    explicit link to that root's same-named, non-symlink checkout directory.
    """
    if manifest.get("packagesDir") != ".lake/packages":
        raise RuntimeError("Expected the approved .lake/packages manifest layout")
    dependency_root = dependency_root.absolute()
    if dependency_root.resolve(strict=True) != dependency_root:
        raise RuntimeError("Approved dependency root must be a canonical directory")
    local = root / ".lake/packages"
    if local.resolve(strict=True) != local:
        raise RuntimeError("Candidate package directory itself may not be redirected")
    result = {}
    for package in manifest["packages"]:
        name = package.get("name")
        if (package.get("type") != "git" or not isinstance(name, str) or
                name in ("", ".", "..") or "/" in name or "\\" in name or name in result):
            raise RuntimeError("Expected unique, single-component Git package names")
        path = local / name
        expected = dependency_root / name
        if expected.resolve(strict=True) != expected or not expected.is_dir():
            raise RuntimeError(f"Approved package checkout is redirected or not a directory: {name}")
        if not path.is_symlink() or path.resolve(strict=True) != expected:
            raise RuntimeError(f"Dependency does not resolve to its exact approved checkout: {name}")
        result[name] = {"candidate_path": str(path), "link_target": os.readlink(path),
                        "resolved_path": str(expected)}
    return result


def identity(root, dependency_root, env, state, limit):
    # Optional index refreshing and external fsmonitor hooks are disabled.
    def git(path, *args):
        return command(["git", "--no-optional-locks", "-c", "core.fsmonitor=false",
                        "-C", str(path), *args], root, env, state)
    def clean(path):
        if Path(git(path, "rev-parse", "--show-toplevel")).resolve() != path.resolve():
            raise RuntimeError(f"Expected independent Git checkout: {path}")
        head = git(path, "rev-parse", "HEAD")
        status = git(path, "status", "--porcelain", "--untracked-files=all")
        if status:
            raise RuntimeError(f"Checkout is not clean: {path}: {status}")
        return head
    sources = list(root.glob("*.lean"))
    for name in ("SquareKit", "Applications", "Examples"):
        sources.extend((root / name).rglob("*.lean"))
    if len(sources) > limit:
        raise RuntimeError("Integrated source inventory exceeds entry limit")
    tracked = set(git(root, "ls-files", "-z").split("\0"))
    modules = {}
    for source in sorted(sources):
        relative = str(source.relative_to(root))
        if relative not in tracked or metadata(source)["kind"] != "file":
            raise RuntimeError(f"Untracked or nonregular integrated source: {source}")
        modules[".".join(source.relative_to(root).with_suffix("").parts)] = relative
    manifest = json.loads((root / "lake-manifest.json").read_text())
    layout = dependency_paths(root, dependency_root, manifest)
    dependencies = {}
    for package in manifest["packages"]:
        path = Path(layout[package["name"]]["candidate_path"])
        dependencies[package["name"]] = clean(path)
        if dependencies[package["name"]] != package["rev"]:
            raise RuntimeError(f"Dependency differs from manifest: {package['name']}")
    return {"candidate": clean(root), "dependencies": dependencies,
            "dependency_layout": layout, "modules": modules}


def family_paths(module):
    stem = module.replace(".", "/")
    members = [f"{TREES[0]}/{stem}.{extension}" for extension in LIB]
    members += [f"{TREES[1]}/{stem}.{extension}" for extension in IR]
    # Both standard setup location and the observed-name alternative are inventoried.
    members += [f"{tree}/{stem}.setup.json" for tree in TREES]
    return sorted(members + [name + ".hash" for name in members])


def member(relative):
    for tree in TREES:
        if relative.startswith(tree + "/"):
            name = relative[len(tree) + 1:]
            sidecar = name.endswith(".hash")
            if sidecar:
                name = name[:-5]
            for extension in SUFFIXES:
                if name.endswith("." + extension):
                    module = name[:-(len(extension) + 1)].replace("/", ".")
                    if all(part and part.replace("'", "_").isidentifier() for part in module.split(".")):
                        return module, extension, sidecar
                    # Never pass empty/absolute/dot-component identities to the guard.
                    return None, None, False
    return None, None, False


def classify(root, inventory, modules, guard):
    findings, families, mapped = [], {}, {}
    def finding(path, reason, module):
        findings.append({"path": path, "observation": reason, "module": module})
        if module:
            families.setdefault(module, set()).add(reason)
    for path, item in inventory.items():
        if item["kind"] == "directory":
            continue
        module, extension, sidecar = member(path)
        mapped[path] = module
        if module is None:
            finding(path, "unrecognized_file", None)
            continue
        if module not in modules:
            finding(path, "module_absent_from_integrated_sources", module)
        stem = module.replace(".", "/")
        canonical = ({f"{tree}/{stem}.setup.json" for tree in TREES} if extension == "setup.json"
                     else {str(guard.artifact_path(root, module, extension).relative_to(root))})
        if sidecar:
            canonical = {name + ".hash" for name in canonical}
        if path not in canonical:
            finding(path, "member_at_noncanonical_path", module)
        if sidecar and inventory.get(path[:-5], {}).get("kind") != "file":
            finding(path, "sidecar_without_regular_base_file", module)
        trace = f"{TREES[0]}/{module.replace('.', '/')}.trace"
        if extension != "trace" and inventory.get(trace, {}).get("kind") != "file":
            finding(path, "member_without_regular_trace", module)
        if item["kind"] != "file":
            finding(path, "nonregular_member_not_followed", module)
    # Only a fully usable trace permits a surplus-output observation.
    for module in sorted({name for name in mapped.values() if name}):
        try:
            expected = {str(path.relative_to(root)) for path, _ in guard.expected_artifacts(root, module)}
        except (OSError, ValueError, TypeError) as error:
            finding(f"{TREES[0]}/{module.replace('.', '/')}.trace",
                    "trace_unusable_for_surplus_classification: " + str(error), module)
            continue
        for path, name in mapped.items():
            _, extension, sidecar = member(path)
            if name == module and not sidecar and extension in (*LIB[:-1], *IR) and path not in expected:
                finding(path, "output_not_described_by_usable_trace", module)
    return findings, families, mapped


def assess(args, out, state):
    root = args.root.resolve(strict=True)
    dependency_root = WORKSPACE / "vfa-validation/.lake/packages"
    if (dependency_root.resolve(strict=True) != dependency_root or
            args.dependency_root.resolve(strict=True) != dependency_root):
        raise RuntimeError("--dependency-root must select this recovery's approved vfa-validation/.lake/packages")
    state.update(root=str(root), candidate=args.candidate, started_utc=utc(),
                 approved_dependency_root=str(dependency_root),
                 argv=sys.argv, historical_origin="Unresolved; current survivors cannot reconstruct the lost originals.")
    env = assessment_environment(out)
    state["environment"] = {name: env.get(name) for name in
        ("LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN",
         "LD_LIBRARY_PATH", "TMPDIR", "GIT_OPTIONAL_LOCKS")}
    # Reject symlinked managed ancestors before inventory or guard traversal.
    for relative in (".lake", ".lake/build", ".lake/build/lib", *TREES):
        if (root / relative).is_symlink():
            raise RuntimeError(f"Managed ancestor is a symlink: {relative}")
    inputs = (".lake/verification.json", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
              "scripts/lake_integrity.py", "scripts/lake-output-hashes.lean", "scripts/check.py")
    for relative in inputs:
        copy_raw(root / relative, out / "inputs" / relative, state, args.max_copy_bytes)
    copy_raw(Path(__file__).resolve(), out / "inputs/assessment-helper.py", state, args.max_copy_bytes)
    for index, source in enumerate(args.provenance):
        copy_raw(source.resolve(strict=True), out / "inputs" / f"provenance-{index:03d}-{source.name}",
                 state, args.max_copy_bytes)
    fresh = json.loads((out / "inputs/.lake/verification.json").read_text())
    if (fresh.get("format") != 1 or fresh.get("result") != "passed" or
            fresh.get("mode") != "fresh" or fresh.get("candidate") != args.candidate or
            not isinstance(fresh.get("completed_at"), str)):
        raise RuntimeError("A matching current fresh verification record is required")
    if sha(root / "scripts/lake_integrity.py") != GUARD_SHA or sha(root / "scripts/lake-output-hashes.lean") != HASH_HELPER_SHA:
        raise RuntimeError("Accepted integrity adapter/hash-helper identity changed")
    before = identity(root, dependency_root, env, state, args.max_entries)
    state["identity_before"] = before
    if before["candidate"] != args.candidate or before["dependencies"] != fresh.get("dependencies"):
        raise RuntimeError("Candidate or dependencies do not match current fresh record")
    for tool in ("lean", "lake"):
        path = shutil.which(tool, path=env.get("PATH"))
        if path is None:
            raise RuntimeError(f"Missing pinned tool: {tool}")
        state.setdefault("tools", {})[tool] = {"path": path, "sha256": sha(Path(path)),
            "version": command([tool, "--version"], root, env, state)}
    if state["tools"]["lean"]["version"] != fresh.get("compiler"):
        raise RuntimeError("Live compiler does not match current fresh record")
    normal = sorted(set(before["modules"]) - {"ProofAudit"})
    save(out / "targets.json", {"normal_targets": normal, "count": len(normal),
                                "excluded_audit_driver": "ProofAudit"})
    state["targets_sha256"] = sha(out / "targets.json")
    print(json.dumps({"phase": "identity_and_targets_recorded", "target_count": len(normal)}), flush=True)
    scan(root, args.max_entries, state["inventory_before"])
    save(out / "inventory-before.json", state["inventory_before"])
    spec = importlib.util.spec_from_file_location("conaled_readonly_guard", root / "scripts/lake_integrity.py")
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    nonregular = [path for path, item in state["inventory_before"].items()
                  if item["kind"] not in ("file", "directory")]
    if nonregular:
        raise RuntimeError(f"Nonregular managed entries recorded; diagnostic not run: {nonregular}")
    guard.validate_layout(root)
    try:
        bad, count = guard.inspect_outputs(root, normal, env)
        state["inspection"] = {"completed": True, "bad_modules": bad, "hashed_artifact_count": count}
    except Exception:
        bad = {}
        state["inspection"] = {"completed": False, "exception": traceback.format_exc()}
    save(out / "inspection.json", state["inspection"])
    print(json.dumps({"phase": "inspection_recorded", "completed": state["inspection"]["completed"],
                      "bad_module_count": len(bad) if state["inspection"]["completed"] else None}), flush=True)
    findings, reasons, mapped = classify(root, state["inventory_before"], before["modules"], guard)
    selected_families = set(KNOWN) | set(bad) | set(reasons)
    for name in KNOWN:
        reasons.setdefault(name, set()).add("historical_family_preserved_even_if_consistent_or_absent")
    for name in bad:
        reasons.setdefault(name, set()).add("guard_diagnostic: " + bad[name])
    state["physical_observations"] = findings
    state["family_inventory"] = {name: {
        "reasons": sorted(reasons[name]), "source": before["modules"].get(name),
        "not_a_normal_guard_target": name == "ProofAudit",
        "missing_fixed_members": [p for p in family_paths(name) if p not in state["inventory_before"]],
        "present_members": [p for p, module in mapped.items() if module == name],
    } for name in sorted(selected_families)}
    selected = sorted(path for path, module in mapped.items() if module is None or module in selected_families)
    state["selected_paths"] = selected
    save(out / "selection.json", {"physical_observations": findings,
                                  "families": state["family_inventory"], "selected_paths": selected})
    print(json.dumps({"phase": "preservation_selected", "family_count": len(selected_families),
                      "physical_file_count": len(selected)}), flush=True)
    total = sum(state["inventory_before"][path]["size"] for path in selected)
    if total + state["copied_bytes"] > args.max_copy_bytes:
        raise RuntimeError(f"Selected raw evidence exceeds byte budget: {total}; selection retained")
    if shutil.disk_usage(out).free < total + 64 * 1024 * 1024:
        raise RuntimeError("Insufficient free space for selected evidence plus 64 MiB reserve")
    for name in sorted(selected_families & set(before["modules"])):
        relative = before["modules"][name]
        copy_raw(root / relative, out / "sources" / relative, state, args.max_copy_bytes)
    for relative in selected:
        copy_raw(root / relative, out / "artifacts" / relative, state, args.max_copy_bytes)
    state["preservation_complete"] = True
    scan(root, args.max_entries, state["inventory_after"])
    save(out / "inventory-after.json", state["inventory_after"])
    state["identity_after"] = identity(root, dependency_root, env, state, args.max_entries)
    state["observed_changes"] = sorted(path for path in set(state["inventory_before"]) | set(state["inventory_after"])
        if state["inventory_before"].get(path) != state["inventory_after"].get(path))
    for relative in inputs:
        if sha(root / relative) != sha(out / "inputs" / relative):
            state["observed_changes"].append(relative)
    if state["identity_after"] != before or state["observed_changes"]:
        raise RuntimeError("Inputs or managed-output metadata changed during assessment")
    if not state["inspection"]["completed"]:
        raise RuntimeError("Inspector failed; available known/orphan evidence retained, assessment incomplete")
    state["assessment_complete"] = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--dependency-root", type=Path, required=True,
                        help="Exact approved shared root: recovery/vfa-validation/.lake/packages")
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--provenance", type=Path, action="append", required=True,
                        help="Preserved actual fresh outcome, launch/log or environment evidence; repeatable")
    parser.add_argument("--max-entries", type=int, default=100000)
    parser.add_argument("--max-copy-bytes", type=int, default=268435456)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.candidate) or min(args.max_entries, args.max_copy_bytes) <= 0:
        parser.error("Require full candidate SHA and positive finite limits")
    out = args.out.absolute()
    root = args.root.resolve(strict=True)
    if out.exists() or out.is_symlink() or not out.parent.resolve().is_relative_to(WORKSPACE / "work-state/validation"):
        parser.error("Output must be a new directory under this work-state/validation")
    if out.parent.resolve().is_relative_to(root):
        parser.error("Evidence may not be written inside candidate checkout")
    os.umask(0o077)
    out.mkdir(mode=0o700)
    state = {"assessment_complete": False, "preservation_complete": False,
             "copies": [], "commands": [], "copied_bytes": 0,
             "inventory_before": {}, "inventory_after": {},
             "limits": {"max_entries": args.max_entries, "max_copy_bytes": args.max_copy_bytes},
             "acceptance_claim": False, "repair_performed": False,
             "journal_directory": str(out),
             "stability_limit": "Before/after observations are not an atomic snapshot or proof of no writers."}
    save(out / "started.json", {"started_utc": utc(), "argv": sys.argv,
                               "assessment_complete": False, "caller_must_establish_fresh_completion_and_idle_inputs": True})
    try:
        assess(args, out, state)
    except Exception:
        state["exception"] = traceback.format_exc()
    finally:
        state["finished_utc"] = utc()
        save(out / "assessment.json", state)
    print(json.dumps({"assessment_complete": state["assessment_complete"],
                      "evidence": str(out), "acceptance_claim": False}), flush=True)
    return 0 if state["assessment_complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

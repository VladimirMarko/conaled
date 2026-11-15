#!/usr/bin/env python3
"""Record statement-inspection inputs without building or changing project files.

This supplements actual recorded compiler runs. It does not certify an audit,
replace Lake's integrity guard, or establish that a prepared program ran.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True


def fingerprint(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def git(path, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(path), *args], text=True
    ).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--program", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compare", type=Path)
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    program = args.program.resolve(strict=True)
    control = Path(__file__).resolve().parents[1]
    base = control.parent
    assert not args.output.exists(), "Never overwrite an observation"
    assert git(project, "rev-parse", "HEAD") == args.candidate
    assert not git(project, "status", "--porcelain=v1", "--untracked-files=all")
    reference = json.loads((control / "provenance/chapter02-standards-source-preparation-20261104/foundation110-potential-type-reuse-0a7ef078.json").read_text())
    configs = {}
    for entry in reference["all_configuration_inputs"]:
        value = fingerprint(project / entry["path"])
        assert value["sha256"] == entry["sha256"], entry["path"]
        configs[entry["path"]] = value
    packages = json.loads((project / "lake-manifest.json").read_text())
    dependencies = {}
    for package in packages["packages"]:
        path = project / packages["packagesDir"] / package["name"]
        head = git(path, "rev-parse", "HEAD")
        status = git(path, "status", "--porcelain=v1", "--untracked-files=all")
        assert head == package["rev"] and not status, package["name"]
        dependencies[package["name"]] = {"head": head, "status": status, "path": str(path.resolve())}
    runtime = {}
    for entry in reference["historically_verified_runtime_components"]:
        path = base / entry["path"]
        value = fingerprint(path)
        assert value["sha256"] == entry["expected_sha256"], str(path)
        runtime[entry["path"]] = value
    sys.path.insert(0, str(project / "scripts"))
    spec = importlib.util.spec_from_file_location("project_source_reader", project / "scripts/check.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    imports = re.compile(r"^(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)
    def imported(text):
        return [name for match in imports.finditer(module.executable_source(text)) for name in match.group(1).split()]
    roots = imported(program.read_text())
    pending = list(roots)
    sources, outputs, external = {}, {}, set()
    while pending:
        name = pending.pop()
        relative = name.replace(".", "/") + ".lean"
        path = project / relative
        if not path.is_file():
            external.add(name)
            continue
        if relative in sources:
            continue
        value = fingerprint(path)
        value["git_blob"] = git(project, "rev-parse", args.candidate + ":" + relative)
        sources[relative] = value
        stem = project / ".lake/build/lib/lean" / name.replace(".", "/")
        assert stem.with_suffix(".olean").is_file(), "Required built module missing: " + name
        for suffix in (".olean", ".olean.hash", ".olean.private", ".olean.server", ".trace"):
            output = Path(str(stem) + suffix)
            if output.is_file():
                outputs[str(output.relative_to(project))] = fingerprint(output)
        pending.extend(imported(path.read_text()))
    checks = re.findall(r"^#check\s+@(\S+)\s*$", program.read_text(), re.MULTILINE)
    assert len(checks) == len(set(checks)) > 0
    identity = {"candidate": args.candidate, "clean": True, "project": str(project),
                "program": {"path": str(program), **fingerprint(program), "names": checks},
                "configuration": configs, "dependencies": dependencies, "runtime": runtime,
                "roots": roots, "local_sources": sources, "local_compiler_objects_and_traces": outputs,
                "direct_external_imports_of_local_closure": sorted(external)}
    receipt = {"observed_utc": datetime.now(timezone.utc).isoformat(), "identity": identity,
               "boundary": "Read-only input observation; actual execution, loaded-object qualification, complete output review, and candidate acceptance remain separate evidence."}
    if args.compare:
        before = json.loads(args.compare.read_text())
        receipt["compared_to"] = {"path": str(args.compare.resolve()), **fingerprint(args.compare)}
        receipt["unchanged"] = before["identity"] == identity
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "candidate": args.candidate,
                      "names": len(checks), "local_sources": len(sources),
                      "object_and_trace_files": len(outputs), "unchanged": receipt.get("unchanged")}))
    if args.compare and not receipt["unchanged"]:
        raise SystemExit("Statement inputs changed; preserve and investigate the observations.")


if __name__ == "__main__":
    main()

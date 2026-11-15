#!/usr/bin/env python3
"""Compare two audits on one stable, already-compiled project environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def inputs():
    """Identify project import artifacts and the inventory/configuration boundary.

    Dependency-cache stability remains the caller's responsibility. This is
    benchmark input comparison, not artifact provenance or candidate acceptance.
    """
    artifacts = ROOT / ".lake/build/lib/lean"
    if not (artifacts / "SquareApplications.olean").is_file():
        raise RuntimeError("Build the project first; the benchmark never compiles its imports")
    files = sorted(path for path in artifacts.rglob("*.olean*") if path.is_file())
    identity = hashlib.sha256()
    for path in files:
        identity.update(json.dumps([str(path.relative_to(ROOT)), digest(path)]).encode())
    inventory = subprocess.check_output(
        ["python3", "scripts/project_sources.py"], cwd=ROOT)
    return {
        "project_artifact_count": len(files),
        "project_artifacts_sha256": identity.hexdigest(),
        "inventory_sha256": hashlib.sha256(inventory).hexdigest(),
        "inventory_modules": json.loads(inventory),
        "configuration": {name: digest(ROOT / name) for name in
                          ("lean-toolchain", "lakefile.toml", "lake-manifest.json",
                           "flake.nix", "flake.lock", "scripts/project_sources.py",
                           "scripts/benchmark-proof-audit.py")},
    }


def semantic_report(output):
    return [line for line in output.splitlines() if
            line.startswith(("Proof audit:", "Excluded from logical roots:",
                             "Transitive axiom union:", "Proof audit PASSED:")) or
            re.fullmatch(r"  \S+: \d+ logical declarations; \d+ theorem declarations; \d+ unsafe runtime declarations", line)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True, help="saved baseline ProofAudit.lean")
    parser.add_argument("--candidate", type=Path, default=ROOT / "ProofAudit.lean")
    parser.add_argument("--allow-partial", action="store_true",
                        help="explicitly measure an incomplete cached import closure; report missing modules")
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True, help="JSON report; raw logs are retained alongside it")
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    if args.output.exists():
        parser.error("--output already exists; choose a new report path")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    logs = Path(tempfile.mkdtemp(prefix=args.output.stem + "-logs-", dir=args.output.parent)).resolve()
    before = inputs()
    report = {
        "status": "incomplete", "inputs": before,
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "affinity": sorted(os.sched_getaffinity(0)), "runs": [], "logs": str(logs),
        "scope": "Existing project import artifacts; dependency caches must remain stable. Not candidate acceptance.",
    }
    reference = None
    try:
        with tempfile.TemporaryDirectory(prefix="conaled-audit-benchmark-") as directory:
            directory = Path(directory)
            sources = {}
            for label, path in (("baseline", args.baseline), ("candidate", args.candidate)):
                target = directory / label / "ProofAudit.lean"
                target.parent.mkdir()
                source = path.read_bytes()
                target.write_bytes(source)
                report[label + "_sha256"] = hashlib.sha256(source).hexdigest()
                sources[label] = target
            # Separate import-only process, not a subtraction claiming exact
            # attribution of startup/import cost in another execution.
            imports = directory / "Imports.lean"
            imports.write_text("import SquareApplications\nimport Lean\n"
                               "import Lean.Util.CollectAxioms\nimport Lean.DeclarationRange\n")
            sources["imports"] = imports
            for repetition in range(args.repetitions):
                order = ("baseline", "candidate") if repetition % 2 == 0 else ("candidate", "baseline")
                for label in ("imports", *order):
                    source = sources[label]
                    started = time.perf_counter()
                    result = subprocess.run(["lake", "env", "lean", "-R", str(source.parent), str(source)],
                                            cwd=ROOT, capture_output=True, text=True)
                    elapsed = time.perf_counter() - started
                    output = result.stdout + result.stderr
                    log = logs / f"{repetition + 1}-{label}.log"
                    log.write_text(output)
                    timings = re.findall(r"Proof audit timings \(ms\): (.*)", output)
                    phases = ({key: int(value) for key, value in re.findall(r"(\w+)=(\d+)", timings[-1])}
                              if timings else None)
                    report["runs"].append({"repetition": repetition + 1, "kind": label,
                                           "seconds": elapsed, "exit": result.returncode,
                                           "phases_ms": phases, "log": str(log)})
                    print(f"{repetition + 1} {label}: {elapsed:.3f}s (exit {result.returncode})", flush=True)
                    if result.returncode:
                        raise RuntimeError(f"{label} failed; see {log}")
                    if label != "imports":
                        observed = semantic_report(output)
                        if len(observed) < 5 or not any(line.startswith("Proof audit PASSED:") for line in observed):
                            raise RuntimeError(f"Missing complete successful audit report: {log}")
                        if reference is None:
                            inventoried = set(before["inventory_modules"])
                            audited = {match.group(1) for line in observed
                                       if (match := re.match(r"  (\S+): \d+ logical declarations;", line))}
                            missing, unexpected = sorted(inventoried - audited), sorted(audited - inventoried)
                            report["coverage"] = {"inventoried": len(inventoried), "audited": len(audited),
                                                  "missing": missing, "unexpected": unexpected,
                                                  "complete": not missing and not unexpected}
                            print(f"Coverage: {len(audited)}/{len(inventoried)} inventoried modules"
                                  + (" (PARTIAL measurement)" if missing else ""), flush=True)
                            if unexpected or (missing and not args.allow_partial):
                                raise RuntimeError("Audit closure differs from inventory; rebuild the project, or "
                                                   "use --allow-partial for an explicitly partial measurement")
                            reference = observed
                        elif observed != reference:
                            raise RuntimeError(f"Audit reports differ: {log}")
            after = inputs()
            report["inputs_after"] = after
            if before != after:
                raise RuntimeError("Benchmark inputs changed during comparison")
            report["semantic_report"] = reference
            report["status"] = "passed"
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()

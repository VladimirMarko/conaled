#!/usr/bin/env python3
"""Explore, persist and reuse bounded choice evidence in a quiet execution slot.

The target is Lean's --run evaluator. These empirical durations are distinct
from circuit depth and declared primitive tariffs. This script does not build.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import platform
from pathlib import Path
import subprocess
import time

from choice_driver_client import ROOT, Session


def source_identity():
    paths = subprocess.check_output([
        "git", "ls-files", "--cached", "--others", "--exclude-standard", "--",
        "*.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "flake.lock",
        "scripts/benchmark-choice.py", "scripts/choice_driver_client.py",
    ], cwd=ROOT, text=True).splitlines()
    digest = hashlib.sha256()
    for name in sorted(set(paths)):
        digest.update(name.encode() + b"\0")
        digest.update((ROOT / name).read_bytes())
    return digest.hexdigest()


def checked(session, request):
    started = time.perf_counter_ns()
    response = session.request(request)
    wall = time.perf_counter_ns() - started
    if response["status"] != "ok":
        raise RuntimeError((request, response))
    return {"request": request, "response": response, "requestWallNs": wall}


def execute(output, repetitions):
    output.mkdir(parents=True, exist_ok=True)
    identity = source_identity()
    host = platform.uname()._asdict()
    cpuinfo = Path("/proc/cpuinfo").read_text() if Path("/proc/cpuinfo").exists() else "unavailable"
    target = f"{host['node']}:{host['system']}:{host['release']}:{host['machine']}"
    report = {"sourceHash": identity,
              "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "timeUTC": datetime.now(timezone.utc).isoformat(), "host": host,
              "cpuinfo": cpuinfo, "affinity": sorted(os.sched_getaffinity(0)),
              "target": "Lean --run evaluator; sequential CPU execution", "workloads": []}
    workloads = [
        {"client": "scan", "variant": "nested"},
        {"client": "scan", "variant": "powers", "power": 6},
        {"client": "scan", "variant": "powers", "power": 8},
    ]
    workloads += [{"client": "tree", "variant": variant, "nodes": nodes, "queries": queries}
                  for variant, nodes, queries in [("star", 17, 1), ("star", 17, 1024),
                                                  ("chain", 65, 32), ("branching", 65, 1024)]]
    startup = time.perf_counter_ns()
    with Session(identity) as session:
        checked(session, {"client": "scan"})
        report["startupAndHandshakeNs"] = time.perf_counter_ns() - startup
        for index, workload in enumerate(workloads):
            base = dict(workload, repetitions=repetitions, target=target)
            training_started = time.perf_counter_ns()
            initial = checked(session, base)
            candidates = initial["response"]["context"]["catalog"]
            if not candidates:
                raise RuntimeError("benchmark workload unexpectedly has no admitted candidate")
            warmups = [checked(session, dict(base, mode="explore", candidate=c)) for c in candidates]
            epoch = None
            training = []
            updates = []
            for repetition in range(repetitions):
                # Rotate order to expose every candidate, rather than observe only a chosen path.
                order = candidates[repetition % len(candidates):] + candidates[:repetition % len(candidates)]
                for candidate in order:
                    sample = checked(session, dict(base, mode="sample", candidate=candidate, repetition=repetition))
                    training.append(sample)
                    updated = checked(session, dict(base, mode="record", evidence=epoch,
                                                    sample=sample["response"]["sample"]))
                    updates.append(updated)
                    epoch = updated["response"]["epoch"]
            evidence_file = output / f"epoch-{index}.json"
            persisted = time.perf_counter_ns()
            evidence_file.write_text(json.dumps(epoch, indent=2) + "\n")
            loaded = json.loads(evidence_file.read_text())
            persistence_ns = time.perf_counter_ns() - persisted
            training_total_ns = time.perf_counter_ns() - training_started
            trained = checked(session, dict(base, evidence=loaded))
            if not trained["response"]["evidenceUsed"]:
                raise RuntimeError("complete saved epoch was not accepted")
            comparisons = []
            for repetition in range(repetitions):
                policies = [("fixed", None), ("trained", loaded)]
                if repetition % 2:
                    policies.reverse()
                for policy, evidence in policies:
                    selected = checked(session, dict(base, evidence=evidence))["response"]["chosen"]
                    outcome = checked(session, dict(base, mode="sample", candidate=selected,
                                                    repetition=repetition, evidence=evidence))
                    if outcome["response"]["executed"] != outcome["response"]["chosen"]:
                        raise RuntimeError("comparison bypassed selected realization")
                    comparisons.append({"policy": policy, **outcome})
            totals = {policy: sum(row["response"]["endToEndNs"] for row in comparisons if row["policy"] == policy)
                      for policy in ("fixed", "trained")}
            wall_totals = {policy: sum(row["requestWallNs"] for row in comparisons if row["policy"] == policy)
                           for policy in ("fixed", "trained")}
            report["workloads"].append({
                "request": base, "initial": initial, "warmups": warmups, "training": training,
                "updates": updates, "trainingTotalWallNs": training_total_ns,
                "epochFile": evidence_file.name, "evidenceSerializationWriteReloadNs": persistence_ns,
                "trainedSelection": trained, "comparisons": comparisons,
                "comparisonEndToEndTotalsNs": totals, "comparisonRequestWallTotalsNs": wall_totals,
                "trainedMinusFixedNs": totals["trained"] - totals["fixed"],
                "trainingRequestWallNs": sum(row["requestWallNs"] for row in training),
            })
    if source_identity() != identity:
        raise RuntimeError("source changed during measurement")
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    for result in report["workloads"]:
        print(json.dumps({"workload": result["request"],
                          "fixed": result["initial"]["response"]["chosen"],
                          "trained": result["trainedSelection"]["response"]["chosen"],
                          "trainedMinusFixedNs": result["trainedMinusFixedNs"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--repetitions", type=int, default=5, choices=range(1, 21))
    args = parser.parse_args()
    execute(args.output, args.repetitions)


if __name__ == "__main__":
    main()

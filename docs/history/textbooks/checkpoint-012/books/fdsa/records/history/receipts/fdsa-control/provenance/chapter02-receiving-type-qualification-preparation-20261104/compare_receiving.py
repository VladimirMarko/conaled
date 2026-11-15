#!/usr/bin/env python3
"""Compare saved C2 input observations. Never inspect a project or execute Lean.

Prepared, unexecuted support for the two existing review axes. This script grants
zero type or acceptance credit and does not choose a remainder to execute.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path


SUFFIXES = (".olean", ".olean.hash", ".olean.private", ".olean.server", ".trace")


def fingerprint(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def difference(left, right):
    return {key: {"producer_present": key in left, "receiver_present": key in right,
                  "producer": left.get(key), "receiver": right.get(key)}
            for key in sorted(set(left) | set(right))
            if key not in left or key not in right or left[key] != right[key]}


def artifact_projection(identity, paths):
    permitted = {".lake/build/lib/lean/" + p.removesuffix(".lean") + suffix
                 for p in paths for suffix in SUFFIXES}
    return {p: value for p, value in identity["local_compiler_objects_and_traces"].items()
            if p in permitted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control", type=Path, required=True)
    parser.add_argument("--full-result", type=Path, required=True)
    parser.add_argument("--receiver-pre", type=Path, required=True)
    parser.add_argument("--receiver-post", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    control = args.control.resolve(strict=True)
    package = Path(__file__).resolve().parent
    if not package.is_relative_to(control / "provenance"):
        raise SystemExit("The prepared package must remain inside this control provenance.")
    read_files = {}

    def read(path, expected=None, decode=True):
        path = Path(path)
        path = (path if path.is_absolute() else control / path).resolve(strict=True)
        if not path.is_relative_to(control):
            raise ValueError("Refusing to read anything outside saved control evidence: " + str(path))
        data = path.read_bytes()
        actual = fingerprint(data)
        if expected is not None and actual != {k: expected[k] for k in ("bytes", "sha256")}:
            raise ValueError("Bound evidence changed: " + str(path))
        read_files[str(path.relative_to(control))] = actual
        return json.loads(data) if decode else data

    schedule = read(package / "schedule.json")
    bound = read(package / "bound-inputs.json")
    for entry in bound["files"]:
        read(entry["path"], entry, decode=False)
    inventory = read(schedule["source_inventory"])
    old_closures = read(schedule["historical_closure_ledger"])
    old_qualification = read(schedule["historical_qualification_ledger"])
    carrier = schedule["observation_carrier"]
    read(carrier["path"], carrier, decode=False)
    full = read(args.full_result)
    receiver = schedule["receiver"]
    if (full.get("candidate") != receiver or full.get("exit_code") != 0
            or full.get("final_head") != receiver or full.get("final_status") != ""
            or full.get("progress_bookkeeping_errors", [])):
        raise ValueError("A secured successful exact-Q outer full result is required first.")
    # The full result's native closure, complete audit, lineage and final approvals
    # remain separately reviewed evidence; this check does not certify those gates.
    pre_document = read(args.receiver_pre)
    post_document = read(args.receiver_post) if args.receiver_post else None
    pre = pre_document["identity"]
    post = post_document["identity"] if post_document else None
    expected_sources = schedule["expected_Q_static_source_catalog"]
    expected_external = inventory["complete_external_import_union"]
    source_by_id = {row["id"]: row for row in inventory["source_ids"]}
    target_closures = {
        root: {"local_source_blobs": {source_by_id[i]["path"]: source_by_id[i]["Z_blob"]
                                     for i in value["local_source_ids"]},
               "direct_external_imports": value["direct_external_imports"]}
        for root, value in inventory["defining_root_closures"].items()}

    def receiver_issues(identity):
        expected = {"candidate": receiver, "clean": True, "project": schedule["project"],
                    "roots": carrier["roots"],
                    "direct_external_imports_of_local_closure": expected_external}
        issues = difference(expected, {k: identity.get(k) for k in expected})
        program = {"path": str(control / carrier["path"]), "bytes": carrier["bytes"],
                   "sha256": carrier["sha256"], "names": carrier["collected_names"]}
        if identity.get("program") != program:
            issues["observation_carrier"] = {"expected": program, "actual": identity.get("program")}
        changed = difference(expected_sources, identity.get("local_sources", {}))
        if changed:
            issues["expected_Q_sources"] = changed
        objects = identity.get("local_compiler_objects_and_traces", {})
        missing_objects = [p for p in expected_sources if
                           objects.get(".lake/build/lib/lean/" + p.removesuffix(".lean") + ".olean", {}).get("bytes", 0) <= 0]
        if missing_objects:
            issues["missing_or_empty_required_olean"] = missing_objects
        extra_objects = sorted(set(objects) - set(artifact_projection(identity, expected_sources)))
        if extra_objects:
            issues["unexpected_artifact_keys_outside_the97_source_projection"] = extra_objects
        counts = schedule["expected_counts"]
        for field, key in (("configuration", "configs"), ("dependencies", "dependency_records"),
                           ("runtime", "runtime_components")):
            if len(identity.get(field, {})) != counts[key]:
                issues[field + "_count"] = {"expected": counts[key],
                                            "actual": len(identity.get(field, {}))}
        return issues

    receiver_checks = {"pre": receiver_issues(pre),
                       "post": receiver_issues(post) if post is not None else None,
                       "pre_post_identity_equal": pre == post if post is not None else None,
                       "identity_differences": difference(pre, post) if post is not None else None}
    receiver_valid = not receiver_checks["pre"] and (post is None or not receiver_checks["post"])
    receiver_stable = post is not None and pre == post and receiver_valid
    identities, producer_checks, global_comparisons = {}, {}, {}
    for key, producer in schedule["recent_producers"].items():
        left = read(producer["pre_inputs"])["identity"]
        right = read(producer["post_inputs"])["identity"]
        identities[key] = left
        profile = schedule["program_profiles"][key]
        expected_names = [inventory["public_rows"][i - 1][0]
                          for i in producer["original_program_name_ids"]]
        producer_checks[key] = {
            "pre_post_equal": left == right,
            "exact_candidate_clean": left.get("candidate") == producer["candidate"] and left.get("clean") is True,
            "exact_program": left["program"]["sha256"] == profile["program"]["sha256"]
                             and left["program"]["bytes"] == profile["program"]["bytes"]
                             and left["program"]["names"] == expected_names}
        global_comparisons[key] = {
            "project": {} if left["project"] == pre["project"] else
                       {"producer": left["project"], "receiver": pre["project"]},
            **{field: difference(left[field], pre[field])
               for field in ("configuration", "dependencies", "runtime")}}

    root_comparisons = {}

    def compare_root(key, root, producer_closure, anchor_only=False):
        tag = ("anchor:" if anchor_only else "printed:") + key + ":" + root
        if tag in root_comparisons:
            return tag
        left = identities[key]
        target = target_closures[root]
        paths = set(producer_closure["local_source_blobs"]) | set(target["local_source_blobs"])
        left_sources = {p: left["local_sources"][p] for p in paths if p in left["local_sources"]}
        right_sources = {p: pre["local_sources"][p] for p in paths if p in pre["local_sources"]}
        source_difference = difference(left_sources, right_sources)
        artifact_difference = difference(artifact_projection(left, paths), artifact_projection(pre, paths))
        static_difference = difference(producer_closure["local_source_blobs"], target["local_source_blobs"])
        external_equal = producer_closure["direct_external_imports"] == target["direct_external_imports"]
        missing = {"producer": sorted(paths - set(left_sources)), "receiver": sorted(paths - set(right_sources))}
        all_match = (receiver_valid and all(producer_checks[key].values())
                     and not any(global_comparisons[key].values())
                     and not source_difference and not artifact_difference and not static_difference
                     and external_equal and not any(missing.values()))
        root_comparisons[tag] = {
            "producer": key, "root": root, "observation_anchor_only": anchor_only,
            "source_paths": sorted(paths), "global_comparison": key,
            "static_closure_blob_differences": static_difference,
            "source_input_differences": source_difference,
            "all_supported_artifact_key_value_differences": artifact_difference,
            "missing_source_inputs": missing,
            "producer_direct_external_imports": producer_closure["direct_external_imports"],
            "receiver_direct_external_imports": target["direct_external_imports"],
            "direct_external_imports_equal": external_equal,
            "producer_artifact_keys": sorted(artifact_projection(left, paths)),
            "receiver_artifact_keys": sorted(artifact_projection(pre, paths)),
            "preliminary_exact_relevant_input_match": all_match,
            "stable_exact_relevant_input_match": all_match and receiver_stable,
            "type_credit": 0,
            "boundary": "Mechanical projection only; actual producer output/profile, guarded lineage and both axes determine any receiving disposition."}
        return tag

    recent_by_name = {}
    for key, producer in schedule["recent_producers"].items():
        for position, name_id in enumerate(producer["original_program_name_ids"], 1):
            row = inventory["public_rows"][name_id - 1]
            root = source_by_id[row[1]]["path"]
            comparison = compare_root(key, root, producer["root_closures"][root])
            recent_by_name.setdefault(name_id, []).append({"producer": key, "check_position": position,
                                                          "comparison": comparison})
    historical_root_comparisons, historical_by_name, historical_globals = {}, {}, {}
    old_ledger_by_run = {r["run"]: r for r in old_closures["runs"]}
    old_source_configs = {p: {k: v[k] for k in ("bytes", "sha256")}
                          for p, v in old_qualification["configuration"].items()}
    old_source_pins = {v["name"]: v["rev"] for v in old_qualification["pinned_dependencies"]}
    for producer in schedule["historical_producers"]:
        key = producer["run"]
        roots = {r["root"]: r for r in old_ledger_by_run[key]["roots"]}
        qualified = set(producer["historical_qualified920_name_ids"])
        command = producer["actual_command"]
        old_project = command[command.index("--project") + 1]
        historical_globals[key] = {
            "actual_historical_command": command,
            "command_project": {"producer": old_project, "receiver": pre["project"],
                                "equal": old_project == pre["project"]},
            "source_configuration_differences": difference(old_source_configs, pre["configuration"]),
            "source_pin_to_receiving_actual_head_differences": difference(
                old_source_pins, {n: v["head"] for n, v in pre["dependencies"].items()}),
            "actual_historical_dependency_paths_and_runtime_hash_pair": None,
            "boundary": "Source configuration/pin qualification is the retained historical ledger, not an invented producer runtime/dependency/object snapshot. Full older profile/build/terminal evidence remains bound."}
        for position, name_id in enumerate(producer["original_program_name_ids"], 1):
            row = inventory["public_rows"][name_id - 1]
            root = source_by_id[row[1]]["path"]
            old = roots[root]
            tag = key + ":" + root
            if tag not in historical_root_comparisons:
                current = {p: v["git_blob"] for p, v in pre["local_sources"].items()
                           if p in target_closures[root]["local_source_blobs"]}
                historical_root_comparisons[tag] = {
                    "root": root, "producer": key,
                    "source_blob_differences": difference(old["historical_local_closure"], current),
                    "producer_external_imports": old["historical_external_imports"],
                    "receiver_external_imports": target_closures[root]["direct_external_imports"],
                    "direct_external_imports_equal": old["historical_external_imports"] == target_closures[root]["direct_external_imports"],
                    "actual_terminal_boundary": producer["terminal_boundary"],
                    "producer_paired_snapshots": None,
                    "boundary": "Original source/profile/build/terminal and semantic evidence retained; no invented paired object/runtime observations."}
            anchor = None
            if name_id in qualified and root in schedule["Z_observation_anchor_closures"]:
                anchor = compare_root("Z815", root, schedule["Z_observation_anchor_closures"][root], anchor_only=True)
            historical_by_name.setdefault(name_id, []).append({
                "producer": key, "check_position": position, "comparison": tag,
                "historically_qualified_at_Z": name_id in qualified,
                "Z_saved_observation_anchor_comparison": anchor,
                "anchor_boundary": "An input anchor is not a claim that this name was printed in Z815."})
    accepted = {i for group in inventory["accepted_R28"] for i in group["name_ids"]}
    names = [{"id": i, "name": row[0], "defining_root": source_by_id[row[1]]["path"],
              "historical_Z_disposition": row[3], "retained_accepted_R": i in accepted,
              "recent_actual_producers": recent_by_name.get(i, []),
              "older_actual_producers": historical_by_name.get(i, []),
              "receiving_credit": 0}
             for i, row in enumerate(inventory["public_rows"], 1)]
    report = {"schema": "fdsa.c2.saved-receiving-comparison.v1",
              "recorded_utc": datetime.now(timezone.utc).isoformat(), "receiver": receiver,
              "status": "Mechanical evidence for both axes; no final eligibility, type credit or selected rerun",
              "receiver_observation_checks": receiver_checks, "producer_checks": producer_checks,
              "global_comparisons": global_comparisons, "root_comparisons": root_comparisons,
              "historical_global_context": historical_globals,
              "historical_root_comparisons": historical_root_comparisons, "names": names,
              "historical_program_profiles": {p["run"]: schedule["program_profiles"][p["run"]]
                                              for p in schedule["historical_producers"]},
              "counts": {"complete_public_union": len(names), "recent_producers": len(identities),
                         "older_producers": len(schedule["historical_producers"]),
                         "historical_checks": 941, "historical_prints": 3,
                         "type_credit": 0}, "input_files": read_files,
              "missing_boundaries": schedule["special_boundaries"],
              "actual_targeted_program_selected": None,
              "qualification_boundary": "No path/trace normalization. All captured supported keys compared. External artifacts are not hashed by the observation helper; qualified full-build/dependency lineage and complete independent assessments remain necessary. The observation carrier is never a type producer."}
    output = args.output if args.output.is_absolute() else control / args.output
    output_parent = output.parent.resolve(strict=True)
    if not output_parent.is_relative_to(control / "provenance"):
        raise ValueError("Write only a fresh comparison record within control provenance.")
    with (output_parent / output.name).open("x", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"output": str(output), "names": len(names),
                      "receiver_stable": receiver_stable, "credit": 0,
                      "recent_root_comparisons": len(root_comparisons),
                      "historical_root_comparisons": len(historical_root_comparisons)}))


if __name__ == "__main__":
    main()

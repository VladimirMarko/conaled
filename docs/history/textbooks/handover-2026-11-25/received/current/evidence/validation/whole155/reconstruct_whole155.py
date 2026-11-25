#!/usr/bin/env python3
"""Reconstruct exact whole155 receipts; never execute their commands.

A retired raw log is not reconstructed or claimed verified from its excerpts.
"""
import argparse
import hashlib
import json
import stat
from pathlib import Path


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        assert key not in value, ("Duplicate JSON key", key)
        value[key] = item
    return value


def load(raw):
    return json.loads(raw, object_pairs_hook=unique_object)


def serialize(value):
    return (json.dumps(value, indent=2, ensure_ascii=True, sort_keys=False) + "\n").encode()


def verify(raw, descriptor):
    assert len(raw) == descriptor["bytes"]
    assert hashlib.sha256(raw).hexdigest() == descriptor["sha256"]


def project(base, delta, allow_null_values=False):
    omitted = delta["omitted_keys"]
    assert len(omitted) == len(set(omitted)) and set(omitted) <= set(base)
    excluded = set(omitted)
    value = {key: item for key, item in base.items() if key not in excluded}
    overrides = delta.get("descriptor_overrides", {})
    assert set(overrides) <= set(value)
    assert allow_null_values or all(x is not None for x in overrides.values())
    value.update(overrides)
    added = delta.get("added_bindings", {})
    assert not set(added) & set(value)
    assert allow_null_values or all(x is not None for x in added.values())
    value.update(added)
    assert delta["key_order"] == "lexicographic"
    value = dict(sorted(value.items()))
    assert len(value) == delta["binding_count"]
    assert allow_null_values or all(x is not None for x in value.values())
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capsule", type=Path)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--path-map", type=Path)
    parser.add_argument("--output", type=Path, help="Optional fresh directory for original receipt bytes")
    args = parser.parse_args()
    capsule = load(args.capsule.read_bytes())
    assert capsule["schema"] == 1 and capsule["run_id"] == "whole155"
    rows = {row["member"]: row for row in capsule["literal_files"]}
    assert len(rows) == len(capsule["literal_files"])
    routing = load(args.path_map.read_bytes()) if args.path_map else {}
    assert set(routing) <= set(rows)
    literals = {}
    for member, row in rows.items():
        path = args.root / routing.get(member, member)
        assert path.is_file() and not path.is_symlink(), path
        raw = path.read_bytes()
        verify(raw, row["descriptor"])
        assert stat.S_IMODE(path.stat().st_mode) == int(row["descriptor"]["mode"], 8) & 0o7777
        literals[member] = raw
    anchor = load(literals[capsule["anchor_member"]])
    bindings = anchor["source_bindings"]
    assert len(bindings) == 4068 and all(x is not None for x in bindings.values())
    before = project(bindings, load(literals[capsule["before_delta_member"]]))
    assert len(before) == 16842
    maps = {"whole_before": before}
    if "after_delta_member" in capsule:
        maps["whole_after"] = project(before, load(literals[capsule["after_delta_member"]]), allow_null_values=True)
    elif capsule["actual_outer_terminal_observed"]:
        maps["whole_after"] = before
    reconstructed, parsed = {}, {}
    for row in capsule["records"]:
        assert row["id"] not in reconstructed
        fields, refs, order = row["nonmap_fields"], row["map_fields"], row["original_top_level_key_order"]
        assert set(fields).isdisjoint(refs)
        assert len(order) == len(set(order)) and set(order) == set(fields) | set(refs)
        value = {key: maps[refs[key]] if key in refs else fields[key] for key in order}
        raw = serialize(value)
        verify(raw, row["original_descriptor"])
        reconstructed[row["id"]], parsed[row["id"]] = raw, value
    start = parsed["whole155.start"]
    assert start["name"] == "whole155" and start["source_bindings"] == before
    terminal = capsule["actual_outer_terminal_observed"]
    if "cutoff_status_member" in capsule:
        status = load(literals[capsule["cutoff_status_member"]])
        assert status["run_id"] == "whole155"
        assert status["cutoff_utc"] == capsule["cutoff_utc"]
        assert status["actual_outer_terminal_observed"] == terminal
        assert status["actual_outer_exit_code"] == capsule["actual_outer_exit_code"]
        assert status["source_bindings_before_count"] == len(before)
        assert status["source_bindings_before_nonnull"] is True
        command = start["command"]
        assert command[command.index("--candidate") + 1] == status["candidate"]
        assert capsule["raw_log"]["kind"] == status["log_kind"]
        for key in ("bytes", "sha256", "mode"):
            assert capsule["raw_log"]["descriptor"][key] == status["frozen_log"][key]
        diagnostics = b"".join(literals[e["member"]] for e in capsule["diagnostic_excerpts"])
        assert all(diagnostics.count((line + "\n").encode()) == 1 for line in status["failed_job_lines"])
        assert diagnostics.count(b"error: Lean exited with code 137\n") == status["reported_137_lines"]
    if terminal:
        assert set(parsed) == {"whole155.start", "whole155.result"}
        result = parsed["whole155.result"]
        child_raw = literals[capsule["child_member"]]
        child = load(child_raw)
        assert isinstance(capsule["actual_outer_exit_code"], int)
        assert result["exit_code"] == child["exit_code"] == capsule["actual_outer_exit_code"]
        for key in ("name", "command", "project", "started_utc", "resource_or_time_limits_added"):
            assert start[key] == result[key] == child[key]
        for key in ("finished_utc", "elapsed_seconds"):
            assert result[key] == child[key]
        assert child["start_record"]["path"] == capsule["original_start_path"]
        verify(reconstructed["whole155.start"], child["start_record"])
        assert result["child_exit_receipt"]["path"] == capsule["original_child_path"]
        verify(child_raw, result["child_exit_receipt"])
        assert result["log"] == child["log"] == capsule["original_log_path"]
        assert child["post_run_hashing_completed"] is False
        assert result["source_bindings"] == before
        assert result["sources_unchanged"] == (before == result["source_bindings_after"])
        assert result["source_bindings_after"] == maps["whole_after"]
        for key in ("bytes", "sha256", "mode"):
            assert result["log_descriptor"][key] == capsule["raw_log"]["descriptor"][key]
    else:
        assert set(parsed) == {"whole155.start"}
        assert capsule["actual_outer_exit_code"] is None
        assert "child_member" not in capsule and "after_delta_member" not in capsule
    full_log_verified = False
    if "raw_log" in capsule:
        raw_log = capsule["raw_log"]
        if "selected_member" in raw_log:
            verify(literals[raw_log["selected_member"]], raw_log["descriptor"])
            full_log_verified = True
        else:
            assert raw_log["full_body_reconstructible_here"] is False
        for excerpt in capsule.get("diagnostic_excerpts", []):
            data = literals[excerpt["member"]]
            for segment in excerpt["segments"]:
                a, b = segment["selected_byte_range"]
                c, d = segment["source_byte_range"]
                assert 0 <= a <= b <= len(data) and 0 <= c <= d <= raw_log["descriptor"]["bytes"]
                assert b - a == d - c
                verify(data[a:b], segment["descriptor"])
                if full_log_verified:
                    assert data[a:b] == literals[raw_log["selected_member"]][c:d]
    if args.output:
        assert not args.output.exists(), "Output must be a fresh directory"
        args.output.mkdir(parents=True)
        for row in capsule["records"]:
            path = args.output / (row["id"] + ".json")
            path.write_bytes(reconstructed[row["id"]])
            path.chmod(int(row["original_descriptor"]["mode"], 8) & 0o7777)
    print(json.dumps({
        "run_id": "whole155", "original_receipts_verified": len(reconstructed),
        "original_serialized_bytes_exact": True, "shared_anchor_bindings": 4068,
        "whole_before_bindings": len(before), "actual_outer_terminal_observed": terminal,
        "actual_outer_exit_code": capsule["actual_outer_exit_code"],
        "literal_files_verified": len(literals), "full_raw_log_verified_from_selected_bytes": full_log_verified,
        "retired_log_excerpt_origin_rechecked_without_raw_body": False,
        "reconstructed_in_memory_only": not bool(args.output), "compiler_run": False,
    }, indent=2))


if __name__ == "__main__":
    main()

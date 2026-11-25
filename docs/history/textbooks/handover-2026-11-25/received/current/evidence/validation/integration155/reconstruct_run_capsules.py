#!/usr/bin/env python3
"""Verify/reconstruct exact completed-run receipts from one literal binding map.

No receipt command is executed. Without --output, reconstruction is in memory.
"""
import argparse
import hashlib
import json
from pathlib import Path
import stat


def digest(data):
    return hashlib.sha256(data).hexdigest()


def serialize(value):
    return (json.dumps(value, indent=2, ensure_ascii=True, sort_keys=False) + "\n").encode("utf-8")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, ("Duplicate JSON key", key)
        result[key] = value
    return result


def load_json(raw):
    return json.loads(raw, object_pairs_hook=unique_object)


def verify_descriptor(data, expected):
    assert len(data) == expected["bytes"]
    assert digest(data) == expected["sha256"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capsules", type=Path)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--path-map", type=Path)
    parser.add_argument("--output", type=Path, help="Optional fresh directory for original receipt bytes")
    args = parser.parse_args()
    capsules = load_json(args.capsules.read_bytes())
    mapping = load_json(args.path_map.read_bytes()) if args.path_map else {}
    literal_rows = {row["canonical_member"]: row for row in capsules["literal_files"]}
    assert isinstance(mapping, dict) and set(mapping) <= set(literal_rows)
    assert all(isinstance(value, str) and value for value in mapping.values())
    literal = {}
    for member, row in literal_rows.items():
        path = args.root / mapping.get(member, member)
        assert path.is_file() and not path.is_symlink(), path
        raw = path.read_bytes()
        verify_descriptor(raw, row["original_descriptor"])
        assert stat.S_IMODE(path.stat().st_mode) == int(row["original_descriptor"]["mode"], 8)
        literal[member] = raw
    anchor_member = capsules["anchor"]["canonical_member"]
    anchor_raw = literal[anchor_member]
    anchor = load_json(anchor_raw)
    assert serialize(anchor) == anchor_raw
    bindings = anchor[capsules["anchor"]["map_field"]]
    assert len(bindings) == capsules["anchor"]["binding_count"] == 4068
    assert all(value is not None for value in bindings.values())
    projections = {}
    for name, row in capsules["projections"].items():
        omitted = row["omitted_keys"]
        assert len(omitted) == len(set(omitted))
        assert set(omitted) <= set(bindings)
        excluded = set(omitted)
        projected = {key: value for key, value in bindings.items() if key not in excluded}
        overrides = row.get("descriptor_overrides", {})
        assert set(overrides) <= set(projected)
        assert all(value is not None for value in overrides.values())
        projected.update(overrides)
        added = row.get("added_bindings", {})
        assert not set(added) & set(projected) and all(v is not None for v in added.values())
        projected.update(added)
        projected = dict(sorted(projected.items()))
        assert row["key_order"] == "lexicographic"
        assert len(projected) == row["binding_count"]
        projections[name] = projected
    reconstructed = {capsules["anchor"]["literal_receipt_id"]: anchor_raw}
    summary = []
    for row in capsules["records"]:
        fields = row["nonmap_fields"]
        maps = row["map_fields"]
        order = row["original_top_level_key_order"]
        assert set(fields).isdisjoint(maps)
        assert len(order) == len(set(order)) and set(order) == set(fields) | set(maps)
        value = {}
        for key in order:
            value[key] = projections[maps[key]["projection"]] if key in maps else fields[key]
        if "source_bindings_after" in value:
            assert value["source_bindings"] == value["source_bindings_after"]
            assert value["sources_unchanged"] is True
        raw = serialize(value)
        verify_descriptor(raw, row["original_descriptor"])
        reconstructed[row["id"]] = raw
        summary.append({"id": row["id"], "bytes": len(raw), "sha256": digest(raw)})
    assert set(reconstructed) == {run[key] for run in capsules["runs"] for key in ("start_record", "result_record")}
    for run in capsules["runs"]:
        result = load_json(reconstructed[run["result_record"]])
        child = load_json(literal[run["child_member"]])
        assert result["exit_code"] == child["exit_code"] == run["actual_exit_code"]
        start = load_json(reconstructed[run["start_record"]])
        for key in ("name", "command", "project", "started_utc", "resource_or_time_limits_added"):
            assert start[key] == result[key] == child[key]
        for key in ("finished_utc", "elapsed_seconds"):
            assert result[key] == child[key]
        assert child["start_record"]["path"] == run["original_start_path"]
        verify_descriptor(reconstructed[run["start_record"]], child["start_record"])
        assert result["child_exit_receipt"]["path"] == run["original_child_path"]
        verify_descriptor(literal[run["child_member"]], result["child_exit_receipt"])
        assert result["log"] == child["log"] == run["original_log_path"]
        assert child["post_run_hashing_completed"] is False
        assert start["source_bindings"] == result["source_bindings"]
        assert len(result["source_bindings"]) == run["nonnull_before_after_bindings"]
        verify_descriptor(literal[run["log_member"]], result["log_descriptor"])
    if args.output:
        assert not args.output.exists(), "Output directory must be fresh"
        args.output.mkdir(parents=True)
        for name, raw in reconstructed.items():
            path = args.output / (name + ".json")
            with path.open("xb") as stream:
                stream.write(raw)
            path.chmod(0o644)
    print(json.dumps({
        "original_receipts_verified": len(reconstructed),
        "projected_receipts": len(capsules["records"]),
        "literal_files_verified": len(literal),
        "anchor_bindings": len(bindings),
        "original_serialized_bytes_exact": True,
        "reconstructed_in_memory_only": not bool(args.output),
        "compiler_run": False,
        "reconstructed": summary,
    }, indent=2))


if __name__ == "__main__":
    main()

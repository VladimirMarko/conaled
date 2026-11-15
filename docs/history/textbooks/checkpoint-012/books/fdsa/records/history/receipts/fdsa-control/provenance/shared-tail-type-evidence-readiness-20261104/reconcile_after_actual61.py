"""Mechanical qualification after the exact Tail full gate and actual61.

This script is preparation until executed with an explicit frozen receiver.
It grants no independent semantic verdict and never invokes a compiler.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
C = Path(__file__).resolve().parents[2]
W = C.parent / "conaled-ch01-review"
J = "932438a765340d69fa6402f6abd17def6ec28d13"
I = "312aafb4446b995ff5542041b4e2e074f776db1e"
F = "f17cc6b1a2bf44215b16202ed0fcee2b5c130761"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--candidate", required=True)
args = parser.parse_args()
L = args.candidate
assert re.fullmatch(r"[0-9a-f]{40}", L)


def read(relative):
    return json.loads((C / relative).read_text())


def identity(path):
    data = path.read_bytes()
    return {"path": str(path), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def git(*arguments):
    return subprocess.check_output(["git", "--no-optional-locks", "-C", str(W), *arguments])


def instant(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


assert git("rev-parse", "HEAD").decode().strip() == L
assert not git("status", "--porcelain=v1", "--untracked-files=all")
assert git("rev-parse", "work/fdsa-book").decode().strip() == J
full_dir = C / "provenance/shared-tail-full-attempt1-20261104"
types_dir = C / "provenance/shared-tail-complete-public-statements61-20261104-attempt1"
full = json.loads((full_dir / "result.json").read_text())
actual = json.loads((types_dir / "result.json").read_text())
for directory, result in ((full_dir, full), (types_dir, actual)):
    owned = json.loads((directory / "owned-terminal.json").read_text())
    assert owned["actual_exit"] == result["exit_code"] == 0
    assert owned["candidate"] == result["candidate"] == result["final_head"] == L
    assert not result["final_status"]
    assert identity(directory / "full.log")["sha256"] == result["log_sha256"]
    assert (directory / "closed-evidence-reconciliation.json").is_file()

observations = {}


def pair(label, directory, candidate, receiving=False):
    entries = []
    for phase in ("pre", "post"):
        path = C / "provenance" / directory / (phase + "-inputs.json")
        record = json.loads(path.read_text())
        assert record["identity"]["candidate"] == candidate
        assert record["identity"]["clean"]
        observations[label + "_" + phase] = {**identity(path), "observed_utc": record["observed_utc"]}
        entries.append(record)
    assert entries[0]["identity"] == entries[1]["identity"]
    if receiving:
        assert instant(full["completed_utc"]) < instant(entries[0]["observed_utc"]) < instant(actual["started_utc"])
        assert instant(actual["completed_utc"]) < instant(entries[1]["observed_utc"])
    return entries[0]["identity"]


l61 = pair("Tail61", "shared-tail61-input-observations-20261104-attempt1", L, True)
l53 = pair("TailJ53", "shared-tail-inherited53-input-observations-20261104-attempt1", L, True)
l314 = pair("TailI314", "shared-tail-inherited314-input-observations-20261104-attempt1", L, True)
l145 = pair("TailF145", "shared-tail-foundation110-input-observations-20261104-attempt1", L, True)
j53 = pair("J53", "shared-order53-input-observations-20261104-attempt1", J)
j314 = pair("J314", "shared-order-inherited314-input-observations-20261104-attempt1", J)
j145 = pair("J145", "shared-order-foundation110-input-observations-20261104-attempt1", J)
i314 = pair("I314", "shared-four314-input-observations-20261104-attempt1", I)
i145 = pair("I145", "shared-four-foundation110-receiving-observations-20261104-attempt1", I)
f145 = pair("F145", "foundation145-input-observations-20261104-attempt1", F)

fields = ("clean", "project", "program", "configuration", "dependencies", "runtime", "roots",
          "local_sources", "local_compiler_objects_and_traces", "direct_external_imports_of_local_closure")
assert {k: j53[k] for k in fields} == {k: l53[k] for k in fields}
assert {k: i314[k] for k in fields} == {k: j314[k] for k in fields} == {k: l314[k] for k in fields}
assert len(l61["local_sources"]) == 9
assert len(l61["local_compiler_objects_and_traces"]) == 27
assert len(l53["local_sources"]) == 6
assert len(l53["local_compiler_objects_and_traces"]) == 18
assert len(l314["local_sources"]) == 27
assert len(l314["local_compiler_objects_and_traces"]) == 81

old = read("provenance/shared-four-foundation110-receiving-qualification-20261104/comparison.json")
accepted_j_comparison = read("provenance/shared-order-inherited-type-qualification-20261104/comparison.json")
assert accepted_j_comparison["recipient"] == J
assert accepted_j_comparison["mechanical_comparison_passed"]
sys.path.insert(0, str(W / "scripts"))
spec = importlib.util.spec_from_file_location("fdsa_tail_source_reader", W / "scripts/check.py")
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
imports = re.compile(r"^(?:public\s+)?import\s+([^\n]+)", re.MULTILINE)
sources, external, edges = {}, set(), []
pending = list(old["source_closure_roots"])
while pending:
    module = pending.pop()
    relative = module.replace(".", "/") + ".lean"
    if relative in sources:
        continue
    if not (W / relative).is_file():
        external.add(module)
        continue
    raw = git("show", L + ":" + relative)
    sources[relative] = {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
                         "git_blob": git("rev-parse", L + ":" + relative).decode().strip()}
    for match in imports.finditer(reader.executable_source(raw.decode())):
        for imported in match.group(1).split():
            edges.append([module, imported])
            pending.append(imported)
assert len(sources) == 23 and len(external) == 32 and len(edges) == 58
assert sources == old["selected_projection"]["local_sources"]
assert sorted(edges) == sorted(old["source_import_edges"])
assert sorted(external) == old["selected_projection"]["eligible_external_imports"]
stems = {".lake/build/lib/lean/" + p.removesuffix(".lean") for p in sources}
supported_keys = {stem + suffix for stem in stems
                  for suffix in (".olean", ".olean.hash", ".olean.private", ".olean.server", ".trace")}


def projection(observation):
    selected = {k: v for k, v in observation["local_compiler_objects_and_traces"].items()
                if k in supported_keys}
    assert len(selected) == 69
    return {"local_sources": {p: observation["local_sources"][p] for p in sources},
            "local_compiler_objects_and_traces": selected,
            **{k: observation[k] for k in ("configuration", "dependencies", "runtime")},
            "eligible_external_imports": sorted(external)}


selected = projection(l145)
assert selected == projection(j145) == projection(i145) == projection(f145) == old["selected_projection"]
all_observations = (l61, l53, l314, l145, j53, j314, j145, i314, i145, f145)
for observation in all_observations:
    assert len(observation["configuration"]) == 10
    assert len(observation["dependencies"]) == 9
    assert len(observation["runtime"]) == 12
    assert all(not p["status"] for p in observation["dependencies"].values())
    for field in ("configuration", "dependencies", "runtime"):
        assert observation[field] == l61[field]
    path = Path(observation["program"]["path"])
    assert identity(path)["sha256"] == observation["program"]["sha256"]
assert f145["program"] == i145["program"] == j145["program"] == l145["program"]


def verify_blocks(path, blocks, names):
    raw = path.read_bytes()
    assert [b["name"] for b in blocks] == names
    for block in blocks:
        part = raw[block["byte_start"]:block["byte_end_exclusive"]]
        assert len(part) == block["bytes"] and hashlib.sha256(part).hexdigest() == block["sha256"]
    return identity(path)


actual_outputs = {}
for label, directory, observed in (
    ("Tail61", "shared-tail-complete-public-statements61-20261104-attempt1", l61),
    ("J53", "shared-order-complete-public-statements53-20261104-attempt1", j53),
    ("I314", "shared-four-complete-public-statements314-20261104-attempt1", i314),
):
    blocks = read("provenance/" + directory + "/output-blocks.json")
    path = Path(blocks["native_output"]["path"])
    value = verify_blocks(path, blocks["blocks"], observed["program"]["names"])
    assert value["sha256"] == blocks["native_output"]["sha256"]
    actual_outputs[label] = value
mapping110 = old["actual110_mapping"]
blocks110 = [row["actual_F145_output"] for row in mapping110]
names110 = [row["name"] for row in mapping110]
positions = list(range(20, 84)) + list(range(100, 146))
assert [b["ordinal"] for b in blocks110] == positions
assert [f145["program"]["names"][n-1] for n in positions] == names110
actual_outputs["F110"] = verify_blocks(C / "provenance/foundation-complete-public-statements145-20261104-attempt1/native-records/output.log", blocks110, names110)
assert len(l61["program"]["names"]) == 61
assert len(set(l61["program"]["names"] + j53["program"]["names"] + i314["program"]["names"] + names110)) == 538

result = {"utc": datetime.now(timezone.utc).isoformat(), "recipient": L,
          "accepted_predecessor": J, "I_producer": I, "Foundation_producer": F,
          "mechanical_comparison_passed": True, "semantic_final_dispositions": "Pending both independent axes",
          "receiving_credit_granted_by_this_record": 0,
          "current61": {"names": l61["program"]["names"], "local_sources": 9,
                        "complete_artifact_keys": sorted(l61["local_compiler_objects_and_traces"])},
          "J53": {"names": j53["program"]["names"], "local_sources": 6,
                  "complete_artifact_keys": sorted(l53["local_compiler_objects_and_traces"]),
                  "all_exact_non_candidate_fields_compared": list(fields)},
          "I314": {"names": i314["program"]["names"], "local_sources": 27,
                   "complete_artifact_keys": sorted(l314["local_compiler_objects_and_traces"]),
                   "all_exact_non_candidate_fields_compared": list(fields)},
          "F110": {"names": names110, "positions_1_based": positions, "local_sources": 23,
                   "complete_artifact_keys": sorted(selected["local_compiler_objects_and_traces"]),
                   "direct_external_imports": sorted(external), "source_import_edges": edges,
                   "F_I_J_Tail_complete_selected_projections_equal": True},
          "actual_producer_outputs": actual_outputs,
          "observation_files": observations, "configs": 10, "clean_dependency_records": 9, "runtime_components": 12,
          "all_four_receiving_observation_pairs_surround_actual61_after_full": True,
          "no_actual53_145_or314_rerun": True, "prospective_distinct_public_account": 538,
          "conditions_retained_verbatim": old["conditions_retained_verbatim"],
          "qualification_boundary": "Exact fingerprints supplement the successful receiving guarded full run, actual61 execution and exclusive stable output ownership; no whole-environment or hostile-input authenticity claim. Both original full scopes and all semantic/final gates remain required."}
out = C / "provenance/shared-tail-inherited-type-qualification-20261104/comparison.json"
out.parent.mkdir(exist_ok=True)
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"output": str(out), "sha256": identity(out)["sha256"], "recipient": L,
                  "actual_names": 61, "J_names": 53, "I_names": 314, "F_names": 110,
                  "source_counts": [9, 6, 27, 23], "artifact_key_counts": [27, 18, 81, 69],
                  "mechanical_pass": True, "semantic_final_dispositions": "Pending both independent axes"}))

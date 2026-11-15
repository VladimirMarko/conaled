"""Run only after the recorded J full check and actual53 have closed successfully.

This records mechanical input and output identity, not a semantic review verdict.
No compiler, project output, source, ref, or earlier evidence is changed.
"""
from pathlib import Path
from datetime import datetime, timezone
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


def read(relative):
    return json.loads((C / relative).read_text())


def identity(path):
    data = path.read_bytes()
    return {"path": str(path), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def git(*args):
    return subprocess.check_output(["git", "-C", str(W), *args])


def instant(value):
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


assert git("rev-parse", "HEAD").decode().strip() == J
assert not git("status", "--porcelain=v1", "--untracked-files=all")
full_dir = C / "provenance/shared-order-full-attempt1-20261104"
types_dir = C / "provenance/shared-order-complete-public-statements53-20261104-attempt1"
full = json.loads((full_dir / "result.json").read_text())
actual = json.loads((types_dir / "result.json").read_text())
for directory, result in ((full_dir, full), (types_dir, actual)):
    owned = json.loads((directory / "owned-terminal.json").read_text())
    assert owned["actual_exit"] == result["exit_code"] == 0
    assert owned["candidate"] == result["candidate"] == result["final_head"] == J
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

j53 = pair("J53", "shared-order53-input-observations-20261104-attempt1", J, True)
j314 = pair("J314", "shared-order-inherited314-input-observations-20261104-attempt1", J, True)
j145 = pair("J145", "shared-order-foundation110-input-observations-20261104-attempt1", J, True)
i314 = pair("I314", "shared-four314-input-observations-20261104-attempt1", I)
i145 = pair("I145", "shared-four-foundation110-receiving-observations-20261104-attempt1", I)
f145 = pair("F145", "foundation145-input-observations-20261104-attempt1", F)

old = read("provenance/shared-four-foundation110-receiving-qualification-20261104/comparison.json")
blocks314 = read("provenance/shared-four-complete-public-statements314-20261104-attempt1/output-blocks.json")
fields314 = ("clean", "project", "program", "configuration", "dependencies", "runtime", "roots",
             "local_sources", "local_compiler_objects_and_traces", "direct_external_imports_of_local_closure")
assert {k: i314[k] for k in fields314} == {k: j314[k] for k in fields314}
assert len(j314["local_sources"]) == 27
assert len(j314["local_compiler_objects_and_traces"]) == 81

sys.path.insert(0, str(W / "scripts"))
spec = importlib.util.spec_from_file_location("fdsa_source_reader", W / "scripts/check.py")
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
    raw = git("show", J + ":" + relative)
    sources[relative] = {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
                         "git_blob": git("rev-parse", J + ":" + relative).decode().strip()}
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

selected = projection(j145)
assert selected == projection(i145) == projection(f145) == old["selected_projection"]
for observation in (j53, j314, j145, i314, i145, f145):
    assert len(observation["configuration"]) == 10
    assert len(observation["dependencies"]) == 9
    assert len(observation["runtime"]) == 12
    assert all(not p["status"] for p in observation["dependencies"].values())
for observation in (i314, j314, f145, i145, j145):
    path = Path(observation["program"]["path"])
    assert identity(path)["sha256"] == observation["program"]["sha256"]
assert f145["program"] == i145["program"] == j145["program"]

def verify_blocks(path, blocks, names):
    raw = path.read_bytes()
    assert [b["name"] for b in blocks] == names
    for block in blocks:
        part = raw[block["byte_start"]:block["byte_end_exclusive"]]
        assert len(part) == block["bytes"] and hashlib.sha256(part).hexdigest() == block["sha256"]
    return identity(path)

log314 = verify_blocks(Path(blocks314["native_output"]["path"]), blocks314["blocks"], i314["program"]["names"])
assert log314["sha256"] == blocks314["native_output"]["sha256"]
mapping110 = old["actual110_mapping"]
blocks110 = [row["actual_F145_output"] for row in mapping110]
names110 = [row["name"] for row in mapping110]
positions = list(range(20, 84)) + list(range(100, 146))
assert [b["ordinal"] for b in blocks110] == positions
assert [f145["program"]["names"][n-1] for n in positions] == names110
log145 = verify_blocks(C / "provenance/foundation-complete-public-statements145-20261104-attempt1/native-records/output.log", blocks110, names110)
assert len(set(j53["program"]["names"] + i314["program"]["names"] + names110)) == 477

result = {"utc": datetime.now(timezone.utc).isoformat(), "recipient": J,
          "accepted_predecessor": I, "Foundation_producer": F,
          "mechanical_comparison_passed": True, "semantic_final_dispositions": "Pending both independent axes",
          "receiving_credit_granted_by_this_record": 0,
          "I314": {"names": i314["program"]["names"], "local_sources": 27, "complete_artifact_keys": sorted(j314["local_compiler_objects_and_traces"]),
                   "all_exact_identity_fields_compared": list(fields314), "actual_producer_output": log314},
          "F110": {"names": names110, "positions_1_based": positions, "local_sources": 23,
                   "complete_artifact_keys": sorted(selected["local_compiler_objects_and_traces"]),
                   "direct_external_imports": sorted(external), "source_import_edges": edges,
                   "F_I_J_complete_selected_projections_equal": True, "actual_producer_output": log145},
          "observation_files": observations, "configs": 10, "clean_dependency_records": 9, "runtime_components": 12,
          "all_three_receiving_observation_pairs_surround_actual53_after_full": True,
          "no_actual145_or314_rerun": True, "prospective_distinct_public_account": 477,
          "conditions_retained_verbatim": old["conditions_retained_verbatim"],
          "qualification_boundary": "Exact fingerprints supplement the successful receiving guarded full run, actual53 execution and exclusive stable output ownership; no whole-environment or hostile-input authenticity claim. Both original full scopes and all semantic/final gates remain required."}
out = C / "provenance/shared-order-inherited-type-qualification-20261104/comparison.json"
out.parent.mkdir(exist_ok=True)
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"output": str(out), "sha256": identity(out)["sha256"], "recipient": J,
                  "I_names": 314, "F_names": 110, "source_counts": [27, 23],
                  "artifact_key_counts": [81, 69], "mechanical_pass": True,
                  "semantic_final_dispositions": "Pending both independent axes"}))

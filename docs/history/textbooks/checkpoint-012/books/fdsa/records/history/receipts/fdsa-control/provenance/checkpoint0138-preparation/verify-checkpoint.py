"""Verify the held current-recovery archive; do not run a compiler or restore."""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
import sys
import tarfile

sys.dont_write_bytecode = True
os.environ["GIT_OPTIONAL_LOCKS"] = "0"
prep = Path(__file__).resolve().parent
control = prep.parents[1]
base = control.parent
name = "conaled-fdsa-0138-tree-cache-accepted-and-chapter04-progress"
accepted = "90469ce4ba3fc49397d369a5db7d58aec7014f58"
chapter3_accepted = "298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2"
accepted_tree = "18bf4bc9df979d4ee6ac76182f58faed235a0714"
chapter3_tree = "ecb69c3918715cbe0682028cd8697dfcf3e463f9"
xr_accepted = "c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5"
xr_tree = "b62fe504a38948e61c6377a4e7661b639c28c08c"
original_q = "2da5708478a1d943a9214b5b386ec2db16cd9eca"


def identity(path):
    with path.open("rb") as stream:
        return {"bytes": path.stat().st_size,
                "sha256": hashlib.file_digest(stream, "sha256").hexdigest()}


def read(path):
    return json.loads(path.read_text())


capture = read(prep / "capture.json")
assert capture["checkpoint"] == name and capture["accepted_head"] == accepted
assert capture["all_writers_held"] and not capture["compiler_live"]
creation = read(prep / "creation-subprocess-result.json")
terminal = read(prep / "creation-terminal.json")
assert creation["actual_exit"] == terminal["actual_exit"] == 0
assert creation["log"] == {"path": str(prep / "create.log"),
                           **identity(prep / "create.log")}
archive = base / "checkpoints" / (name + ".tar.gz")
sidecar = read(archive.with_name(name + ".json"))
outer = identity(archive)
assert outer == {"bytes": sidecar["size_bytes"], "sha256": sidecar["sha256"]}

actual, seen = {}, set()
manifest = sums = None
with tarfile.open(archive, "r|gz") as stream:
    for member in stream:
        path = PurePosixPath(member.name)
        assert not path.is_absolute() and ".." not in path.parts and path.parts[0] == name
        assert member.name not in seen
        seen.add(member.name)
        if member.isdir():
            continue
        assert member.isfile(), member.name
        relative = str(PurePosixPath(*path.parts[1:]))
        content = stream.extractfile(member)
        assert content is not None
        if relative in ("MANIFEST.json", "SHA256SUMS"):
            data = content.read()
            actual[relative] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
            if relative == "MANIFEST.json":
                manifest = json.loads(data)
            else:
                sums = data.decode()
        else:
            actual[relative] = {"bytes": member.size,
                                "sha256": hashlib.file_digest(content, "sha256").hexdigest()}
assert manifest is not None and sums is not None
expected = {}
for line in sums.splitlines():
    digest, relative = line.split("  ", 1)
    assert relative not in expected
    expected[relative] = digest
assert set(expected) == set(actual) - {"SHA256SUMS"}
for relative, digest in expected.items():
    assert actual[relative]["sha256"] == digest, relative
assert manifest["format"] == 2 and manifest["checkpoint"] == name
assert actual["fdsa-control/provenance/checkpoint0138-preparation/capture.json"] == identity(prep / "capture.json")

spec = importlib.util.spec_from_file_location("compact_reader", control / "checkpoint_compact.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
repo = base / "conaled"
refs = [{"oid": p[0], "ref": p[1], "symref": p[2]} for p in
        (line.split(" ", 2) for line in module.git(repo, "for-each-ref",
         "--format=%(objectname) %(refname) %(symref)").splitlines())]
assert refs == manifest["refs"] == capture["refs"]
current_refs = {row["ref"]: row for row in refs}
previous_manifest = read(prep / "previous-manifest-0137.json")
assert previous_manifest["checkpoint"] == "conaled-fdsa-0137-chapter03-accepted"
assert len(previous_manifest["refs"]) == 74
previous_refs = {row["ref"]: row for row in previous_manifest["refs"]}
allowed_advances = {"refs/heads/work/fdsa-book"}
advanced = []
for ref, row in previous_refs.items():
    assert ref in current_refs
    if current_refs[ref] != row:
        assert ref in allowed_advances and current_refs[ref]["symref"] == row["symref"]
        module.git(repo, "merge-base", "--is-ancestor", row["oid"], current_refs[ref]["oid"])
        advanced.append(ref)
integration_ref = "refs/heads/work/fdsa-ch03-integration"
assert integration_ref in previous_refs
new_refs = {"refs/heads/work/fdsa-tree-cache-integration",
            "refs/heads/work/fdsa-ch04-structural",
            "refs/heads/work/fdsa-ch04-balancing",
            "refs/heads/work/fdsa-ch04-exercises"}
assert set(current_refs) == set(previous_refs) | new_refs
assert not new_refs & set(previous_refs) and len(current_refs) == 78
for ref in new_refs:
    assert current_refs[ref]["symref"] == ""
    module.git(repo, "merge-base", "--is-ancestor", accepted, current_refs[ref]["oid"])
book_ref = "refs/heads/work/fdsa-book"
assert previous_refs[book_ref]["oid"] == chapter3_accepted
assert current_refs[book_ref]["oid"] == accepted
assert current_refs[book_ref]["symref"] == previous_refs[book_ref]["symref"]
assert book_ref in advanced
assert current_refs[integration_ref]["symref"] == ""
integration_origin = "660f974640fb89a766b26a4d786ae7ed197cecf2"
module.git(repo, "merge-base", "--is-ancestor", xr_accepted, integration_origin)
module.git(repo, "merge-base", "--is-ancestor", integration_origin,
           current_refs[integration_ref]["oid"])
integration_worktree = base / "conaled-ch02-natural-runs"
assert current_refs[integration_ref]["oid"] == chapter3_accepted
assert module.git(integration_worktree, "branch", "--show-current").strip() == "work/fdsa-tree-cache-integration"
assert module.git(integration_worktree, "rev-parse", "HEAD").strip() == accepted
assert current_refs["refs/heads/work/fdsa-tree-cache-integration"]["oid"] == accepted

live = module.worktrees(repo)
assert live == capture["worktrees"]
assert len(live) == len(manifest["worktrees"]) == 9
retirement_dir = control / "provenance/inactive-worktree-retirement-20261104"
retirement = read(retirement_dir / "result.json")
retirement_pre = read(retirement_dir / "preflight.json")
persistence = read(retirement_dir / "separate-persistence.json")
assert retirement["actual_git_exits"] == [0] * 6 and retirement["removed_worktrees"] == 6
assert persistence["all_six_paths_remain_absent"] and persistence["all_protected_refs_still_match"]
retired_paths = {row["path"] for row in retirement_pre["targets"]}
assert len(retired_paths) == 6
assert {row["path"] for row in live} == {row["path"] for row in previous_manifest["worktrees"]}
for row in retirement_pre["targets"]:
    assert not Path(row["path"]).exists()
    assert current_refs[row["branch_ref"]]["oid"] == row["head"]
    assert module.git(repo, "rev-parse", row["head"] + "^{tree}").strip() == row["tree"]
for now, saved in zip(live, manifest["worktrees"]):
    assert all(now[k] == saved[k] for k in now), now["path"]
assert manifest["external_assets"] == [module.ASSET]
assert module.git(repo, "rev-parse", "HEAD").strip() == accepted
assert module.git(repo, "rev-parse", "work/fdsa-book").strip() == accepted
assert module.git(repo, "rev-parse", "HEAD^{tree}").strip() == accepted_tree
assert not module.git(repo, "diff", "--name-only").strip()
assert not module.git(repo, "diff", "--cached", "--name-only").strip()
qualified = base / "conaled-ch01-review"
assert module.git(qualified, "rev-parse", "HEAD").strip() == capture["qualified_candidate"]
assert not module.git(qualified, "status", "--porcelain=v1", "--untracked-files=all").strip()

for relative, expected_identity in capture["held_control"].items():
    assert identity(control / relative) == expected_identity, relative
    assert actual["fdsa-control/" + relative] == expected_identity, relative
previous_controls = read(control / "provenance/checkpoint0137-preparation/capture.json")["held_control"]
allowed = set(capture["declared_prior_control_updates"])
assert allowed <= {"CURRENT.md", "STATUS.md", "checkpoints.json",
                   "reviews/binary-tree-cache-round1.md", "reviews/chapter03-round1.md",
                   "reviews/README.md", "tickets/FDSA-003.md", "tickets/FDSA-004.md",
                   "tickets/FDSA-XT01.md", "tickets/INDEX.md"}
changed = []
for relative, old in previous_controls.items():
    assert relative in capture["held_control"], relative
    if capture["held_control"][relative] != old:
        assert relative in allowed, relative
        changed.append(relative)
assert sorted(changed) == sorted(capture["actual_prior_control_updates"])

acceptance = read(control / "provenance/chapter02-acceptance-20261104/acceptance.json")
assert acceptance["accepted_commit"] == "2da5708478a1d943a9214b5b386ec2db16cd9eca" and acceptance["accepted_tree"] == "fe0bd9f17a5e1a09797be55fd79491e8c363cbd0"
assert acceptance["independent_axes"]["Standards"]["outcome"] == "Passed"
assert acceptance["independent_axes"]["Spec"]["outcome"] == "PASS"
for axis in acceptance["independent_axes"].values():
    assert axis["unresolved"] == 0 and axis["full_saved_readback_and_hold"]
assert acceptance["immediate_verification"]["actual_exit"] == acceptance["fast_forward"]["actual_exit"] == 0
durability = read(control / "provenance/chapter02-acceptance-20261104/durability.json")
assert durability["status"] == "succeeded" and durability["C2_acceptance_durability_complete"]
assert durability["library_file_id"] == "libfile_bd68f45a79dc8191b9bba484b30eb4a6"
xr = read(control / "provenance/affine-recurrence-acceptance-20261104/acceptance.json")
assert xr["accepted_commit"] == xr_accepted and xr["accepted_tree"] == xr_tree
assert xr["original_scope_paths"] == 5 and xr["authored_public_names"] == 21
for axis in xr["independent_axes"].values():
    assert axis["outcome"].upper() in {"PASS", "PASSED"} and axis["unresolved"] == 0
    assert axis["full_saved_readback_and_hold"]
assert set(xr["independent_axes"]) == {"Standards", "Spec"}
assert xr["full_check"]["actual_exit"] == xr["immediate_verification"]["actual_exit"] == xr["fast_forward"]["actual_exit"] == 0
assert xr["actual_public_types"]["count"] == 21 and xr["actual_public_types"]["stable_pre_post_identity"]
assert not xr["chapter03_accepted"]
xr_durability = read(control / "provenance/affine-recurrence-acceptance-20261104/durability.json")
assert xr_durability["status"] == "succeeded"
assert xr_durability["library_file_id"] == "libfile_42e1b111f1c08191abb8bcf105cee504"

# Preserve actual Chapter 3 acceptance, without performing an acceptance action.
def checked_binding(row):
    path = Path(row["path"])
    assert path.is_relative_to(control), str(path)
    expected_identity = {key: row[key] for key in ("bytes", "sha256")}
    assert identity(path) == expected_identity, str(path)
    assert actual["fdsa-control/" + str(path.relative_to(control))] == expected_identity
    return path


c3_path = checked_binding(capture["chapter03_acceptance"])
assert c3_path == control / "provenance/chapter03-acceptance-20261105/acceptance.json"
c3 = read(c3_path)
assert c3["accepted_commit"] == chapter3_accepted and c3["accepted_tree"] == chapter3_tree
assert c3["previous_accepted_commit"] == xr_accepted and c3["original_whole_task_base"] == original_q
assert c3["accepted_branch"] == "work/fdsa-book" and c3["approved_candidate_branch"] == "work/fdsa-ch03-integration"
assert c3["chapter03_accepted"] and not c3["all27_chapters_and_appendices_complete"]
assert c3["obligations"] == 83 and c3["original_scope_paths"] == 84
assert c3["original_formal_modules"] == 80 and c3["chapter03_formal_modules"] == 78
assert c3["chapter03_public_names"] == 1370 and c3["accepted_XR_public_names"] == 21 and c3["actual_public_names"] == 1391
assert c3["obligation_ids"] == [f"C03-{n:03}" for n in range(1, 84)]
assert module.git(repo, "symbolic-ref", "HEAD").strip() == book_ref
assert current_refs[integration_ref]["oid"] == chapter3_accepted
assert module.git(repo, "rev-parse", chapter3_accepted + "^{tree}").strip() == chapter3_tree
for row in c3["bound_files"]:
    checked_binding(row)
checked_binding(c3["frozen_obligations"])
assert c3["frozen_obligations"]["sha256"] == "eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed"
assert identity(qualified / "docs/research/fdsa-selection.md") == {key: c3["correspondence_document"][key] for key in ("bytes", "sha256")}
coverage = read(control / "provenance/chapter03-acceptance-20261105/coverage.json")
assert coverage["candidate"] == chapter3_accepted and coverage["original_task_base"] == original_q
assert [row["id"] for row in coverage["rows"]] == c3["obligation_ids"]
assert all(row["status"] == "accepted" and row["candidate"] == chapter3_accepted for row in coverage["rows"])
assert set(c3["independent_axes"]) == {"Standards", "Spec"}
for axis_name, axis in c3["independent_axes"].items():
    assert axis["outcome"].upper() in {"PASS", "PASSED"} and axis["unresolved"] == 0
    assert axis["full_saved_readback_and_hold"] and axis["candidate"] == chapter3_accepted and axis["original_task_base"] == original_q
    for key in ("report", "final_record", "hold", "completion_readback_receipt"):
        checked_binding(axis[key])
    assessment = read(Path(axis["final_record"]["path"]))
    hold = read(Path(axis["hold"]["path"]))
    assert assessment["outcome"].upper() in {"PASS", "PASSED"}
    for record in (assessment, hold):
        assert record["candidate"] == chapter3_accepted and record["tree"] == chapter3_tree and record["original_task_base"] == original_q
    assert "HELD" in hold["state"] and not hold["unresolved_findings"]
    if axis_name == "Standards":
        disposition = assessment["final_standards_disposition"]
        assert disposition["full_original_scope_complete"] and disposition["all_83_obligations_preserved_and_assessed"]
        assert disposition["all_1391_final_names_qualified"] and disposition["normal_full_check_and_exhaustive_audit_established"]
        assert not disposition["unresolved_findings"]
    else:
        assert assessment["review_complete"] and assessment["source_assessment_complete"] and assessment["scope_obligations"] == 83
        assert not assessment["unresolved_findings"] and not assessment["new_findings"]
gate = read(checked_binding(c3["root_gate"]))
assert gate["candidate"] == chapter3_accepted and gate["candidate_tree"] == chapter3_tree and gate["accepted_base"] == xr_accepted
assert gate["original_whole_task_base"] == original_q and gate["original_scope_paths"] == 84 and gate["obligations"] == 83
assert gate["chapter03_public_names"] == 1370 and gate["accepted_XR_public_names"] == 21 and gate["actual_public_names"] == 1391
assert gate["all_required_preacceptance_gates_passed"] and gate["all_source_writers_held"] and not gate["compiler_live"]
assert set(gate["axes"]) == {"Standards", "Spec"}
for axis in gate["axes"].values():
    assert axis["outcome"].upper() in {"PASS", "PASSED"} and axis["unresolved"] == 0 and axis["complete_readback_and_hold"]
for row in gate["bound_files"]:
    checked_binding(row)
full_dir = control / "provenance/chapter03-final-complete-full-attempt1-20261105"
types_dir = control / "provenance/chapter03-final-complete-statements1391-attempt1-20261105"
immediate_dir = control / "provenance/chapter03-immediate-verification-20261105"
statement_dir = control / "provenance/chapter03-final-statement-inputs-20261105"
commands = [(full_dir, ["./check.sh", "--candidate", "HEAD"]),
            (types_dir, ["lake", "env", "lean", str(statement_dir / "Statements1391-complete.lean")]),
            (immediate_dir, ["./check.sh", "--verify-candidate", "HEAD"])]
for directory, command in commands:
    result = read(directory / "result.json")
    owned = read(directory / "owned-terminal.json")
    actual_terminal = read(directory / "actual-tool-terminal.json")
    native = read(directory / "native-records/result.json")
    closed = read(directory / "closed-evidence-reconciliation.json")
    assert result["exit_code"] == owned["actual_exit"] == actual_terminal["exit_code"] == native["exit_code"] == 0
    assert result["candidate"] == result["final_head"] == owned["candidate"] == chapter3_accepted and not result["final_status"]
    assert owned["terminal_tool_chunk"] == actual_terminal["chunk_id"] and closed["complete_closed_log"]
    assert native["command"] == command and native["lean_threads"] == "1" and native["cwd"] == str(qualified)
    assert not native["timed_out"] and native["recorder_error"] is None
    assert identity(directory / "full.log") == {"bytes": result["log_size_bytes"], "sha256": result["log_sha256"]}
    assert (directory / "full.log").read_bytes() == ((directory / "outer-prefix.log").read_bytes() + (directory / "native-records/output.log").read_bytes() + (directory / "outer-suffix.log").read_bytes())
    assert (directory / "verification.json").read_bytes() == (full_dir / "verification.json").read_bytes()
assert next(row["head"] for row in previous_manifest["worktrees"] if row["path"] == str(qualified)) == chapter3_accepted
verification = read(full_dir / "verification.json")
assert verification["candidate"] == chapter3_accepted and verification["result"] == "passed" and verification["mode"] == "incremental"
assert identity(full_dir / "verification.json")["sha256"] == "152ccbf0ee1d37fbe8eef300d88ad16284858464e5c4dc82f1f3884db3641088"
audit = read(checked_binding(c3["full_check"]["audit_reconciliation"]))
assert (audit["checked_modules"], audit["audit_rows"], audit["logical_declarations"], audit["theorem_declarations"], audit["unsafe_runtime_declarations"]) == (1109, 1107, 50135, 29316, 0)
assert set(audit["axiom_union"]) == {"propext", "Classical.choice", "Quot.sound"}
assert audit["all80_original_scope_modules_in_audit_rows"] and audit["source_policy_passed"]
assert audit["pre_invalidated_modules"] == audit["post_inconsistent_modules"] == 0
types = c3["actual_public_types"]
assert types["actual_exit"] == 0 and types["candidate"] == chapter3_accepted and types["count"] == 1391 and types["stable_pre_post_identity"]
checked_binding(types["program"])
assert types["program"]["sha256"] == "a4671a1d5cd377fcdd0899d7700a3b7b635faeef18b9006bab2cfa3521c2aa2d"
observations = read(checked_binding(types["observation_reconciliation"]))
assert observations["candidate"] == chapter3_accepted and observations["identity_equal"] and observations["actual_exit"] == 0
assert (observations["sources"], observations["objects_and_traces"], observations["configuration"], observations["dependencies"], observations["runtime_components"]) == (113, 339, 10, 9, 12)
assert read(statement_dir / "pre-inputs.json")["identity"] == read(statement_dir / "post-inputs.json")["identity"]
assert c3["full_check"]["actual_exit"] == c3["immediate_verification"]["actual_exit"] == c3["fast_forward"]["actual_exit"] == 0
assert c3["immediate_verification"]["matching_full_verification"] and c3["immediate_verification"]["command"] == ["./check.sh", "--verify-candidate", "HEAD"]
ff = read(checked_binding(c3["fast_forward"]["result"]))
ff_pre = read(checked_binding(c3["fast_forward"]["preflight"]))
ff_start = read(checked_binding(c3["fast_forward"]["start"]))
ff_actual = read(checked_binding(c3["fast_forward"]["actual_tool_result"]))
ff_command = read(checked_binding(ff["command_result"]))
assert ff["actual_exit"] == ff_actual["exit_code"] == ff_command["actual_exit"] == 0
assert ff["old"] == xr_accepted and ff["accepted_commit"] == chapter3_accepted and ff["accepted_tree"] == chapter3_tree
assert ff["only_changed_ref"] == book_ref and ff["other_refs_preserved"] == 73 and ff["other_worktree_heads_preserved"] == 8
assert ff["all_worktree_statuses_preserved"] and ff["qualified_source_and_verification_preserved"] and ff["local_fast_forward_only"]
assert ff_pre["old"] == xr_accepted and ff_pre["candidate"] == chapter3_accepted
expected_after = dict(ff_pre["all_refs"]); expected_after[book_ref] = chapter3_accepted
assert {key: value["oid"] for key, value in previous_refs.items()} == expected_after
previous_worktrees = {row["path"]: row for row in previous_manifest["worktrees"]}
for worktree in ff_pre["worktrees"]:
    path = Path(worktree["path"])
    expected_head = chapter3_accepted if path == repo else worktree["head"]
    assert previous_worktrees[str(path)]["head"] == expected_head
    assert previous_worktrees[str(path)]["status"] == worktree["status"]
assert ff_start["argv"] == ["git", "-C", str(repo), "merge", "--ff-only", chapter3_accepted]
immediate_result = read(immediate_dir / "result.json")
assert datetime.fromisoformat(immediate_result["completed_utc"]) < datetime.fromisoformat(ff_start["started_utc"]) <= datetime.fromisoformat(ff["completed_utc"])
measured_delay = (datetime.fromisoformat(ff["completed_utc"]) - datetime.fromisoformat(immediate_result["completed_utc"])).total_seconds()
assert abs(measured_delay - ff["elapsed_seconds_after_immediate_completion"]) < 0.01
assert c3["accepted_utc"] == ff["completed_utc"]

# The new XT01 acceptance uses the same complete validation and review gates.
xt_path = checked_binding(capture["tree_cache_acceptance"])
assert xt_path == control / "provenance/binary-tree-cache-acceptance-20261105/acceptance.json"
xt = read(xt_path)
assert xt["unit"] == "FDSA-XT01" and xt["unit_accepted"]
assert xt["accepted_commit"] == accepted and xt["accepted_tree"] == accepted_tree
assert xt["previous_accepted_commit"] == chapter3_accepted
assert xt["original_unit_base"] == "a14977b9e316cc484ffad8a470d26b15615956c0"
assert xt["original_donor"] == "64c6b777d828ecfe83234fc2aed94600a1f24297"
assert xt["accepted_branch"] == "work/fdsa-book"
assert xt["approved_candidate_branch"] == "work/fdsa-tree-cache-integration"
assert xt["requirements_ids"] == [f"XT01-{i:02}" for i in range(1, 8)]
assert xt["authored_public_names"] == 115 and len(xt["original_scope_paths"]) == 7
assert len(xt["formal_modules"]) == 4 and not xt["chapter04_accepted"]
assert not xt["all27_chapters_and_appendices_complete"]
checked_binding(xt["requirements"])
assert xt["requirements"]["sha256"] == "81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce"
for row in xt["bound_files"]:
    checked_binding(row)
xt_scope_paths = ["Applications/Resources/TreeCache.lean", "Applications/Trees/Cached.lean",
                  "Applications/Trees/Observations.lean", "Examples/TreeCache.lean",
                  "SquareApplications.lean", "docs/research/fdsa-reconstruction-map.md",
                  "docs/research/fdsa-tree-cache.md"]
assert xt["original_scope_paths"] == xt_scope_paths

def require_xt_axis_scope(value, axis_name):
    assert value["unit"] == "FDSA-XT01" and value["axis"] == axis_name
    assert value["candidate"] == accepted and value["tree"] == accepted_tree
    assert value["original_unit_base"] == xt["original_unit_base"]
    assert value["original_donor"] == xt["original_donor"]
    assert value["incorporated_base"] == chapter3_accepted
    assert value["requirements_ids"] == xt["requirements_ids"]
    assert value["original_scope_paths"] == xt_scope_paths and value["public_names"] == 115
    assert value["outcome"].upper() in {"PASS", "PASSED"} and not value["unresolved_findings"]
    for flag in ("full_original_scope_complete", "actual_public_types_complete", "full_validation_accepted", "review_complete"):
        assert value[flag] is True, (axis_name, flag)

assert set(xt["independent_axes"]) == {"Standards", "Spec"}
for axis_name, axis in xt["independent_axes"].items():
    assert axis["outcome"].upper() in {"PASS", "PASSED"} and axis["unresolved"] == 0
    assert axis["candidate"] == accepted and axis["full_saved_readback_and_hold"]
    for key in ("report", "final_record", "hold", "completion_readback_receipt"):
        checked_binding(axis[key])
    assessment = read(checked_binding(axis["final_record"]))
    hold = read(checked_binding(axis["hold"]))
    require_xt_axis_scope(assessment, axis_name)
    require_xt_axis_scope(hold, axis_name)
    assert "HELD" in hold["state"]
xt_gate = read(checked_binding(xt["root_gate"]))
assert xt_gate["unit"] == "FDSA-XT01"
assert xt_gate["candidate"] == accepted and xt_gate["candidate_tree"] == accepted_tree
assert xt_gate["accepted_base"] == xt_gate["incorporated_base"] == chapter3_accepted
assert xt_gate["original_unit_base"] == xt["original_unit_base"]
assert xt_gate["original_donor"] == xt["original_donor"]
assert xt_gate["requirements_ids"] == xt["requirements_ids"]
assert xt_gate["original_scope_paths"] == xt_scope_paths and xt_gate["actual_public_names"] == 115
assert xt_gate["full_original_scope_complete"] and xt_gate["original_formal_source_modules"] == 4
assert xt_gate["all_required_preacceptance_gates_passed"]
assert xt_gate["all_source_writers_held"] and not xt_gate["compiler_live"]
assert set(xt_gate["axes"]) == {"Standards", "Spec"}
for axis_name, axis in xt_gate["axes"].items():
    assert axis["outcome"].upper() in {"PASS", "PASSED"} and axis["unresolved"] == 0
    assert axis["complete_readback_and_hold"] and axis["unit"] == "FDSA-XT01"
    assert axis["candidate"] == accepted and axis["tree"] == accepted_tree
    assert axis["original_unit_base"] == xt["original_unit_base"] and axis["original_donor"] == xt["original_donor"]
    assert axis["incorporated_base"] == chapter3_accepted
    assert axis["requirements_ids"] == xt["requirements_ids"] and axis["original_scope_paths"] == xt_scope_paths
    assert axis["public_names"] == 115
    for flag in ("full_original_scope_complete", "actual_public_types_complete", "full_validation_accepted", "review_complete"):
        assert axis[flag] is True, (axis_name, flag)
    for key in ("final_record", "hold", "report"):
        assert axis[key] == xt["independent_axes"][axis_name][key]
    assert axis["receipt"] == xt["independent_axes"][axis_name]["completion_readback_receipt"]
for row in xt_gate["bound_files"]:
    checked_binding(row)
xt_full = control / "provenance/binary-tree-cache-receiving-full-attempt1-20261105"
xt_types = control / "provenance/binary-tree-cache-receiving-statements115-attempt1-20261105"
xt_immediate = control / "provenance/binary-tree-cache-immediate-verification-20261105"
xt_statements = control / "provenance/binary-tree-cache-receiving-statements115-20261105"
xt_commands = [(xt_full, ["./check.sh", "--candidate", "HEAD"]),
               (xt_types, ["lake", "env", "lean", str(xt_statements / "Statements115-complete.lean")]),
               (xt_immediate, ["./check.sh", "--verify-candidate", "HEAD"])]
for directory, command in xt_commands:
    result = read(directory / "result.json")
    owned = read(directory / "owned-terminal.json")
    actual_terminal = read(directory / "actual-tool-terminal.json")
    native = read(directory / "native-records/result.json")
    closed = read(directory / "closed-evidence-reconciliation.json")
    assert result["exit_code"] == owned["actual_exit"] == actual_terminal["exit_code"] == native["exit_code"] == 0
    assert result["candidate"] == result["final_head"] == owned["candidate"] == accepted
    assert not result["final_status"] and closed["complete_closed_log"]
    assert owned["terminal_tool_chunk"] == actual_terminal["chunk_id"]
    assert native["command"] == command and native["lean_threads"] == "1"
    assert native["cwd"] == str(qualified) and not native["timed_out"] and native["recorder_error"] is None
    assert identity(directory / "full.log") == {"bytes": result["log_size_bytes"], "sha256": result["log_sha256"]}
    assert (directory / "full.log").read_bytes() == ((directory / "outer-prefix.log").read_bytes() + (directory / "native-records/output.log").read_bytes() + (directory / "outer-suffix.log").read_bytes())
    if directory != xt_types:
        assert (directory / "verification.json").read_bytes() == (xt_full / "verification.json").read_bytes()
# The type run preceded the full check; its inherited old record grants no XT01 credit.
assert read(xt_types / "verification.json")["candidate"] == chapter3_accepted
assert (qualified / ".lake/verification.json").read_bytes() == (xt_full / "verification.json").read_bytes()
xt_verification = read(xt_full / "verification.json")
assert xt_verification["candidate"] == accepted and xt_verification["result"] == "passed"
assert xt_verification["mode"] == "incremental"
xt_audit = read(checked_binding(xt["full_check"]["audit_reconciliation"]))
assert xt_audit["source_policy_passed"] and xt_audit["all4_scope_modules_in_audit_rows"]
assert xt_audit["checked_modules"] == 1113 and xt_audit["audit_rows"] == 1111
assert xt_audit["unsafe_runtime_declarations"] == 0
assert xt_audit["pre_invalidated_modules"] == xt_audit["post_inconsistent_modules"] == 0
assert set(xt_audit["axiom_union"]) == {"propext", "Classical.choice", "Quot.sound"}
xt_pre = read(xt_statements / "pre-inputs.json")["identity"]
xt_post = read(xt_statements / "post-inputs.json")["identity"]
assert xt_pre == xt_post and xt_pre["candidate"] == accepted
assert len(xt_pre["program"]["names"]) == 115
assert [len(xt_pre[k]) for k in ("local_sources", "local_compiler_objects_and_traces", "configuration", "dependencies", "runtime")] == [26, 78, 10, 9, 12]
assert xt["actual_public_types"]["actual_exit"] == 0 and xt["actual_public_types"]["count"] == 115
xt_program = checked_binding(xt["actual_public_types"]["program"])
assert xt_program == xt_statements / "Statements115-complete.lean"
assert identity(xt_program) == {"bytes": 4721, "sha256": "eea207cce83ce453b3625076041ff1262235771a8b92add322a149a044c98738"}
assert xt_gate["actual_statement_qualification"]["program"] == xt["actual_public_types"]["program"]
assert xt["actual_public_types"]["stable_pre_post_identity"]
xt_observation = read(checked_binding(xt["actual_public_types"]["observation_reconciliation"]))
assert xt_observation["candidate"] == accepted and xt_observation["same_inputs"]
assert xt_observation["actual_exit"] == 0
xt_ff = read(checked_binding(xt["fast_forward"]["result"]))
xt_ff_pre = read(checked_binding(xt["fast_forward"]["preflight"]))
xt_ff_start = read(checked_binding(xt["fast_forward"]["start"]))
xt_ff_actual = read(checked_binding(xt["fast_forward"]["actual_tool_result"]))
xt_ff_command = read(checked_binding(xt_ff["command_result"]))
assert xt_ff["actual_exit"] == xt_ff_actual["exit_code"] == xt_ff_command["actual_exit"] == 0
assert xt_ff["old"] == chapter3_accepted and xt_ff["accepted_commit"] == accepted
assert xt_ff["accepted_tree"] == accepted_tree and xt_ff["only_changed_ref"] == book_ref
assert xt_ff["other_refs_preserved"] == 77 and xt_ff["other_worktree_heads_preserved"] == 8
assert xt_ff["all_worktree_statuses_preserved"] and xt_ff["qualified_source_and_verification_preserved"]
assert xt_ff["local_fast_forward_only"]
xt_expected_refs = dict(xt_ff_pre["all_refs"]); xt_expected_refs[book_ref] = accepted
assert {key: value["oid"] for key, value in current_refs.items()} == xt_expected_refs
for worktree in xt_ff_pre["worktrees"]:
    path = Path(worktree["path"])
    assert module.git(path, "rev-parse", "HEAD").strip() == (accepted if path == repo else worktree["head"])
    assert module.git(path, "status", "--porcelain=v1", "--untracked-files=all") == worktree["status"]
assert xt_ff_start["argv"] == ["git", "-C", str(repo), "merge", "--ff-only", accepted]
xt_immediate_result = read(xt_immediate / "result.json")
assert datetime.fromisoformat(xt_immediate_result["completed_utc"]) < datetime.fromisoformat(xt_ff_start["started_utc"]) <= datetime.fromisoformat(xt_ff["completed_utc"])
xt_delay = (datetime.fromisoformat(xt_ff["completed_utc"]) - datetime.fromisoformat(xt_immediate_result["completed_utc"])).total_seconds()
assert abs(xt_delay - xt_ff["elapsed_seconds_after_immediate_completion"]) < 0.01
assert xt["accepted_utc"] == xt_ff["completed_utc"]
assert xt["full_check"]["actual_exit"] == xt["immediate_verification"]["actual_exit"] == xt["fast_forward"]["actual_exit"] == 0
assert xt["immediate_verification"]["matching_full_verification"]

for item in capture["closed_development_runs"]:
    directory = control / "provenance" / item["name"]
    result = read(directory / "result.json")
    owned = read(directory / "owned-terminal.json")
    native = read(directory / "native-records/result.json")
    assert result["candidate"] == result["final_head"] == owned["candidate"] == item["candidate"]
    assert not result["final_status"]
    assert result["exit_code"] == owned["actual_exit"] == native["exit_code"] == item["exit"]
    assert identity(directory / "full.log") == {"bytes": result["log_size_bytes"], "sha256": result["log_sha256"]}
    assert native["lean_threads"] == "1" and not native["timed_out"] and native["recorder_error"] is None
    assert native["command"] == result["command"][result["command"].index("--") + 1:]
# Preserve the interrupted launch honestly; no terminal or pass is synthesized.
interrupted = capture["interrupted_development_runs"]
assert len(interrupted) == 1
for item in interrupted:
    assert item["name"] == "chapter03-random-selection-drift-focused-attempt2-20261104"
    directory = control / "provenance" / item["name"]
    evidence = control / "provenance/chapter03-drift-attempt2-interruption-20261104"
    reconciliation = read(evidence / "reconciliation.json")
    assert reconciliation["run"] == item["name"]
    assert reconciliation["candidate"] == item["candidate"] == "f535b1ef557795c4e09c97ce0daf599961c9b268"
    assert reconciliation["actual_exit"] is None and item["actual_exit"] is None
    assert reconciliation["original_exec_session_id"] is None
    assert reconciliation["no_full_or_focused_success_credit"]
    assert reconciliation["ps_observation"]["global_process_absence_not_claimed"]
    assert not (directory / "result.json").exists()
    assert not (directory / "owned-terminal.json").exists()
    assert set(reconciliation["original_outer_files"]) == {"full.log", "launch.json", "progress.json", "request.json", "start.json"}
    for filename, row in reconciliation["original_outer_files"].items():
        expected_identity = {key: row[key] for key in ("bytes", "sha256")}
        assert identity(directory / filename) == expected_identity
        assert identity(evidence / ("interrupted-outer-" + filename)) == expected_identity
        assert actual["fdsa-control/" + str((directory / filename).relative_to(control))] == expected_identity
    assert set(reconciliation["original_native_files"]) == {"output.log", "start.json"}
    for filename, row in reconciliation["original_native_files"].items():
        expected_identity = {key: row[key] for key in ("bytes", "sha256")}
        saved = evidence / ("interrupted-native-" + filename)
        assert identity(saved) == expected_identity
        assert actual["fdsa-control/" + str(saved.relative_to(control))] == expected_identity

# Keep the completed failed command distinct from its missing transport terminal.
transport = capture["transport_terminal_unavailable_runs"]
assert len(transport) == 1
for item in transport:
    assert item["name"] == "chapter03-random-selection-trace-focused-attempt1-20261104"
    directory = control / "provenance" / item["name"]
    reconciliation_path = control / item["reconciliation"]
    expected_reconciliation = {key: item[key] for key in ("bytes", "sha256")}
    assert identity(reconciliation_path) == expected_reconciliation
    assert actual["fdsa-control/" + item["reconciliation"]] == expected_reconciliation
    reconciliation = read(reconciliation_path)
    assert reconciliation["candidate"] == item["candidate"] == "0fa717b8c150e0ae6edb9d538dd2b86d73f02b2d"
    assert reconciliation["owned_session"] == item["original_exec_session_id"] == 81642
    assert reconciliation["transport_terminal_exit"] is None
    assert reconciliation["transport_terminal_tool_chunk"] is None
    assert item["transport_terminal_exit"] is None
    assert reconciliation["actual_qualified_command_exit_from_completed_native_recorder"] == 1
    assert reconciliation["outer_recorder_recorded_child_exit"] == 1
    assert not reconciliation["owned_terminal_credit"]
    assert not reconciliation["focused_pair_pass"] and not reconciliation["chapter_acceptance_credit"]
    assert reconciliation["complete_native_and_outer_logs_preserved"]
    assert reconciliation["project_lock_observation"]["exclusive_nonblocking_acquired_and_released"]
    assert reconciliation["project_lock_observation"]["global_process_absence_not_claimed"]
    assert not (directory / "owned-terminal.json").exists()
    assert item["name"] not in {row["name"] for row in capture["closed_development_runs"]}
    assert item["name"] not in {row["name"] for row in interrupted}
    result = read(directory / "result.json")
    native = read(directory / "native-records/result.json")
    assert result["candidate"] == result["final_head"] == item["candidate"] and not result["final_status"]
    assert result["exit_code"] == native["exit_code"] == item["recorded_native_exit"] == 1
    assert native["lean_threads"] == "1" and not native["timed_out"] and native["recorder_error"] is None
    assert native["command"] == result["command"][result["command"].index("--") + 1:]
    for relative, row in reconciliation["records"].items():
        expected_identity = {key: row[key] for key in ("bytes", "sha256")}
        assert identity(control / relative) == expected_identity
        assert actual["fdsa-control/" + relative] == expected_identity
    outer_bytes = (directory / "full.log").read_bytes()
    body = (directory / "native-records/output.log").read_bytes()
    prefix = (directory / "outer-prefix.log").read_bytes()
    suffix = (directory / "outer-suffix.log").read_bytes()
    assert [len(prefix), len(body), len(suffix)] == [127, 12920, 157]
    assert outer_bytes == prefix + body + suffix
    assert identity(directory / "full.log") == {"bytes": result["log_size_bytes"], "sha256": result["log_sha256"]}

kit = control / "tooling/unified-native-kit-4.35.0"
kit_rows = (kit / "SHA256SUMS").read_text().splitlines()
assert len(kit_rows) == 298
for line in kit_rows:
    digest, relative = line.split("  ", 1)
    assert identity(kit / relative)["sha256"] == digest, relative
    assert actual["fdsa-control/tooling/unified-native-kit-4.35.0/" + relative]["sha256"] == digest

record = {"verified_utc": datetime.now(timezone.utc).isoformat(), "file": str(archive),
          **outer, "payload_hashes_verified": len(expected), "refs_verified": len(refs),
          "all74_prior_refs_retained": True, "authorized_ref_advances": sorted(advanced),
          "authorized_new_refs": sorted(new_refs), "integration_origin": integration_origin,
          "retired_clean_worktrees_reconstructible": 6, "worktrees_verified": len(live),
          "held_control_hashes_verified": len(capture["held_control"]),
          "prior_control_changes_explicit": sorted(changed), "accepted_head": accepted,
          "qualified_candidate": capture["qualified_candidate"],
          "chapter02_acceptance_preserved": True, "chapter03_obligations": 83,
          "closed_development_runs_verified": len(capture["closed_development_runs"]),
          "interrupted_runs_preserved_without_terminal_or_credit": len(interrupted),
          "known_recorded_failures_without_transport_terminal": len(transport),
          "complete_native_kit_manifest_entries": 298,
          "XR_accepted_with_complete_evidence": True, "chapter03_acceptance_claimed": True,
          "chapter03_accepted_with_complete_evidence": True,
          "chapter03_actual_public_names": 1391,
          "chapter03_acceptance_record": capture["chapter03_acceptance"],
          "XT01_accepted_with_complete_evidence": True,
          "XT01_actual_public_names": 115,
          "XT01_acceptance_record": capture["tree_cache_acceptance"],
          "chapter04_accepted": False, "chapter04_obligations_retained": 76,
          "no_compiler_restore_fsck_or_acceptance_execution": True,
          "format2_creator_and_restorer_preserved": True}
with (prep / "integrity.json").open("x") as stream:
    json.dump(record, stream, indent=2)
    stream.write("\n")
print(json.dumps(record, indent=2))

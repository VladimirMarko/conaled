from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib, importlib.util, json, os, sys, tarfile
sys.dont_write_bytecode = True
os.environ["GIT_OPTIONAL_LOCKS"] = "0"
control = Path(__file__).resolve().parents[2]
prep = Path(__file__).resolve().parent
base = control.parent
# PREPARED ONLY. Root supplies actual held final bindings; this template cannot run.
Q = "2da5708478a1d943a9214b5b386ec2db16cd9eca"
L = "726cb9a9b9ff4444a7614383de4fb336e8804aa7"
Q_TREE = "fe0bd9f17a5e1a09797be55fd79491e8c363cbd0"
bindings = json.loads((prep / "final-bindings.json").read_text())
assert bindings["state"] == "actual-held-final-evidence-bound"
assert bindings["candidate"] == Q and bindings["accepted_predecessor"] == L
name = bindings["checkpoint_name"]
assert name.startswith("conaled-fdsa-0122-") and name.replace("-", "").replace("_", "").isalnum()
archive = base / "checkpoints" / (name + ".tar.gz")
sidecar = json.loads(archive.with_name(name + ".json").read_text())
creation = json.loads((prep / "creation-terminal.json").read_text())
assert creation["exit_code"] == 0
with archive.open("rb") as stream:
    outer_sha = hashlib.file_digest(stream, "sha256").hexdigest()
assert archive.stat().st_size == sidecar["size_bytes"] and outer_sha == sidecar["sha256"]
actual = {}; seen = set(); manifest = sums = None
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
        if relative in ("SHA256SUMS", "MANIFEST.json"):
            data = content.read()
            actual[relative] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
            if relative == "SHA256SUMS": sums = data.decode()
            elif relative == "MANIFEST.json": manifest = json.loads(data)
        else:
            actual[relative] = {"bytes": member.size, "sha256": hashlib.file_digest(content, "sha256").hexdigest()}
assert manifest is not None and sums is not None
expected = {}
for line in sums.splitlines():
    sha, path = line.split("  ", 1)
    assert path not in expected
    expected[path] = sha
assert set(expected) == set(actual) - {"SHA256SUMS"}
for relative, sha in expected.items():
    assert actual[relative]["sha256"] == sha, relative
assert manifest["format"] == 2 and manifest["checkpoint"] == name
spec = importlib.util.spec_from_file_location("fdsa_compact_checker", control / "checkpoint_compact.py")
module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
repo = base / "conaled"
refs = [{"oid": parts[0], "ref": parts[1], "symref": parts[2]} for parts in
        (line.split(" ", 2) for line in module.git(repo, "for-each-ref", "--format=%(objectname) %(refname) %(symref)").splitlines())]
assert refs == manifest["refs"] and len(refs) == 67
live = module.worktrees(repo)
saved = manifest["worktrees"]
assert len(live) == len(saved) == 15
for now, then in zip(live, saved):
    assert all(now[k] == then[k] for k in now), now["path"]
assert manifest["external_assets"] == [module.ASSET]
held = json.loads((prep / "capture-control-identities.json").read_text())
for relative, identity in held.items():
    file = control / relative
    with file.open("rb") as stream:
        live_identity = {"bytes": file.stat().st_size, "sha256": hashlib.file_digest(stream, "sha256").hexdigest()}
    assert live_identity == identity, relative
    assert actual["fdsa-control/" + relative] == identity, relative
accepted = module.git(repo, "rev-parse", "work/fdsa-book").strip()
candidate = module.git(base / "conaled-ch01-review", "rev-parse", "HEAD").strip()
assert accepted == Q
assert module.git(repo, "rev-parse", "HEAD").strip() == Q
assert module.git(repo, "rev-parse", "HEAD^{tree}").strip() == Q_TREE
assert not module.git(repo, "diff", "--name-only").strip()
assert not module.git(repo, "diff", "--cached", "--name-only").strip()
assert not module.git(base / "conaled-ch01-review", "status", "--porcelain=v1", "--untracked-files=all").strip()
assert candidate == "2da5708478a1d943a9214b5b386ec2db16cd9eca"

source_dir = control / "provenance/shared-chapter02-source-integration-20261104"
source = json.loads((source_dir / "receipt.json").read_text())
assert source["candidate"] == candidate and source["accepted_book"] == L
assert source["ordered_parents"] == [L, "4b5dbfa07288acc73f25c27838d3fb2f78e77d71"]
assert source["source_clean"] and source["receiving_validation_credit"] == 0 and source["compiler_calls"] == 0
assert source["actual_merge_exit"] == 1 and source["actual_commit_exit"] == 0
for row in source["payloads_excluding_receipt"]:
    content = (source_dir / row["path"]).read_bytes()
    assert len(content) == row["bytes"] and hashlib.sha256(content).hexdigest() == row["sha256"]
gate = json.loads((control / "provenance/chapter02-receiving-source-coordinator-20261104/source-review-gate.json").read_text())
assert gate["candidate"] == candidate and gate["both_source_assessments_complete"] and gate["unresolved_source_findings"] == 0
assert gate["receiving_validation_credit"] == 0
for row in gate["bound_review_files"]:
    content = (control / row["path"]).read_bytes()
    assert len(content) == row["bytes"] and hashlib.sha256(content).hexdigest() == row["sha256"]
acceptance = json.loads((control / "provenance/shared-tail-acceptance-20261104/acceptance.json").read_text())
assert acceptance["accepted_commit"] == L
assert acceptance["independent_axes"]["Standards"]["outcome"] == "Passed"
assert acceptance["independent_axes"]["Spec"]["outcome"] == "PASS"
assert acceptance["immediate_verification"]["actual_exit"] == acceptance["fast_forward"]["actual_exit"] == 0
full_dir = control / "provenance/shared-tail-full-attempt1-20261104"
run = json.loads((full_dir / "result.json").read_text())
owned = json.loads((full_dir / "owned-terminal.json").read_text())
assert owned["actual_exit"] == run["exit_code"] == 0
assert run["candidate"] == run["final_head"] == owned["candidate"] == L
assert not run["final_status"] and run["state"] == "passed"
assert hashlib.sha256((full_dir / "full.log").read_bytes()).hexdigest() == run["log_sha256"]
audit = json.loads((full_dir / "audit-and-build-summary.json").read_text())
assert (audit["checked_modules"], audit["audit_module_rows"], audit["kernel_safe_declarations"], audit["theorem_declarations"], audit["unsafe_excluded"]) == (983,981,45809,25533,0)
assert audit["permitted_axiom_union"] == ["propext", "Classical.choice", "Quot.sound"]
q_dir = control / "provenance/chapter02-complete-receiving-full-attempt1-20261104"
q_run = json.loads((q_dir / "result.json").read_text())
q_owned = json.loads((q_dir / "owned-terminal.json").read_text())
q_closed = json.loads((q_dir / "closed-evidence-reconciliation.json").read_text())
q_audit = json.loads((q_dir / "audit-and-build-summary.json").read_text())
q_verification = json.loads((q_dir / "verification.json").read_text())
assert q_owned["actual_exit"] == q_run["exit_code"] == 0
assert q_run["candidate"] == q_run["final_head"] == q_owned["candidate"] == candidate
assert not q_run["final_status"] and not q_run["progress_bookkeeping_errors"]
assert q_run["state"] == "passed" and q_closed["complete_log_closed"]
assert hashlib.sha256((q_dir / "full.log").read_bytes()).hexdigest() == q_run["log_sha256"] == q_closed["outer_sha256"]
assert hashlib.sha256((q_dir / "verification.json").read_bytes()).hexdigest() == q_run["verification_record_sha256"]
assert q_verification["candidate"] == candidate and q_verification["result"] == "passed" and q_verification["mode"] == "incremental"
assert (q_audit["checked_modules"], q_audit["audit_module_rows"], q_audit["kernel_safe_declarations"], q_audit["theorem_declarations"], q_audit["unsafe_excluded"]) == (1029,1027,47797,27214,0)
assert q_audit["permitted_axiom_union"] == ["propext", "Classical.choice", "Quot.sound"]
observation_dir = control / "provenance/chapter02-complete-receiving-input-observations-20261104-attempt1"
pre_run = json.loads((observation_dir / "pre-observation-execution.json").read_text())
failed_comparison = json.loads((observation_dir / "preliminary-comparison-execution.json").read_text())
assert pre_run["actual_exit"] == 0 and failed_comparison["actual_exit"] == 1
assert hashlib.sha256((observation_dir / "pre-inputs.json").read_bytes()).hexdigest() == pre_run["product"]["sha256"]
assert not (observation_dir / "preliminary-comparison.json").exists()
comparison2 = json.loads((observation_dir / "comparison-attempt2-execution.json").read_text())
assert comparison2["actual_exit"] == 0
assert hashlib.sha256((observation_dir / "preliminary-comparison-attempt2.json").read_bytes()).hexdigest() == comparison2["product"]["sha256"]
cleanup_dir = control / "provenance/chapter02-generated-setup-retirement-20261104"
cleanup_owned = json.loads((cleanup_dir / "owned-terminal.json").read_text())
cleanup_persistence = json.loads((cleanup_dir / "separate-persistence.json").read_text())
assert cleanup_owned["actual_exit"] == 0 and cleanup_persistence["all_target_payloads_zero_bytes_zero_blocks"]
assert cleanup_persistence["target_count"] == 103 and cleanup_persistence["preserved_non_target_count"] == 8121
assert cleanup_persistence["refs_source_dependencies_verification_and_saved_receiver_evidence_unchanged"]

# Retain the exact format-2 creator/restorer and complete unchanged native kit.
pinned_controls = {
    "checkpoint_compact.py": "5e72098a4b07a80c6861cdaf14f4d2234e33cd7b6a0a79170bae762599cbe078",
    "restore_compact.py": "23cdb74849a049df746c9f03af0e90ab261fd4fdc97bf2ea8f8088ffe9159376",
    "ENVIRONMENT.md": "62b3dfaa4ce57a0833c7132c991c51053e444b7a9d97a18db826dd2bd557f2b1",
    "tooling/unified-native-kit-4.35.0/SHA256SUMS": "72ba31d697b09e71cd21edbf6a46340f1fef6380585df86eb0320e1b05b737b6",
    "tooling/unified-native-kit-4.35.0/pins.json": "84f0fb3fc2b392d0249ca078dfc0beb0896dd3764af93acfe25eeda9d0e41bd4",
}
for relative, digest in pinned_controls.items():
    assert held[relative]["sha256"] == actual["fdsa-control/" + relative]["sha256"] == digest
kit_root = "tooling/unified-native-kit-4.35.0/"
kit_entries = (control / (kit_root + "SHA256SUMS")).read_text().splitlines()
assert len(kit_entries) == 298
for entry in kit_entries:
    digest, relative = entry.split("  ", 1)
    p = PurePosixPath(relative)
    assert not p.is_absolute() and ".." not in p.parts
    assert held[kit_root + relative]["sha256"] == actual["fdsa-control/" + kit_root + relative]["sha256"] == digest
assert module.ASSET["size_bytes"] == 67920919
assert module.ASSET["sha256"] == "8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63"
assert module.ASSET["git_blob"] == "e887c040b8c9902c6d9d38672ca54dd84937959d"

def captured(row):
    """Require an actual control file, its held identity, and its archived payload."""
    p = Path(row["path"])
    if p.is_absolute():
        relative = str(p.relative_to(control))
    else:
        relative = str(p)
    safe = PurePosixPath(relative)
    assert not safe.is_absolute() and ".." not in safe.parts
    identity = {"bytes": row["bytes"], "sha256": row["sha256"]}
    assert type(identity["bytes"]) is int and identity["bytes"] > 0
    assert isinstance(identity["sha256"], str) and len(identity["sha256"]) == 64
    assert held[relative] == actual["fdsa-control/" + relative] == identity, relative
    return control / relative

def recorded(relative):
    identity = held[relative]
    captured({"path": relative, **identity})
    return json.loads((control / relative).read_text())

# Archive preservation of the eleven actual serial runs, not a new type comparison.
programs = recorded("provenance/chapter02-receiving-targeted-statements1297-prepared-20261104/manifest.json")
coord = "provenance/chapter02-receiving-targeted-execution-coordinator-20261104/"
series = recorded(coord + "execution-result.json")
series_owned = recorded(coord + "owned-terminal.json")
assert series["candidate"] == series_owned["candidate"] == Q
assert series["status"] == "all-eleven-closed-zero" and series_owned["actual_exit"] == 0
assert series_owned["state"].startswith("CLOSED") and series["all_programs_bound_unchanged"]
assert len(series["completed_profiles"]) == len(programs["profiles"]) == 11
native_body_bytes = 0
for number, (row, profile) in enumerate(zip(series["completed_profiles"], programs["profiles"]), 1):
    assert row["profile_number"] == profile["number"] == number
    assert row["label"] == profile["label"] and row["actual_exit"] == 0
    run_dir = control / "provenance" / profile["receiving_run_name"]
    assert Path(row["directory"]) == run_dir
    relative = str(run_dir.relative_to(control)) + "/"
    result_row = recorded(relative + "result.json")
    request_row = recorded(relative + "request.json")
    owned_row = recorded(relative + "owned-subprocess-terminal.json")
    closure = json.loads(captured(row["closed_evidence"]).read_text())
    native_result = recorded(relative + "native-records/result.json")
    recorded(relative + "native-records/start.json")
    assert result_row["exit_code"] == owned_row["actual_exit"] == native_result["exit_code"] == 0
    assert result_row["state"] == "passed" and native_result["passed"]
    assert result_row["candidate"] == result_row["final_head"] == request_row["candidate"] == closure["candidate"] == Q
    assert not result_row["final_status"] and not result_row["progress_bookkeeping_errors"]
    assert closure["complete_closed_log"] and closure["terminal"] == owned_row
    assert closure["profile_number"] == number and closure["label"] == profile["label"]
    assert row["program"] == profile["program"] == closure["program_before"] == closure["program_after"]
    captured(profile["program"])
    assert owned_row["argv"] == profile["receiving_outer_argv"]
    argv = profile["receiving_outer_argv"]
    assert request_row["command"] == result_row["command"] == argv[argv.index("--") + 1:]
    assert native_result["command"] == ["lake", "env", "lean", profile["program"]["path"]]
    assert str(native_result["lean_threads"]) == "1" and native_result["cwd"] == str(base / "conaled-ch01-review")
    native_records = {Path(item["path"]).name: item for item in closure["native_records"]}
    assert len(closure["native_records"]) == len(native_records) == 3
    assert set(native_records) == {"start.json", "result.json", "output.log"}
    for leaf, item in native_records.items():
        assert captured(item) == run_dir / "native-records" / leaf
    assert all(row["native_output"][k] == native_records["output.log"][k] for k in ("path", "bytes", "sha256"))
    captured(row["native_output"])
    native_body_bytes += row["native_output"]["bytes"]
    for key in ("outer_log", "outer_prefix", "outer_suffix", "inherited_full_verification"):
        captured(closure[key])
    assert closure["outer_log"]["sha256"] == result_row["log_sha256"]
    assert closure["outer_log"]["bytes"] == result_row["log_size_bytes"]
    assert closure["inherited_full_verification"]["sha256"] == result_row["verification_record_sha256"] == q_run["verification_record_sha256"]
    assert closure["inherited_verification_is_not_a_new_full_check"]
assert native_body_bytes == 1081225
post_series = recorded(coord + "post-sequence-result.json")
post_owned = recorded(coord + "post-owned-terminal.json")
post_run = recorded(coord + "post-observation-execution.json")
stable_run = recorded(coord + "stable-comparison-execution.json")
assert post_series["actual_exit"] == post_owned["actual_exit"] == post_run["actual_exit"] == stable_run["actual_exit"] == 0
assert post_series["candidate"] == post_owned["candidate"] == Q
assert post_series["actual_post_stable"] and post_owned["identities_exactly_equal"]
assert post_owned["state"].startswith("CLOSED") and post_owned["carrier_never_executed_by_Lean"]
assert post_series["post"] == post_owned["post"] == post_run["product"]
assert post_series["comparison"] == post_owned["comparison"] == stable_run["product"]
captured(post_series["post"])
stable = json.loads(captured(post_series["comparison"]).read_text())
assert stable["receiver"] == Q and stable["receiver_observation_checks"]["pre_post_identity_equal"]
assert not stable["receiver_observation_checks"]["identity_differences"]
for run_record in (post_run, stable_run):
    captured(run_record["log"])

# These records must be real and held. No missing final path or hash is inferred.
roles = {
    "acceptance", "root_gate", "fast_forward_preflight", "fast_forward_result", "coverage",
    "standards_review", "standards_completion", "spec_review", "spec_completion",
    "immediate_result", "immediate_closed_evidence", "immediate_owned_terminal",
    "immediate_verification", "immediate_full_log",
}
assert set(bindings["files"]) == roles
bound_paths = {role: captured(row) for role, row in bindings["files"].items()}
assert bound_paths["acceptance"] == control / "provenance/chapter02-acceptance-20261104/acceptance.json"
for role, filename in (("root_gate", "root-gate-reconciliation.json"),
                       ("fast_forward_preflight", "prepared-fast-forward-preflight.json"),
                       ("fast_forward_result", "fast-forward-result.json"), ("coverage", "coverage.md")):
    assert bound_paths[role] == control / "provenance/chapter02-acceptance-20261104" / filename
final_acceptance = json.loads(bound_paths["acceptance"].read_text())
assert final_acceptance["accepted_commit"] == Q and final_acceptance["accepted_tree"] == Q_TREE
assert final_acceptance["previous_accepted_commit"] == L and final_acceptance["branch"] == "work/fdsa-book"
for axis, prefix in (("Standards", "standards"), ("Spec", "spec")):
    final_axis = final_acceptance["independent_axes"][axis]
    assert final_axis["outcome"] in ("Passed", "PASS") and final_axis["unresolved"] == 0
    assert captured(final_axis["report"]) == bound_paths[prefix + "_review"]
    assert captured(final_axis["completion"]) == bound_paths[prefix + "_completion"]
assert final_acceptance["root_gate"]["actual_exit"] == 0
assert captured(final_acceptance["root_gate"]["record"]) == bound_paths["root_gate"]
assert final_acceptance["immediate_verification"]["actual_exit"] == final_acceptance["fast_forward"]["actual_exit"] == 0
assert captured(final_acceptance["immediate_verification"]["result"]) == bound_paths["immediate_result"]
assert captured(final_acceptance["immediate_verification"]["closed_evidence"]) == bound_paths["immediate_closed_evidence"]
assert captured(final_acceptance["fast_forward"]["record"]) == bound_paths["fast_forward_result"]
immediate = json.loads(bound_paths["immediate_result"].read_text())
immediate_owned = json.loads(bound_paths["immediate_owned_terminal"].read_text())
immediate_closed = json.loads(bound_paths["immediate_closed_evidence"].read_text())
assert immediate["exit_code"] == immediate_owned["actual_exit"] == 0
assert immediate["candidate"] == immediate["final_head"] == immediate_owned["candidate"] == immediate_closed["candidate"] == Q
assert immediate["state"] == "passed" and not immediate["final_status"] and not immediate["progress_bookkeeping_errors"]
assert immediate["command"][-3:] == ["./check.sh", "--verify-candidate", "HEAD"]
assert immediate_closed["complete_log_closed"] and immediate_owned["state"].startswith("CLOSED")
assert bindings["files"]["immediate_full_log"]["sha256"] == immediate["log_sha256"] == immediate_closed["outer_sha256"]
assert bindings["files"]["immediate_full_log"]["bytes"] == immediate["log_size_bytes"]
assert bindings["files"]["immediate_verification"]["sha256"] == immediate["verification_record_sha256"] == immediate_closed["verification_sha256"] == q_run["verification_record_sha256"]
ff = json.loads(bound_paths["fast_forward_result"].read_text())
ff_pre = json.loads(bound_paths["fast_forward_preflight"].read_text())
assert ff["exit_code"] == 0 and ff["accepted_before"] == ff_pre["accepted_before"] == L
assert ff["approved_candidate"] == ff["accepted_after"] == ff_pre["candidate"] == Q
assert ff["accepted_tree"] == Q_TREE and ff["qualified_worktree_still_clean"] and ff["source_and_ref_postchecks_passed"]
assert ff["unrelated_baseline_bytes_preserved"] and ff_pre["accepted_tracked_and_index_clean"]
assert ff["command"][-3:] == ["merge", "--ff-only", Q]
assert ff["accepted_status_preserved"].strip() == module.git(repo, "status", "--porcelain=v1", "--untracked-files=all").strip()
# A recorded unrelated untracked baseline is preserved, not treated as dirty tracked source.
assert len(ff_pre["refs_before"]) == len(ff["refs_after"]) == 67
assert ff["refs_after"] == refs
before_refs = {row["ref"]: row for row in ff_pre["refs_before"]}
after_refs = {row["ref"]: row for row in ff["refs_after"]}
assert set(before_refs) == set(after_refs)
assert [key for key in before_refs if before_refs[key] != after_refs[key]] == ["refs/heads/work/fdsa-book"]
assert before_refs["refs/heads/work/fdsa-book"]["oid"] == L
assert after_refs["refs/heads/work/fdsa-book"]["oid"] == Q
assert datetime.fromisoformat(immediate["completed_utc"]) <= datetime.fromisoformat(ff["started_utc"])
# Final bindings must themselves be inside the same held control snapshot.
captured({"path": str((prep / "final-bindings.json").relative_to(control)),
          **held[str((prep / "final-bindings.json").relative_to(control))]})

result = {
    "verified_utc": datetime.now(timezone.utc).isoformat(), "file": str(archive),
    "bytes": archive.stat().st_size, "sha256": outer_sha,
    "actual_creation": creation, "payload_hashes_verified": len(expected),
    "refs_verified": len(refs), "worktree_states_verified": len(live),
    "held_control_hashes_verified": len(held), "accepted_head": accepted,
    "current_candidate": candidate, "format2_restorer_unchanged": True,
    "accepted_Tail_full_and_final_acceptance_preserved": True,
    "C2_original_R_scope": "81 paths / 112 obligations / ten shared scopes / 1763 public names",
    "C2_ordinary_L_Z_merge_and_six_conflict_stages_preserved": True,
    "C2_both_complete_source_continuations_preserved": True,
    "C2_complete_statement_and_resource_preparations_preserved": True,
    "C2_full_check_and_audit_passed": True,
    "C2_full_audit_counts": [1029,1027,47797,27214,0],
    "C2_first_pre_observation_success_and_comparison_failure_preserved": True,
    "C2_corrected_comparison_closed0_preserved": True,
    "Q_setup_only_retirement_and_separate_persistence_preserved": True,
    "C2_all11_closed_receiving_runs_and_native_bodies_preserved": True,
    "C2_native_body_bytes": native_body_bytes,
    "C2_actual_stable_postcomparison_preserved": True,
    "C2_actual_final_reviews_immediate_and_FF_captured": True,
    "C2_accepted_and_integrated_locally": True,
    "C2_final_bound_file_roles": sorted(roles),
    "complete_native_kit_manifest_entries": len(kit_entries),
    "no_new_type_comparison_or_compiler_execution": True,
    "all_original_failures_and_later_drafts_retained": True,
}
(prep / "integrity.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

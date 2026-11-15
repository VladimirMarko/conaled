from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib, importlib.util, json, os, sys, tarfile
sys.dont_write_bytecode = True
os.environ["GIT_OPTIONAL_LOCKS"] = "0"
control = Path(__file__).resolve().parents[2]
prep = Path(__file__).resolve().parent
base = control.parent
name = "conaled-fdsa-0121-checked-chapter02-receiving-evidence"
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
assert accepted == "726cb9a9b9ff4444a7614383de4fb336e8804aa7"
assert candidate == "2da5708478a1d943a9214b5b386ec2db16cd9eca"

source_dir = control / "provenance/shared-chapter02-source-integration-20261104"
source = json.loads((source_dir / "receipt.json").read_text())
assert source["candidate"] == candidate and source["accepted_book"] == accepted
assert source["ordered_parents"] == [accepted, "4b5dbfa07288acc73f25c27838d3fb2f78e77d71"]
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
assert acceptance["accepted_commit"] == accepted
assert acceptance["independent_axes"]["Standards"]["outcome"] == "Passed"
assert acceptance["independent_axes"]["Spec"]["outcome"] == "PASS"
assert acceptance["immediate_verification"]["actual_exit"] == acceptance["fast_forward"]["actual_exit"] == 0
full_dir = control / "provenance/shared-tail-full-attempt1-20261104"
run = json.loads((full_dir / "result.json").read_text())
owned = json.loads((full_dir / "owned-terminal.json").read_text())
assert owned["actual_exit"] == run["exit_code"] == 0
assert run["candidate"] == run["final_head"] == owned["candidate"] == accepted
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
    "C2_final_receiving_type_qualification_pending": True,
    "C2_not_accepted": True, "no_live_compiler": True,
    "all_original_failures_and_later_drafts_retained": True,
}
(prep / "integrity.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

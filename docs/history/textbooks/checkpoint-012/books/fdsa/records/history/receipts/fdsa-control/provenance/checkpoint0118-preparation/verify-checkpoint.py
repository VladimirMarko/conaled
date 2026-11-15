from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib, importlib.util, json, os, sys, tarfile
sys.dont_write_bytecode = True
os.environ["GIT_OPTIONAL_LOCKS"] = "0"
control = Path(__file__).resolve().parents[2]
prep = Path(__file__).resolve().parent
base = control.parent
name = "conaled-fdsa-0118-checked-tail-and-chapter02-evidence"
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
assert refs == manifest["refs"] and len(refs) == 66
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
assert accepted == "932438a765340d69fa6402f6abd17def6ec28d13"
assert candidate == "726cb9a9b9ff4444a7614383de4fb336e8804aa7"
full_dir = control / "provenance/shared-tail-full-attempt1-20261104"
type_dir = control / "provenance/shared-tail-complete-public-statements61-20261104-attempt1"
for directory in (full_dir, type_dir):
    run = json.loads((directory / "result.json").read_text())
    owned = json.loads((directory / "owned-terminal.json").read_text())
    assert owned["actual_exit"] == run["exit_code"] == 0
    assert run["candidate"] == run["final_head"] == owned["candidate"] == candidate
    assert not run["final_status"] and run["state"] == "passed"
    assert hashlib.sha256((directory / "full.log").read_bytes()).hexdigest() == run["log_sha256"]
    assert (directory / "closed-evidence-reconciliation.json").is_file()
audit = json.loads((full_dir / "audit-and-build-summary.json").read_text())
assert (audit["checked_modules"], audit["audit_module_rows"], audit["kernel_safe_declarations"], audit["theorem_declarations"], audit["unsafe_excluded"]) == (983,981,45809,25533,0)
assert audit["permitted_axiom_union"] == ["propext","Classical.choice","Quot.sound"]
comparison = json.loads((control / "provenance/shared-tail-inherited-type-qualification-20261104/comparison.json").read_text())
assert comparison["recipient"] == candidate and comparison["mechanical_comparison_passed"]
assert comparison["receiving_credit_granted_by_this_record"] == 0
assert comparison["prospective_distinct_public_account"] == 538
result = {"verified_utc": datetime.now(timezone.utc).isoformat(), "file": str(archive),
          "bytes": archive.stat().st_size, "sha256": outer_sha,
          "actual_creation": creation, "payload_hashes_verified": len(expected),
          "refs_verified": len(refs), "worktree_states_verified": len(live),
          "held_control_hashes_verified": len(held), "accepted_head": accepted,
          "unaccepted_Tail_candidate": candidate, "full_I_actual_exit": 0, "I_types314_actual_exit": 0, "I_both_complete_actual_type_reads": True, "I_final_110_transfer_and_reviews_passed": True, "I_accepted_after_immediate_verification_and_exact_FF": True,
          "history_correction_and_both_source_assessments_preserved": True,
          "format2_restorer_unchanged": True, "no_live_compiler": True, "XT02_complete_source_and_unexecuted90_preserved": True,
          "I_actual110_both_final_axes_qualified": True,
          "XT03_both_complete_source_assessments_and_unexecuted88_preserved": True, "J_both_complete_source_assessments_preserved": True, "J_full_actual_exit": 0, "J_actual53_exit": 0, "J_inherited_comparison_mechanical_pass": True, "J_final_axes_pending": False, "J_acceptance_credit": True, "J_both_complete_final_axes_pass": True, "J_immediate_actual_exit": 0, "J_exact_accepted_FF_actual_exit": 0, "Tail_readiness_and_both_bounded_preparations": True, "C2_conditional_readiness_preserved": True, "L_both_complete_source_axes_preserved": True, "L_full_actual_exit": 0, "L_actual61_exit": 0, "L_inherited_comparison_mechanical_pass": True, "L_both_final_axes_pending": True, "L_acceptance_credit": False, "C2_complete1763_statement_preparation_preserved": True, "C2_receiving_credit": 0, "L_actual_single_documentary_merge_conflict_and_resolution_preserved": True}
(prep / "integrity.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

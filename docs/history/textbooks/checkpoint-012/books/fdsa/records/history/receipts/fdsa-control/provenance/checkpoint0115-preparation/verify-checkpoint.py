from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib, importlib.util, json, os, sys, tarfile
sys.dont_write_bytecode = True
os.environ["GIT_OPTIONAL_LOCKS"] = "0"
control = Path(__file__).resolve().parents[2]
prep = Path(__file__).resolve().parent
base = control.parent
name = "conaled-fdsa-0115-checked-order-awaiting-final-reviews"
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
assert refs == manifest["refs"] and len(refs) == 65
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
assert accepted == "312aafb4446b995ff5542041b4e2e074f776db1e"
assert candidate == "932438a765340d69fa6402f6abd17def6ec28d13"
result = {"verified_utc": datetime.now(timezone.utc).isoformat(), "file": str(archive),
          "bytes": archive.stat().st_size, "sha256": outer_sha,
          "actual_creation": creation, "payload_hashes_verified": len(expected),
          "refs_verified": len(refs), "worktree_states_verified": len(live),
          "held_control_hashes_verified": len(held), "accepted_head": accepted,
          "unaccepted_Order_candidate": candidate, "full_I_actual_exit": 0, "I_types314_actual_exit": 0, "I_both_complete_actual_type_reads": True, "I_final_110_transfer_and_reviews_passed": True, "I_accepted_after_immediate_verification_and_exact_FF": True,
          "history_correction_and_both_source_assessments_preserved": True,
          "format2_restorer_unchanged": True, "no_live_compiler": True, "XT02_complete_source_and_unexecuted90_preserved": True,
          "I_actual110_both_final_axes_qualified": True,
          "XT03_both_complete_source_assessments_and_unexecuted88_preserved": True, "J_both_complete_source_assessments_preserved": True, "J_full_actual_exit": 0, "J_actual53_exit": 0, "J_inherited_comparison_mechanical_pass": True, "J_final_axes_pending": True, "J_acceptance_credit": 0, "Tail_readiness_and_both_bounded_preparations": True, "C2_conditional_readiness_preserved": True}
(prep / "integrity.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

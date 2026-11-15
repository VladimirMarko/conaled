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
name = "conaled-fdsa-0123-checked-selection-foundations"
accepted = "2da5708478a1d943a9214b5b386ec2db16cd9eca"
accepted_tree = "fe0bd9f17a5e1a09797be55fd79491e8c363cbd0"


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
assert actual["fdsa-control/provenance/checkpoint0123-preparation/capture.json"] == identity(prep / "capture.json")

spec = importlib.util.spec_from_file_location("compact_reader", control / "checkpoint_compact.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
repo = base / "conaled"
refs = [{"oid": p[0], "ref": p[1], "symref": p[2]} for p in
        (line.split(" ", 2) for line in module.git(repo, "for-each-ref",
         "--format=%(objectname) %(refname) %(symref)").splitlines())]
assert refs == manifest["refs"] == capture["refs"]
current_refs = {row["ref"]: row for row in refs}
previous_manifest = read(prep / "previous-manifest-0122.json")
assert previous_manifest["checkpoint"] == "conaled-fdsa-0122-accepted-chapter02"
assert len(previous_manifest["refs"]) == 67
for row in previous_manifest["refs"]:
    assert current_refs[row["ref"]] == row, row["ref"]
live = module.worktrees(repo)
assert live == capture["worktrees"]
assert len(live) == len(manifest["worktrees"]) == 15
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
previous_controls = read(control / "provenance/checkpoint0122-preparation/capture-control-identities.json")
allowed = set(capture["declared_prior_control_updates"])
assert allowed <= {"CURRENT.md", "STATUS.md", "ENVIRONMENT.md", "checkpoints.json",
                   "tickets/FDSA-002.md", "tickets/FDSA-003.md", "tickets/INDEX.md",
                   "reviews/chapter02-round1.md", "reviews/affine-recurrence-round1.md"}
changed = []
for relative, old in previous_controls.items():
    assert relative in capture["held_control"], relative
    if capture["held_control"][relative] != old:
        assert relative in allowed, relative
        changed.append(relative)
assert sorted(changed) == sorted(capture["actual_prior_control_updates"])

acceptance = read(control / "provenance/chapter02-acceptance-20261104/acceptance.json")
assert acceptance["accepted_commit"] == accepted and acceptance["accepted_tree"] == accepted_tree
assert acceptance["independent_axes"]["Standards"]["outcome"] == "Passed"
assert acceptance["independent_axes"]["Spec"]["outcome"] == "PASS"
for axis in acceptance["independent_axes"].values():
    assert axis["unresolved"] == 0 and axis["full_saved_readback_and_hold"]
assert acceptance["immediate_verification"]["actual_exit"] == acceptance["fast_forward"]["actual_exit"] == 0
durability = read(control / "provenance/chapter02-acceptance-20261104/durability.json")
assert durability["status"] == "succeeded" and durability["C2_acceptance_durability_complete"]
assert durability["library_file_id"] == "libfile_bd68f45a79dc8191b9bba484b30eb4a6"

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
kit = control / "tooling/unified-native-kit-4.35.0"
kit_rows = (kit / "SHA256SUMS").read_text().splitlines()
assert len(kit_rows) == 298
for line in kit_rows:
    digest, relative = line.split("  ", 1)
    assert identity(kit / relative)["sha256"] == digest, relative
    assert actual["fdsa-control/tooling/unified-native-kit-4.35.0/" + relative]["sha256"] == digest

record = {"verified_utc": datetime.now(timezone.utc).isoformat(), "file": str(archive),
          **outer, "payload_hashes_verified": len(expected), "refs_verified": len(refs),
          "prior67_refs_preserved": True, "worktrees_verified": len(live),
          "held_control_hashes_verified": len(capture["held_control"]),
          "prior_control_changes_explicit": sorted(changed), "accepted_head": accepted,
          "qualified_candidate": capture["qualified_candidate"],
          "chapter02_acceptance_preserved": True, "chapter03_obligations": 83,
          "closed_development_runs_verified": len(capture["closed_development_runs"]),
          "complete_native_kit_manifest_entries": 298,
          "XR_and_chapter03_acceptance_claimed": False,
          "no_compiler_restore_fsck_or_acceptance_execution": True,
          "format2_creator_and_restorer_preserved": True}
with (prep / "integrity.json").open("x") as stream:
    json.dump(record, stream, indent=2)
    stream.write("\n")
print(json.dumps(record, indent=2))

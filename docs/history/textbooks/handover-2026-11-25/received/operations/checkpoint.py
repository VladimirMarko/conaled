#!/usr/bin/env python3
"""Create, inspect and recover one complete source-continuation checkpoint.

Standard library plus ordinary Git only. No Lean execution, toolchain changes,
Git publication, source acceptance or upload is performed by this program.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
from typing import Any


SCHEMA = "conaled-single-checkpoint-v1"
CAP = 536_870_912
SOURCE_MODES = {"100644", "100755"}
# Frozen research artifacts may intentionally be read-only. Preserve their exact
# mode; this does not add a Git source mode or permit special permission bits.
MODES = SOURCE_MODES | {"100444"}
REQUIRED_DOCUMENTS = {"requirements", "authored_commits", "continuation", "status"}
INHERITED_ROOTS = {
    "conaled-textbooks-136-progress-2026-11-23",
    "conaled-textbooks-136-completion-2026-11-23",
    "conaled-textbooks-136-followup-notes-2026-11-23",
}
EXCLUDED_COMPONENTS = {".git", ".lake", "__pycache__", "node_modules"}
EXCLUDED_SUFFIXES = (
    ".tar", ".xz", ".zip", ".tgz", ".gz", ".bz2", ".zst", ".7z",
    ".rar", ".ltar", ".bundle", ".olean", ".ilean", ".pyc", ".so", ".o", ".a",
)
COMPACT_MODE = "curated-v2"
RETENTION_SCHEMA = "conaled-checkpoint-retention-v1"
PREDECESSOR_INVENTORY = "retention/predecessor-INVENTORY.json"


class CheckpointError(Exception):
    """A concrete invariant or input failed; no acceptance is implied."""


def need(condition: bool, message: str) -> None:
    if not condition:
        raise CheckpointError(message)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def safe_relative(name: str) -> Path:
    need(isinstance(name, str) and bool(name), "Expected a nonempty relative path")
    need("\\" not in name and not any(ord(c) < 32 for c in name),
         "Unsupported path characters: " + repr(name))
    p = PurePosixPath(name)
    need(not p.is_absolute() and p.as_posix() == name and
         all(part not in ("", ".", "..", ".git") for part in name.split("/")),
         "Unsafe relative path: " + repr(name))
    return Path(*p.parts)


def no_symlink_parents(path: Path) -> None:
    for part in (path, *path.parents):
        need(not part.is_symlink(), "Symlink path component: " + str(part))


def absolute_path(value: str, *, directory: bool = False) -> Path:
    path = Path(value).absolute()
    no_symlink_parents(path)
    need(path.is_dir() if directory else path.is_file(), "Missing input: " + str(path))
    return path


def new_output(value: str) -> Path:
    path = Path(value).absolute()
    no_symlink_parents(path)
    need(path.parent.is_dir() and not path.exists(), "New output with existing parent required: " + str(path))
    return path


def descriptor(raw: bytes, mode: str = "100644") -> dict[str, Any]:
    need(mode in MODES, "Unsupported regular-file mode: " + mode)
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(), "mode": mode}


def file_descriptor(path: Path) -> dict[str, Any]:
    no_symlink_parents(path)
    st = path.lstat()
    need(stat.S_ISREG(st.st_mode), "Not an own regular file: " + str(path))
    mode = format(st.st_mode, "o")
    need(mode in MODES, "Unsupported file mode: " + str(path))
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
            size += len(chunk)
    after = path.lstat()
    need((st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_mode) ==
         (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_mode)
         and size == st.st_size, "Input changed while reading: " + str(path))
    return {"bytes": size, "sha256": digest.hexdigest(), "mode": mode}


def scan_directory(root: Path, *, packaging: bool = False) -> dict[str, dict[str, Any]]:
    no_symlink_parents(root)
    need(root.is_dir(), "Not a directory: " + str(root))
    members: dict[str, dict[str, Any]] = {}
    for path in sorted(root.rglob("*")):
        need(not path.is_symlink(), "Symlink in input tree: " + str(path))
        rel = path.relative_to(root).as_posix()
        safe_relative(rel)
        if packaging:
            need(not (set(path.relative_to(root).parts) & EXCLUDED_COMPONENTS),
                 "Tool/cache/output directory excluded from checkpoints: " + rel)
        if path.is_dir():
            continue
        if packaging:
            need(not rel.lower().endswith(EXCLUDED_SUFFIXES),
                 "Nested archive, installed tool or generated output excluded: " + rel)
        members[rel] = file_descriptor(path)
    return members


def load_json(path: Path) -> Any:
    return json.loads(path.read_bytes())


def verify_inventory(root: Path) -> dict[str, dict[str, Any]]:
    actual = scan_directory(root)
    need("INVENTORY.json" in actual, "Missing inventory in " + str(root))
    inventory = load_json(root / "INVENTORY.json")
    need(isinstance(inventory, dict) and isinstance(inventory.get("members"), dict),
         "Invalid inventory in " + str(root))
    expected = inventory["members"]
    need(set(actual) == set(expected) | {"INVENTORY.json"}, "Inventory member set differs: " + str(root))
    for name, desc in expected.items():
        safe_relative(name)
        need(actual[name] == desc, "Inventory bytes/hash/mode differ: " + name)
    return actual


def git(repo: Path | None, *args: str, input_bytes: bytes | None = None,
        allow_failure: bool = False) -> subprocess.CompletedProcess[bytes]:
    inherited = [key for key in os.environ if key.startswith("GIT_") and key != "GIT_PAGER"]
    need(not inherited, "Remove caller Git overrides before use: " + ", ".join(inherited))
    command = ["git", "-c", "core.hooksPath=/dev/null", "-c", "core.autocrlf=false"]
    if repo is not None:
        command += ["-C", str(repo)]
    result = subprocess.run(command + list(args), input=input_bytes,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if not allow_failure:
        need(result.returncode == 0, "Git failed (" + str(result.returncode) + "): " +
             " ".join(args) + "\n" + result.stderr.decode("utf-8", "replace"))
    return result


def git_text(repo: Path, *args: str) -> str:
    return git(repo, *args).stdout.decode("utf-8").strip()


def exact_commit(repo: Path, value: str) -> str:
    need(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None,
         "Use an explicit complete immutable commit SHA: " + repr(value))
    need(git_text(repo, "rev-parse", value + "^{commit}") == value, "Commit identity differs")
    return value


def ancestor(repo: Path, older: str, newer: str) -> None:
    result = git(repo, "merge-base", "--is-ancestor", older, newer, allow_failure=True)
    need(result.returncode == 0, "Required ancestry is missing: " + older + " -> " + newer)


def tree_entries(repo: Path, treeish: str) -> dict[str, dict[str, str]]:
    entries = {}
    for record in git(repo, "ls-tree", "-r", "-z", "--full-tree", treeish).stdout.split(b"\0"):
        if not record:
            continue
        header, raw_path = record.split(b"\t", 1)
        mode, kind, oid = header.decode("ascii").split()
        path = raw_path.decode("utf-8")
        safe_relative(path)
        need(mode in SOURCE_MODES and kind == "blob", "Unsupported source tree member: " + path)
        entries[path] = {"mode": mode, "git_blob": oid}
    return entries


@dataclass
class Payload:
    desc: dict[str, Any]
    path: Path | None = None
    raw: bytes | None = None

    def read(self) -> bytes:
        data = self.raw if self.raw is not None else self.path.read_bytes()  # type: ignore[union-attr]
        need(descriptor(data, self.desc["mode"]) == self.desc, "Payload changed: " + str(self.path))
        if self.path is not None:
            need(file_descriptor(self.path) == self.desc, "Payload mode changed: " + str(self.path))
        return data


def payload_key(desc: dict[str, Any]) -> tuple[str, int, str]:
    return desc["mode"], desc["bytes"], desc["sha256"]


def add_payload(payload: dict[str, Payload], name: str, item: Payload) -> None:
    safe_relative(name)
    need(name not in payload and name != "INVENTORY.json", "Duplicate payload name: " + name)
    payload[name] = item


def validate_url(url: str) -> None:
    need(isinstance(url, str) and re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\.git", url) is not None,
         "Expected a canonical public GitHub HTTPS .git repository URL")


def compact_json(raw: bytes) -> Any:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, "Duplicate compact JSON key: " + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def exact_descriptor(value: Any) -> None:
    need(isinstance(value, dict) and set(value) == {"bytes", "sha256", "mode"},
         "Expected exact bytes/sha256/mode descriptor")
    need(type(value["bytes"]) is int and value["bytes"] >= 0 and
         isinstance(value["sha256"], str) and re.fullmatch(r"[0-9a-f]{64}", value["sha256"]) is not None and
         value["mode"] in MODES, "Invalid compact file descriptor")


def reason_text(value: Any) -> None:
    need(isinstance(value, str) and bool(value.strip()), "A nonempty retention/selection reason is required")


def compact_member(name: str) -> None:
    path = safe_relative(name)
    need(not (set(path.parts) & EXCLUDED_COMPONENTS) and
         not name.lower().endswith(EXCLUDED_SUFFIXES + (".part", ".partial", ".crdownload", ".download")),
         "Excluded compact archive/cache/output member: " + name)


def expected_input(binding: Any) -> tuple[Path, dict[str, Any]]:
    need(isinstance(binding, dict) and set(binding) == {"path", "expected"},
         "Input binding needs exactly path and expected")
    path = absolute_path(binding["path"])
    exact_descriptor(binding["expected"])
    need(file_descriptor(path) == binding["expected"], "Expected input descriptor differs: " + str(path))
    return path, binding["expected"]


def prepare_compact(config: dict[str, Any], payload: dict[str, Payload]):
    """Verify the actual predecessor; select literal files, never directory trees."""
    predecessor = config["predecessor"]
    need(isinstance(predecessor, dict) and set(predecessor) == {"packet_name", "archive", "inventory"},
         "Bind the immediate predecessor packet, archive and inventory explicitly")
    archive, archive_desc = expected_input(predecessor["archive"])
    inventory_path, inventory_desc = expected_input(predecessor["inventory"])
    previous = verify_archive(archive, expected_sha256=archive_desc["sha256"], expected_bytes=archive_desc["bytes"])
    need(previous["packet_name"] == predecessor["packet_name"] != config["packet_name"],
         "Immediate predecessor packet identity differs or equals successor")
    need(previous["inventory_descriptor"] == inventory_desc, "Predecessor inventory descriptor differs from archive")
    with tarfile.open(archive, "r:xz") as tar:
        stream = tar.extractfile(predecessor["packet_name"] + "/INVENTORY.json")
        need(stream is not None and stream.read() == inventory_path.read_bytes(),
             "Supplied predecessor inventory bytes differ from actual archive")
    retention_path, retention_desc = expected_input(config["retention"])
    spec = compact_json(retention_path.read_bytes())
    need(isinstance(spec, dict) and set(spec) == {"schema", "dispositions", "historical_outcomes_member"}
         and spec["schema"] == 1, "Expected compact disposition input schema 1")
    files = config["files"]
    need(isinstance(files, dict), "Compact files must map destinations to exact carriers")
    inputs = [(archive, archive_desc), (inventory_path, inventory_desc), (retention_path, retention_desc)]
    selection = {}
    reserved = {"START_HERE.md", "STATE.json", "SOURCE_MANIFEST.json", "INVENTORY.json",
                "RETENTION.json", "RETENTION.md", "operations/checkpoint.py", "operations/checkpoint-README.md"}
    seen = {}
    for member, record in sorted(files.items()):
        compact_member(member)
        need(member not in reserved and not member.startswith(("retention/", "current/source/")),
             "Reserved generated compact route: " + member)
        need(isinstance(record, dict) and set(record) == {"path", "expected", "reason"},
             "Each selected file needs path, expected descriptor and reason")
        reason_text(record["reason"])
        path, desc = expected_input({"path": record["path"], "expected": record["expected"]})
        need(not (set(path.parts) & EXCLUDED_COMPONENTS) and
             not path.name.lower().endswith(EXCLUDED_SUFFIXES + (".part", ".partial", ".crdownload", ".download")),
             "Excluded compact carrier: " + str(path))
        key = payload_key(desc)
        need(key not in seen, "Duplicate selected bytes/mode; reuse one survivor route: " + member)
        seen[key] = member
        add_payload(payload, member, Payload(desc, path=path))
        selection[member] = {"descriptor": desc, "reason": record["reason"]}
        inputs.append((path, desc))
    add_payload(payload, PREDECESSOR_INVENTORY, Payload(inventory_desc, path=inventory_path))
    record = {"schema": RETENTION_SCHEMA,
              "predecessor": {"packet_name": predecessor["packet_name"], "archive_descriptor": archive_desc,
                              "inventory_member": PREDECESSOR_INVENTORY, "inventory_descriptor": inventory_desc,
                              "regular_member_count": previous["regular_member_count"],
                              "expanded_bytes": previous["total_regular_bytes_including_inventory"]},
              "selection": selection, "dispositions": spec["dispositions"],
              "historical_outcomes_member": spec["historical_outcomes_member"],
              "boundary": "The curator identifies the immediate predecessor and substantive survivors. Retired/updated bodies have no reconstruction contract. No acceptance is inferred."}
    return record, inputs, archive


def validate_retention(record: Any, members: dict[str, dict[str, Any]], read, previous_read=None) -> None:
    need(isinstance(record, dict) and record.get("schema") == RETENTION_SCHEMA, "Unsupported retention manifest")
    need(isinstance(record.get("selection"), dict) and isinstance(record.get("predecessor"), dict),
         "Invalid retention selection or predecessor object")
    previous = record["predecessor"]
    exact_descriptor(previous["archive_descriptor"])
    exact_descriptor(previous["inventory_descriptor"])
    need(previous["inventory_member"] == PREDECESSOR_INVENTORY and
         members.get(PREDECESSOR_INVENTORY) == previous["inventory_descriptor"],
         "Bound predecessor inventory identity differs")
    inv_raw = read(PREDECESSOR_INVENTORY)
    need(descriptor(inv_raw, previous["inventory_descriptor"]["mode"]) == previous["inventory_descriptor"],
         "Bound predecessor inventory bytes differ")
    inventory = compact_json(inv_raw)
    need(isinstance(inventory, dict) and isinstance(inventory.get("members"), dict) and
         "INVENTORY.json" not in inventory["members"], "Invalid predecessor member inventory")
    old_members = {**inventory["members"], "INVENTORY.json": previous["inventory_descriptor"]}
    need(previous["regular_member_count"] == len(old_members) and
         previous["expanded_bytes"] == sum(d["bytes"] for d in old_members.values()),
         "Predecessor member count or expanded bytes differ")
    dispositions = record["dispositions"]
    need(isinstance(dispositions, dict) and set(dispositions) == set(old_members),
         "Dispositions must cover every predecessor member exactly, including INVENTORY.json")
    for name, old_desc in sorted(old_members.items()):
        safe_relative(name)
        exact_descriptor(old_desc)
        entry = dispositions[name]
        required = {"previous_descriptor", "disposition", "reason", "survivor_member", "old_body_reconstructible"}
        need(isinstance(entry, dict) and set(entry) in (required, required | {"byte_offset"}),
             "Invalid disposition fields: " + name)
        need(entry["previous_descriptor"] == old_desc, "Previous member descriptor differs: " + name)
        reason_text(entry["reason"])
        kind = entry["disposition"]
        need(kind in {"retained", "duplicate", "updated", "embedded", "retired"}, "Unknown disposition: " + name)
        survivor = entry["survivor_member"]
        compact_member(survivor)
        need(survivor in members and survivor not in {"INVENTORY.json", "RETENTION.json"},
             "Missing or circular survivor member: " + name)
        reconstructible = kind in {"retained", "duplicate", "embedded"}
        need(type(entry["old_body_reconstructible"]) is bool and entry["old_body_reconstructible"] == reconstructible,
             "Disposition makes an invalid reconstruction claim: " + name)
        need(("byte_offset" in entry) == (kind == "embedded"), "Offset belongs only to embedded disposition: " + name)
        if name == "INVENTORY.json":
            need(kind in {"retained", "duplicate"} and survivor == PREDECESSOR_INVENTORY,
                 "Retain the exact predecessor inventory once at its bound route")
        if kind in {"retained", "duplicate"}:
            need(members[survivor] == old_desc, "Retained/duplicate bytes or mode differ: " + name)
            if previous_read is not None:
                need(read(survivor) == previous_read(name), "Retained/duplicate literal bytes differ: " + name)
        elif kind == "embedded":
            offset = entry["byte_offset"]
            need(type(offset) is int and offset >= 0, "Embedded offset must be a nonnegative integer: " + name)
            raw = read(survivor)
            embedded = raw[offset:offset + old_desc["bytes"]]
            need(offset + old_desc["bytes"] <= len(raw) and descriptor(embedded, old_desc["mode"]) == old_desc,
                 "Embedded predecessor bytes/offset differ: " + name)
            if previous_read is not None:
                need(embedded == previous_read(name), "Embedded literal bytes differ: " + name)
    for member, selected in record["selection"].items():
        compact_member(member)
        reason_text(selected["reason"])
        exact_descriptor(selected["descriptor"])
        need(members.get(member) == selected["descriptor"], "Selected successor descriptor differs: " + member)
    outcomes_member = record["historical_outcomes_member"]
    compact_member(outcomes_member)
    need(outcomes_member in members, "Missing durable historical outcomes member")
    outcomes = compact_json(read(outcomes_member))
    need(isinstance(outcomes, dict) and isinstance(outcomes.get("outcomes"), list) and bool(outcomes["outcomes"]),
         "Historical outcomes must be a nonempty curated ledger")
    reason_text(outcomes.get("coverage_statement"))
    ids = set()
    for outcome in outcomes["outcomes"]:
        need(isinstance(outcome, dict) and
             {"id", "outcome", "actual_exit_code", "terminal_observed", "candidate", "scope", "source_evidence",
              "reading_limits", "availability_limits"} <= set(outcome), "Incomplete historical outcome record")
        reason_text(outcome["id"])
        need(outcome["id"] not in ids, "Duplicate historical outcome id")
        ids.add(outcome["id"])
        status, code, terminal = outcome["outcome"], outcome["actual_exit_code"], outcome["terminal_observed"]
        need((status == "UNKNOWN" and code is None and terminal is False) or
             (status == "failed" and type(code) is int and code != 0 and terminal is True) or
             (status == "passed" and type(code) is int and code == 0 and terminal is True),
             "Inconsistent historical outcome/exit/terminal observation")
        need(isinstance(outcome["source_evidence"], list) and bool(outcome["source_evidence"]),
             "Historical outcome requires explicit evidence references")
        need(outcome["candidate"] is None or isinstance(outcome["candidate"], str),
             "Historical candidate must be an explicit identity/limitation string or null")
        for key in ("scope", "reading_limits", "availability_limits"):
            reason_text(outcome[key])


def compact_start_here(state: dict[str, Any], manifest: dict[str, Any], continuation: str) -> bytes:
    docs = state["documents"]
    return f"""# Start here: {state['packet_name']}

This is the one complete checkpoint for this cutoff. Recovery needs the declared
public Git history and this packet, not the predecessor archive or private donor
objects. Recovery tested, source accepted and saved/delivered are separate facts.

## Read in this order

1. [RETENTION.md](RETENTION.md): the durable compact-checkpoint policy.
2. [STATE.json](STATE.json), [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json), and
   [{docs['status']}]({docs['status']}).
3. [{state['retention']['historical_outcomes_member']}]({state['retention']['historical_outcomes_member']}):
   actual failures, UNKNOWNs and reading/availability limits; absence is not success.
4. [{docs['continuation']}]({docs['continuation']}), complete fixed requirements
   [{docs['requirements']}]({docs['requirements']}), and authored-commit inventory
   [{docs['authored_commits']}]({docs['authored_commits']}).
5. Current preparation, original independent review records, unresolved findings
   and useful research at the exact continuation paths below. In recovered source,
   read AGENTS.md and docs/textbooks/external-agent.md before continuing.

## Source and recovery

- Cutoff: `{state['created_utc']}`.
- Frozen candidate: `{manifest['candidate']}`; whole tree: `{manifest['source_tree']}`.
- Public prerequisite: `{manifest['public_base']}`; original specification base: `{manifest['original_base']}`.
- Entire source delta: {len(manifest['updates'])} updated/new owners and {len(manifest['deletions'])} deletions.

After safe extraction, from this root use a new destination and receipt:

```sh
python3 -B operations/checkpoint.py restore --packet . \\
  --destination /absolute/new/conaled --receipt /absolute/new-recovery-result.json
```

The unchanged restore/inspect gates check an independent ordinary public clone,
the complete delta, exact index tree, every tracked body and mode, source style,
owned Git storage and absence of unstaged/untracked/ignored files. They do not
compile Lean or confer source acceptance. See operations/checkpoint-README.md.
RETENTION.json binds the actual immediate predecessor inventory and accounts for
every member; retired/updated carriers have no old-body reconstruction contract.

Do not post local progress to issue558. Preserve the existing independent review
loop and actual unresolved findings. Make one complete archive per cutoff; later
results and the actual external save receipt belong in the next checkpoint.

## Current continuation instructions

{continuation.rstrip()}
""".encode("utf-8")


def start_here(state: dict[str, Any], manifest: dict[str, Any], continuation: str) -> bytes:
    if state.get("retention_mode") == COMPACT_MODE:
        return compact_start_here(state, manifest, continuation)
    docs = state["documents"]
    text = f"""# Start here: {state['packet_name']}

This is the one complete archive for this cutoff. No earlier checkpoint attachment
or private author Git object is required for source recovery. Public Git history,
the compiler, pinned dependencies and their caches are external prerequisites.
The nested history entrypoints describe earlier observations; this root state and
source manifest identify the current source.

## Current identities

- Cutoff: `{state['created_utc']}`.
- Current frozen author candidate: `{manifest['candidate']}`.
- Current complete source tree: `{manifest['source_tree']}`.
- Accepted public source prerequisite: `{manifest['public_base']}`.
- Original full-specification base: `{manifest['original_base']}`.
- Current source delta: {len(manifest['updates'])} updated/new owners and {len(manifest['deletions'])} deletions.

Recovery, mathematical acceptance and durable saving are separate observations.
This archive's construction establishes neither Lean acceptance nor independent
review approval. The current status document records actual validation limits.

## One recovery command

Extract the archive safely, enter this directory, then use a nonexistent output
directory and an external new receipt path:

```sh
python3 -B operations/checkpoint.py restore --packet . \\
  --destination /absolute/new/conaled \\
  --receipt /absolute/new-recovery-result.json
```

The command verifies the whole inventory, makes an ordinary non-shallow public
clone, checks the pinned public tree and ancestry, restores the complete declared
delta, and checks the exact staged tree, every tracked body/mode, source style,
own Git object storage, and absence of unstaged/untracked/ignored files. It does
not compile Lean, recreate the author's private candidate commit, or execute old
recorded commands. See `operations/checkpoint-README.md` for archive verification,
the optional independently held public-cache route, and standalone inspection.

## Read in this order

1. Root `STATE.json`, `SOURCE_MANIFEST.json`, and [{docs['status']}]({docs['status']}).
2. The current continuation instructions below and [{docs['continuation']}]({docs['continuation']}).
3. In the recovered repository: `AGENTS.md`, `docs/textbooks/external-agent.md`,
   `docs/textbooks/CTB.json`, `docs/textbooks/coverage.json`, and the inbox.
4. Complete fixed requirements: [{docs['requirements']}]({docs['requirements']});
   authored commit inventory: [{docs['authored_commits']}]({docs['authored_commits']}).
5. The maintained preparation paper, original Standards/Spec review records and
   unresolved findings, and current evidence/research at the paths below.

## Continuation boundaries

- Do not post local progress updates to GitHub issue #558. The user's
  2026-11-24 instruction supersedes the older conditional progress-posting policy.
- Preserve original independent Standards/Spec review roles, seven rounds and
  unresolved findings. Operational helpers do not supply either acceptance axis.
- Historical module5, whole115, whole128 and whole129-recovery terminals remain
  UNKNOWN. The inherited whole137 record has no terminal receipt; loss of its
  process/workspace leaves its terminal outcome UNKNOWN.
- Focused proof compilation, archive recovery, receiving acceptance and durable
  saving have separate meanings. Do not manufacture missing outcomes.
- Receiving master publication remains with the conaled integration agent.
  A saved continuation archive is not a remotely inspectable receiving handoff.
- Use exact native pins, normal resource settings and privately owned project
  outputs. Keep tools, caches and build outputs outside future checkpoints.
- Create one complete archive per next cutoff. Carry later results into that
  next archive; do not create a completion companion solely for a save receipt.

## Current continuation instructions

{continuation.rstrip()}
"""
    return text.encode("utf-8")


def build_plan(config_path: Path):
    config_desc = file_descriptor(config_path)
    config_raw = config_path.read_bytes()
    need(descriptor(config_raw, config_desc["mode"]) == config_desc, "Configuration changed while reading")
    config = json.loads(config_raw)
    need(isinstance(config, dict) and config.get("schema") in (1, 2), "Expected config schema 1 or 2")
    compact = config["schema"] == 2
    if compact:
        config = compact_json(config_raw)
    allowed = {"schema", "packet_name", "repo", "candidate", "public_base", "original_base",
               "repository_url", "documents", "created_utc"}
    allowed |= {"predecessor", "files", "retention"} if compact else {"history", "directories"}
    need(not (set(config) - allowed), "Unknown config keys: " + repr(sorted(set(config) - allowed)))
    name = config["packet_name"]
    need(re.fullmatch(r"conaled-textbooks-[A-Za-z0-9._-]+", name) is not None, "Invalid packet name")
    repo = absolute_path(config["repo"], directory=True)
    candidate = exact_commit(repo, config["candidate"])
    base = exact_commit(repo, config["public_base"])
    original = exact_commit(repo, config["original_base"])
    ancestor(repo, original, base)
    ancestor(repo, base, candidate)
    validate_url(config["repository_url"])
    need(git_text(repo, "rev-parse", "--is-shallow-repository") == "false", "Source repository is shallow")
    before, after = tree_entries(repo, base), tree_entries(repo, candidate)
    payload: dict[str, Payload] = {}
    history = []
    input_trees = []
    compact_inputs = []
    retention_record = None
    predecessor_archive = None
    if compact:
        retention_record, compact_inputs, predecessor_archive = prepare_compact(config, payload)
    else:
        raw_history = config["history"]
        need(isinstance(raw_history, list) and len(raw_history) == 3, "Supply all three inherited packet directories")
        history_paths = [absolute_path(p, directory=True) for p in raw_history]
        need({p.name for p in history_paths} == INHERITED_ROOTS, "Inherited packet set differs from the three supplied C136 packets")
        for root in sorted(history_paths):
            members = verify_inventory(root)
            # Enforce source-only content even when an inherited inventory is internally valid.
            need(scan_directory(root, packaging=True) == members, "Inherited tree changed")
            prefix = "history/" + root.name
            history.append({"root": prefix, "inventory": prefix + "/INVENTORY.json",
                            "inventory_descriptor": members["INVENTORY.json"]})
            input_trees.append((root, members))
            for rel, desc in members.items():
                add_payload(payload, prefix + "/" + rel, Payload(desc, path=root / rel))
    directories = config.get("directories", {})
    need(isinstance(directories, dict) and not (set(directories) - {"evidence", "research", "operations"}),
         "Directory categories must be evidence, research or operations")
    directory_routes = {}
    for category, groups in sorted(directories.items()):
        need(isinstance(groups, dict), "Each directory category must map names to paths")
        for label, raw_path in sorted(groups.items()):
            need(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", label) is not None, "Invalid directory label")
            root = absolute_path(raw_path, directory=True)
            members = scan_directory(root, packaging=True)
            need(bool(members), "Selected directory has no regular-file payload: " + str(root))
            input_trees.append((root, members))
            prefix = "current/" + category + "/" + label
            directory_routes[category + "/" + label] = prefix
            for rel, desc in members.items():
                add_payload(payload, prefix + "/" + rel, Payload(desc, path=root / rel))
    matching: dict[tuple[str, int, str], list[str]] = {}
    for rel, item in sorted(payload.items(), key=lambda pair: (not pair[0].startswith("history/"), pair[0])):
        matching.setdefault(payload_key(item.desc), []).append(rel)

    def reuse_or_add(raw: bytes, mode: str, proposed: str) -> str:
        desc = descriptor(raw, mode)
        for existing in matching.get(payload_key(desc), []):
            if payload[existing].read() == raw:
                return existing
        add_payload(payload, proposed, Payload(desc, raw=raw))
        matching.setdefault(payload_key(desc), []).append(proposed)
        return proposed

    updates = {}
    for owner, entry in sorted(after.items()):
        if before.get(owner) == entry:
            continue
        raw = git(repo, "cat-file", "blob", entry["git_blob"]).stdout
        route = reuse_or_add(raw, entry["mode"], "current/source/" + owner)
        updates[owner] = {"payload": route, **descriptor(raw, entry["mode"]),
                          "git_blob": entry["git_blob"]}
    deletions = sorted(set(before) - set(after))
    documents = config["documents"]
    need(isinstance(documents, dict) and set(documents) == REQUIRED_DOCUMENTS,
         "Provide exactly requirements, authored_commits, continuation and status documents")
    document_routes = {}
    document_inputs = [(config_path, config_desc)] + compact_inputs
    for key, raw_path in sorted(documents.items()):
        path = absolute_path(raw_path)
        desc = file_descriptor(path)
        raw = path.read_bytes()
        need(descriptor(raw, desc["mode"]) == desc, "Document changed during read")
        if key in ("status", "authored_commits"):
            need(isinstance(json.loads(raw), (dict, list)), "Expected JSON document: " + key)
        else:
            need(bool(raw.decode("utf-8").strip()), "Empty document: " + key)
        extension = ".json" if key in ("status", "authored_commits") else ".md"
        document_routes[key] = reuse_or_add(raw, desc["mode"], "current/control/" + key + extension)
        document_inputs.append((path, desc))
    manifest = {"schema": SCHEMA, "repository_url": config["repository_url"],
                "public_base": base, "prerequisite_tree": git_text(repo, "rev-parse", base + "^{tree}"),
                "original_base": original, "original_base_tree": git_text(repo, "rev-parse", original + "^{tree}"),
                "candidate": candidate, "source_tree": git_text(repo, "rev-parse", candidate + "^{tree}"),
                "updates": updates, "deletions": deletions,
                "snapshot_source": "Exact immutable Git commit blobs; the live index/worktree is not packaged implicitly",
                "private_author_git_objects_required_for_recovery": False}
    source_raw = json_bytes(manifest)
    add_payload(payload, "SOURCE_MANIFEST.json", Payload(descriptor(source_raw), raw=source_raw))
    state = {"schema": SCHEMA, "packet_name": name, "created_utc": config.get("created_utc") or utc_now(),
             "source_manifest": "SOURCE_MANIFEST.json", "source_manifest_descriptor": descriptor(source_raw),
             "current_source": {key: manifest[key] for key in
                                ("public_base", "prerequisite_tree", "original_base", "original_base_tree", "candidate", "source_tree")},
             "documents": document_routes, "directories": directory_routes, "history": history,
             "payload_limit_bytes_including_inventory": CAP,
             "source_accepted_by_packaging": False, "review_approved_by_packaging": False,
             "recovery_tested_by_packaging": False, "durably_saved_by_packaging": False,
             "issue558_progress_updates_authorized": False,
             "receiving_master_publication_owner": "conaled integration agent",
             "external_prerequisites": "Ordinary public Git history and the separately pinned compiler/dependency environment",
             "save_receipt_policy": "The exact final archive/save receipt is external until the next complete checkpoint; no completion companion"}
    if compact:
        retention_raw = json_bytes(retention_record)
        add_payload(payload, "RETENTION.json", Payload(descriptor(retention_raw), raw=retention_raw))
        policy_path = Path(__file__).absolute().with_name("RETENTION.md")
        if not policy_path.exists():
            policy_path = Path(__file__).absolute().parent.parent / "RETENTION.md"
        policy_desc = file_descriptor(policy_path)
        policy_raw = policy_path.read_bytes()
        need(descriptor(policy_raw, policy_desc["mode"]) == policy_desc, "Retention policy changed while reading")
        document_inputs.append((policy_path, policy_desc))
        add_payload(payload, "RETENTION.md", Payload(policy_desc, raw=policy_raw))
        state["retention_mode"] = COMPACT_MODE
        state["retention"] = {"manifest": "RETENTION.json", "manifest_descriptor": descriptor(retention_raw),
                              "policy": "RETENTION.md", "policy_descriptor": policy_desc,
                              "historical_outcomes_member": retention_record["historical_outcomes_member"]}
    state_raw = json_bytes(state)
    add_payload(payload, "STATE.json", Payload(descriptor(state_raw), raw=state_raw))
    continuation = payload[document_routes["continuation"]].read().decode("utf-8")
    start_raw = start_here(state, manifest, continuation)
    add_payload(payload, "START_HERE.md", Payload(descriptor(start_raw), raw=start_raw))
    own_path = Path(__file__).absolute()
    own_desc = file_descriptor(own_path)
    tool_raw = own_path.read_bytes()
    need(descriptor(tool_raw, own_desc["mode"]) == own_desc, "Checkpoint helper changed while reading")
    document_inputs.append((own_path, own_desc))
    add_payload(payload, "operations/checkpoint.py", Payload(descriptor(tool_raw, "100755"), raw=tool_raw))
    readme = own_path.with_name("checkpoint-README.md")
    readme_desc = file_descriptor(readme)
    readme_raw = readme.read_bytes()
    need(descriptor(readme_raw, readme_desc["mode"]) == readme_desc, "Checkpoint documentation changed while reading")
    document_inputs.append((readme, readme_desc))
    add_payload(payload, "operations/checkpoint-README.md", Payload(descriptor(readme_raw), raw=readme_raw))
    if compact:
        with tarfile.open(predecessor_archive, "r:xz") as tar:
            def previous_read(name):
                stream = tar.extractfile(retention_record["predecessor"]["packet_name"] + "/" + name)
                need(stream is not None, "Missing actual predecessor body: " + name)
                return stream.read()
            validate_retention(retention_record, {name: item.desc for name, item in payload.items()},
                               lambda name: payload[name].read(), previous_read)
    # Freeze observed input trees again before a plan can become a packet.
    for root, expected in input_trees:
        need(scan_directory(root, packaging=True) == expected, "Input tree changed during planning: " + str(root))
    for path, desc in document_inputs:
        need(file_descriptor(path) == desc, "Input document changed during planning: " + str(path))
    inventory = {"schema": SCHEMA, "members": {rel: item.desc for rel, item in sorted(payload.items())},
                 "boundary": "All literal files except INVENTORY.json itself; reconstructed historical bodies are not falsely listed as literal files"}
    inventory_raw = json_bytes(inventory)
    total = sum(item.desc["bytes"] for item in payload.values()) + len(inventory_raw)
    need(total <= CAP, "Expanded checkpoint exceeds 512 MiB including inventory")
    payload["INVENTORY.json"] = Payload(descriptor(inventory_raw), raw=inventory_raw)
    plan = {"schema": SCHEMA, "kind": "checkpoint-plan", "packet_name": name,
            "candidate": candidate, "source_tree": manifest["source_tree"],
            "regular_member_count": len(payload), "total_regular_bytes_including_inventory": total,
            "source_owner_count": len(updates), "source_deletion_count": len(deletions),
            "history_packet_count": len(history), "source_manifest_descriptor": descriptor(source_raw),
            "inventory_descriptor": descriptor(inventory_raw), "source_accepted": False}
    return payload, state, plan, (input_trees, document_inputs)


def validate_packet_structure(root: Path, members: dict[str, dict[str, Any]], reader=None) -> dict[str, Any]:
    read = reader or (lambda name: (root / safe_relative(name)).read_bytes())
    state = json.loads(read("STATE.json"))
    manifest = json.loads(read("SOURCE_MANIFEST.json"))
    need(state.get("schema") == manifest.get("schema") == SCHEMA, "Unsupported packet schema")
    need(state["packet_name"] == root.name, "Packet root name differs from state")
    need(state["source_manifest_descriptor"] == members["SOURCE_MANIFEST.json"], "Source manifest identity differs")
    validate_url(manifest["repository_url"])
    for key in ("public_base", "prerequisite_tree", "original_base", "original_base_tree", "candidate", "source_tree"):
        need(re.fullmatch(r"[0-9a-f]{40}", manifest[key]) is not None, "Invalid Git identity: " + key)
        need(state["current_source"][key] == manifest[key], "Root state source identity differs")
    for owner, desc in manifest["updates"].items():
        need(desc["mode"] in SOURCE_MODES, "Unsupported source payload mode: " + owner)
        safe_relative(owner)
        safe_relative(desc["payload"])
        need(desc["payload"] in members, "Missing source payload: " + owner)
        need(members[desc["payload"]] == {k: desc[k] for k in ("bytes", "sha256", "mode")},
             "Source payload descriptor differs: " + owner)
        raw = read(desc["payload"])
        oid = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        need(oid == desc["git_blob"], "Source Git blob differs: " + owner)
    need(len(manifest["deletions"]) == len(set(manifest["deletions"])), "Duplicate source deletion")
    for owner in manifest["deletions"]:
        safe_relative(owner)
        need(owner not in manifest["updates"], "Source both updated and deleted")
    need(set(state["documents"]) == REQUIRED_DOCUMENTS, "Required reading route is incomplete")
    for route in state["documents"].values():
        safe_relative(route)
        need(route in members, "Missing required document: " + route)
    compact = "retention_mode" in state
    if compact:
        need(state["retention_mode"] == COMPACT_MODE and state["history"] == [] and state["directories"] == {},
             "Compact state cannot carry bulk history or directory selections")
        routes = state["retention"]
        need(routes["manifest"] == "RETENTION.json" and routes["policy"] == "RETENTION.md" and
             members.get("RETENTION.json") == routes["manifest_descriptor"] and
             members.get("RETENTION.md") == routes["policy_descriptor"], "Retention manifest or policy identity differs")
        record = compact_json(read("RETENTION.json"))
        need(record["historical_outcomes_member"] == routes["historical_outcomes_member"],
             "Root historical outcome route differs")
        validate_retention(record, members, read)
        allowed_members = {"START_HERE.md", "STATE.json", "SOURCE_MANIFEST.json", "INVENTORY.json",
                           "RETENTION.json", "RETENTION.md", PREDECESSOR_INVENTORY,
                           "operations/checkpoint.py", "operations/checkpoint-README.md"}
        allowed_members |= set(record["selection"]) | set(state["documents"].values())
        allowed_members |= {desc["payload"] for desc in manifest["updates"].values()}
        need(set(members) == allowed_members, "Unselected or missing compact payload member")
        literal_keys = set()
        for member in members:
            compact_member(member)
            key = payload_key(members[member])
            need(key not in literal_keys, "Duplicate literal compact payload bytes/mode: " + member)
            literal_keys.add(key)
    else:
        need("retention" not in state, "Retention record has no compact mode")
        need({Path(record["root"]).name for record in state["history"]} == INHERITED_ROOTS,
             "Inherited history packet set differs")
        for record in state["history"]:
            safe_relative(record["root"])
            need(record["inventory"] == record["root"] + "/INVENTORY.json", "Invalid historical inventory route")
            need(members[record["inventory"]] == record["inventory_descriptor"], "Historical inventory identity differs")
            prefix = record["root"] + "/"
            inherited = json.loads(read(record["inventory"]))["members"]
            observed = {name[len(prefix):]: desc for name, desc in members.items() if name.startswith(prefix)}
            need(set(observed) == set(inherited) | {"INVENTORY.json"}, "Historical member set differs")
            need(all(observed[name] == desc for name, desc in inherited.items()), "Historical inventory contents differ")
    need(state["payload_limit_bytes_including_inventory"] == CAP, "Changed payload cap")
    total = sum(desc["bytes"] for desc in members.values())
    need(total <= CAP, "Expanded packet exceeds 512 MiB")
    return {"schema": SCHEMA, "kind": "packet-verification", "verified_utc": utc_now(),
            "packet_name": state["packet_name"], "candidate": manifest["candidate"],
            "source_tree": manifest["source_tree"], "regular_member_count": len(members),
            "total_regular_bytes_including_inventory": total,
            "inventory_descriptor": members["INVENTORY.json"], "complete_inventory_verified": True,
            "history_inventories_verified": not compact, "source_payloads_verified": True,
            "source_recovery_executed": False, "source_accepted": False, "durably_saved": False,
            **({"retention_mode": COMPACT_MODE, "predecessor_inventory_verified": True,
                "exhaustive_dispositions_verified": True, "predecessor_archive_needed_for_recovery": False}
               if compact else {})}


def verify_directory(root: Path) -> dict[str, Any]:
    return validate_packet_structure(root, verify_inventory(root))


def verify_archive(archive: Path, *, expected_sha256: str | None = None,
                   expected_bytes: int | None = None, extract: Path | None = None) -> dict[str, Any]:
    outer = file_descriptor(archive)
    need(expected_sha256 is None or outer["sha256"] == expected_sha256, "Archive SHA256 mismatch")
    need(expected_bytes is None or outer["bytes"] == expected_bytes, "Archive byte count mismatch")
    with tarfile.open(archive, "r:xz") as tar:
        entries = tar.getmembers()
        need(entries and all(m.isfile() for m in entries), "Archive must contain only regular files")
        need(len(entries) == len({m.name for m in entries}), "Duplicate archive member")
        roots = set()
        for member in entries:
            path = safe_relative(member.name)
            need(len(path.parts) >= 2, "Archive member lacks its single root")
            roots.add(path.parts[0])
            need(format(stat.S_IFREG | member.mode, "o") in MODES, "Unsupported archive file mode")
        need(len(roots) == 1, "Archive must have one root")
        root_name = roots.pop()
        need(sum(m.size for m in entries) <= CAP, "Archive expanded bytes exceed 512 MiB")
        prefix = root_name + "/"
        by_rel = {m.name[len(prefix):]: m for m in entries}
        need("INVENTORY.json" in by_rel, "Missing archive inventory")
        inv_stream = tar.extractfile(by_rel["INVENTORY.json"])
        need(inv_stream is not None, "Cannot read archive inventory")
        inv_raw = inv_stream.read()
        inventory = json.loads(inv_raw)
        need(inventory.get("schema") == SCHEMA, "Unsupported archive inventory")
        need(set(by_rel) == set(inventory["members"]) | {"INVENTORY.json"}, "Archive inventory member set differs")
        observed = {}
        for rel, member in by_rel.items():
            stream = tar.extractfile(member)
            need(stream is not None, "Missing archive stream: " + rel)
            digest = hashlib.sha256()
            count = 0
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
                count += len(chunk)
            desc = {"bytes": count, "sha256": digest.hexdigest(), "mode": format(stat.S_IFREG | member.mode, "o")}
            need(count == member.size, "Archive declared size differs")
            if rel != "INVENTORY.json":
                need(desc == inventory["members"][rel], "Archive hash/bytes/mode differ: " + rel)
            observed[rel] = desc
        if extract is not None:
            need(not extract.exists() and extract.parent.is_dir(), "Extraction destination must be new")
            extract.mkdir()
            packet_root = extract / root_name
            packet_root.mkdir()
            for rel, member in by_rel.items():
                target = packet_root / safe_relative(rel)
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open("xb") as output:
                    shutil.copyfileobj(tar.extractfile(member), output)  # type: ignore[arg-type]
                target.chmod(member.mode)
            result = verify_directory(packet_root)
        else:
            def archive_reader(name):
                stream = tar.extractfile(by_rel[name])
                need(stream is not None, "Missing archive stream: " + name)
                return stream.read()
            result = validate_packet_structure(Path(root_name), observed, archive_reader)
            result["kind"] = "archive-verification"
    result.update(archive=str(archive), archive_descriptor=outer,
                  extracted_packet=str(extract / root_name) if extract is not None else None)
    need(file_descriptor(archive) == outer, "Archive changed during verification")
    return result


def own_git_storage(repo: Path) -> None:
    dotgit = repo / ".git"
    no_symlink_parents(dotgit)
    need(dotgit.is_dir(), "Recovery requires own ordinary .git directory, not a linked worktree")
    need(Path(git_text(repo, "rev-parse", "--absolute-git-dir")).resolve() == dotgit.resolve(), "Git directory is external")
    common = Path(git_text(repo, "rev-parse", "--git-common-dir"))
    need((common if common.is_absolute() else repo / common).resolve() == dotgit.resolve(), "Shared common Git storage")
    need(git_text(repo, "rev-parse", "--is-shallow-repository") == "false", "Recovery repository is shallow")
    need(not (dotgit / "shallow").exists(), "Shallow boundary present")
    need(not (dotgit / "objects/info/alternates").exists(), "Git alternates are not allowed")
    need(not (dotgit / "objects/info/http-alternates").exists(), "HTTP Git alternates are not allowed")
    partial = git(repo, "config", "--get-regexp", r"^(extensions\.partialClone|remote\..*\.(promisor|partialclonefilter))$", allow_failure=True)
    need(partial.returncode == 1 and not partial.stdout, "Partial/promisor Git storage is not allowed")
    need(not (dotgit / "info/sparse-checkout").exists(), "Sparse checkout is not allowed")
    objects = dotgit / "objects"
    no_symlink_parents(objects)
    need(objects.is_dir(), "Missing own Git object directory")
    for path in objects.rglob("*"):
        need(not path.is_symlink(), "Symlink in Git object storage")
        if path.is_file():
            need(path.stat().st_nlink == 1, "Hard-linked Git object storage is not owned")


def inspect_recovery(packet: Path, destination: Path) -> dict[str, Any]:
    packet_result = verify_directory(packet)
    manifest = load_json(packet / "SOURCE_MANIFEST.json")
    own_git_storage(destination)
    need(git_text(destination, "rev-parse", "HEAD") == manifest["public_base"], "Recovery HEAD is not the declared public base")
    need(git_text(destination, "rev-parse", "HEAD^{tree}") == manifest["prerequisite_tree"], "Public prerequisite tree differs")
    ancestor(destination, manifest["original_base"], manifest["public_base"])
    need(git_text(destination, "rev-parse", manifest["original_base"] + "^{tree}") == manifest["original_base_tree"], "Original base tree differs")
    index_tree = git_text(destination, "write-tree")
    need(index_tree == manifest["source_tree"], "Whole recovery index tree differs: " + index_tree)
    git(destination, "diff", "--quiet", "--")
    need(not git(destination, "ls-files", "--others", "--exclude-standard", "-z").stdout, "Recovery has untracked files")
    need(not git(destination, "ls-files", "--others", "--ignored", "--exclude-standard", "-z").stdout, "Recovery has ignored files")
    git(destination, "diff", "--cached", "--check", manifest["public_base"], "--")
    entries = tree_entries(destination, index_tree)
    for owner, entry in entries.items():
        path = destination / safe_relative(owner)
        desc = file_descriptor(path)
        raw = path.read_bytes()
        need(desc["mode"] == entry["mode"], "Tracked recovery mode differs: " + owner)
        oid = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        need(oid == entry["git_blob"], "Tracked recovery body differs: " + owner)
    for owner, desc in manifest["updates"].items():
        need(file_descriptor(destination / owner) == {k: desc[k] for k in ("bytes", "sha256", "mode")},
             "Updated source differs after recovery: " + owner)
    for owner in manifest["deletions"]:
        need(not (destination / owner).exists(), "Declared source deletion remains: " + owner)
    need(git_text(destination, "remote", "get-url", "origin") == manifest["repository_url"], "Recovery origin differs")
    return {"schema": SCHEMA, "kind": "recovered-source-inspection", "verified_utc": utc_now(),
            "packet": str(packet), "destination": str(destination),
            "candidate_identity_from_packet": manifest["candidate"], "public_base": manifest["public_base"],
            "source_tree": index_tree, "tracked_files_checked": len(entries),
            "source_updates_checked": len(manifest["updates"]), "source_deletions_checked": len(manifest["deletions"]),
            "own_nonshallow_git_storage": True, "all_tracked_bodies_and_modes_match": True,
            "no_unstaged_untracked_or_ignored_files": True, "source_style_exit_code": 0,
            "packet_inventory_descriptor": packet_result["inventory_descriptor"],
            "source_accepted": False, "durably_saved": False}


def restore(packet: Path, destination: Path, public_cache: Path | None = None) -> dict[str, Any]:
    verify_directory(packet)
    manifest = load_json(packet / "SOURCE_MANIFEST.json")
    need(not destination.exists() and destination.parent.is_dir(), "Recovery destination must be new")
    no_symlink_parents(destination)
    source = manifest["repository_url"]
    if public_cache is not None:
        own_git_storage(public_cache)
        need(git_text(public_cache, "remote", "get-url", "origin") == source, "Public cache origin differs")
        need(git_text(public_cache, "rev-parse", "HEAD") == manifest["public_base"], "Public cache must be at the declared prerequisite")
        need(git_text(public_cache, "rev-parse", "HEAD^{tree}") == manifest["prerequisite_tree"], "Public cache prerequisite tree differs")
        ancestor(public_cache, manifest["original_base"], manifest["public_base"])
        if manifest["candidate"] != manifest["public_base"]:
            private = git(public_cache, "cat-file", "-e", manifest["candidate"] + "^{commit}", allow_failure=True)
            need(private.returncode != 0, "Public cache contains the private candidate; use public-only history")
        source = str(public_cache)
    started = utc_now()
    git(None, "clone", "--no-checkout", "--no-local", "--no-hardlinks", "--", source, str(destination))
    if public_cache is not None:
        git(destination, "remote", "set-url", "origin", manifest["repository_url"])
    git(destination, "checkout", "--detach", manifest["public_base"])
    own_git_storage(destination)
    need(git_text(destination, "rev-parse", "HEAD^{tree}") == manifest["prerequisite_tree"], "Cloned public tree differs")
    ancestor(destination, manifest["original_base"], manifest["public_base"])
    for owner in manifest["deletions"]:
        path = destination / safe_relative(owner)
        no_symlink_parents(path)
        need(path.is_file(), "Expected public file for deletion: " + owner)
        path.unlink()
    for owner, desc in manifest["updates"].items():
        target = destination / safe_relative(owner)
        no_symlink_parents(target)
        target.parent.mkdir(parents=True, exist_ok=True)
        raw = (packet / safe_relative(desc["payload"])).read_bytes()
        need(descriptor(raw, desc["mode"]) == {k: desc[k] for k in ("bytes", "sha256", "mode")}, "Source payload changed during restoration")
        target.write_bytes(raw)
        target.chmod(int(desc["mode"], 8) & 0o777)
    git(destination, "add", "--all")
    result = inspect_recovery(packet, destination)
    result.update(kind="source-restoration", started_utc=started, completed_utc=utc_now(),
                  restore_operations_completed=True, clone_source_kind="verified separate public cache" if public_cache else "canonical public URL",
                  private_candidate_commit_recreated=False, compilation_executed=False)
    return result


def pack(config: Path, archive: Path, stage: Path, plan_only: bool = False) -> dict[str, Any]:
    payload, state, plan, frozen_inputs = build_plan(config)
    if plan_only:
        return plan
    need(archive.name == state["packet_name"] + ".tar.xz", "Archive filename must be packet_name + .tar.xz")
    need(not stage.exists() and stage.parent.is_dir(), "Staging directory must be new")
    need(not archive.exists() and archive.parent.is_dir(), "Archive output must be new")
    stage.mkdir()
    root = stage / state["packet_name"]
    root.mkdir()
    for rel, item in sorted(payload.items()):
        target = root / safe_relative(rel)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(item.read())
        target.chmod(int(item.desc["mode"], 8) & 0o777)
    staged = verify_directory(root)
    # Creating the archive never overwrites an earlier checkpoint or partial attempt.
    with archive.open("xb") as output:
        with tarfile.open(fileobj=output, mode="w:xz", preset=6, format=tarfile.PAX_FORMAT) as tar:
            for rel, item in sorted(payload.items()):
                info = tarfile.TarInfo(state["packet_name"] + "/" + rel)
                info.size = item.desc["bytes"]
                info.mode = int(item.desc["mode"], 8) & 0o777
                info.mtime = 0
                info.uid = info.gid = 0
                info.uname = info.gname = ""
                with (root / rel).open("rb") as stream:
                    tar.addfile(info, stream)
    archive.chmod(0o644)
    verified = verify_archive(archive)
    need(verified["inventory_descriptor"] == staged["inventory_descriptor"], "Packed inventory differs from staged inventory")
    # Check that every live carrier still has its frozen identity after packing.
    for item in payload.values():
        if item.path is not None:
            need(file_descriptor(item.path) == item.desc, "Input carrier changed during packing")
    input_trees, document_inputs = frozen_inputs
    for root_path, expected in input_trees:
        need(scan_directory(root_path, packaging=True) == expected,
             "Input directory membership or contents changed during packing: " + str(root_path))
    for path, expected in document_inputs:
        need(file_descriptor(path) == expected, "Input document changed during packing: " + str(path))
    return {**plan, "kind": "checkpoint-packed", "completed_utc": utc_now(),
            "archive": str(archive), "archive_descriptor": verified["archive_descriptor"],
            "staged_packet": str(root), "archive_verified": True, "recovery_tested": False,
            "durably_saved": False, "separate_save_receipt_required": True}


def emit_result(value: dict[str, Any], receipt: str | None) -> None:
    raw = json_bytes(value)
    if receipt is not None:
        path = new_output(receipt)
        with path.open("xb") as stream:
            stream.write(raw)
        path.chmod(0o644)
    sys.stdout.buffer.write(raw)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    p = subs.add_parser("pack", help="Plan or create one complete checkpoint from an immutable candidate")
    p.add_argument("--config", required=True)
    p.add_argument("--archive")
    p.add_argument("--stage")
    p.add_argument("--plan-only", action="store_true")
    p.add_argument("--receipt")
    p = subs.add_parser("verify", help="Verify the entire extracted packet or archive")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument("--packet")
    group.add_argument("--archive")
    p.add_argument("--expected-sha256")
    p.add_argument("--expected-bytes", type=int)
    p.add_argument("--extract")
    p.add_argument("--receipt")
    for command in ("restore", "inspect"):
        p = subs.add_parser(command)
        p.add_argument("--packet", required=True)
        p.add_argument("--destination", required=True)
        p.add_argument("--receipt")
        if command == "restore":
            p.add_argument("--public-cache", help="Optional separate ordinary full public clone, at the exact base and without private candidate objects")
    args = parser.parse_args()
    if args.receipt:
        new_output(args.receipt)
    if args.command == "pack":
        need(args.plan_only or (args.archive and args.stage), "Pack needs --archive and --stage unless --plan-only")
        archive = new_output(args.archive) if args.archive else Path("unused-plan-archive")
        stage = new_output(args.stage) if args.stage else Path("unused-plan-stage")
        result = pack(absolute_path(args.config), archive, stage, args.plan_only)
    elif args.command == "verify":
        if args.packet:
            need(not (args.extract or args.expected_sha256 or args.expected_bytes is not None), "Archive-only options supplied with --packet")
            result = verify_directory(absolute_path(args.packet, directory=True))
        else:
            result = verify_archive(absolute_path(args.archive), expected_sha256=args.expected_sha256,
                                    expected_bytes=args.expected_bytes,
                                    extract=new_output(args.extract) if args.extract else None)
    else:
        packet = absolute_path(args.packet, directory=True)
        if args.command == "restore":
            result = restore(packet, new_output(args.destination),
                             absolute_path(args.public_cache, directory=True) if args.public_cache else None)
        else:
            result = inspect_recovery(packet, absolute_path(args.destination, directory=True))
    emit_result(result, args.receipt)


if __name__ == "__main__":
    try:
        main()
    except (CheckpointError, OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print(json.dumps({"status": "failed", "error_type": type(error).__name__, "error": str(error),
                          "source_accepted": False, "durably_saved": False}), file=sys.stderr)
        raise SystemExit(1)

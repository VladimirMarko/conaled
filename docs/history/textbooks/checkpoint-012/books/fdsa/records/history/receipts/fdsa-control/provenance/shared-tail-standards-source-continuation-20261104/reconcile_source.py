"""Independent, source-only XU03 receiving reconciliation; never runs Lean."""
from pathlib import Path
from datetime import datetime, timezone
from functools import lru_cache
from collections import Counter
import hashlib
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
C = Path(__file__).resolve().parents[2]
P = Path(__file__).resolve().parent
R = C.parent / "conaled-ch02-top-down"
W = C.parent / "conaled-ch01-review"
L = "726cb9a9b9ff4444a7614383de4fb336e8804aa7"
J = "932438a765340d69fa6402f6abd17def6ec28d13"
T = "02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9"
B = "4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8"
A = "a0597381f02eddd074ee96cabaa974f2062285f8"
Z = "4b5dbfa07288acc73f25c27838d3fb2f78e77d71"
SOURCE = C / "provenance/shared-tail-source-integration-20261104"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def ident(path):
    raw = path.read_bytes()
    return {"path": str(path.relative_to(C)), "bytes": len(raw),
            "lines": len(raw.splitlines()), "sha256": sha(raw)}


def read(relative):
    return json.loads((C / relative).read_text())


def git(*args, repo=R):
    return subprocess.check_output(["git", "--no-optional-locks", "-C", str(repo), *args])


@lru_cache(None)
def raw(commit, path):
    return git("show", commit + ":" + path)


def source_ident(commit, path):
    data = raw(commit, path)
    return {"path": path, "commit": commit, "bytes": len(data),
            "lines": len(data.splitlines()), "sha256": sha(data),
            "git_blob": git("rev-parse", commit + ":" + path).decode().strip()}


def tree(commit):
    answer = {}
    for entry in git("ls-tree", "-r", "-z", commit).split(b"\0"):
        if not entry:
            continue
        metadata, path = entry.split(b"\t", 1)
        answer[path.decode()] = metadata.decode().split()
    return answer


def executable(text):
    """Erase nested comments and strings, preserving positions and newlines."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i+1] != "\n":
                    out[i+1] = " "
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end-i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    assert depth == 0 and not quoted
    return "".join(out)


def imports(text):
    return [name for match in re.finditer(r"^(?:public\s+)?import\s+([^\n]+)", executable(text), re.M)
            for name in match[1].split()]


ready = read("provenance/shared-tail-integration-readiness-20261104/inventory.json")
prior = read("provenance/shared-tail-standards-receiving-preparation-20261104/preparation.json")
binding = read("provenance/shared-tail-type-evidence-readiness-20261104/receiver-binding.json")
author = json.loads((SOURCE / "result.json").read_text())
baseline = json.loads((SOURCE / "baseline.json").read_text())
manifest = json.loads((SOURCE / "receipt.json").read_text())
scope = ready["six_path_scope"]
assert git("show", "-s", "--format=%P", L).decode().strip().split() == [J, T]
assert git("rev-parse", L + "^{tree}").decode().strip() == "43f1c15166931d4bd3e91e6dbf12059d0da1cfc2"
assert git("merge-base", J, T).decode().strip() == B
for commit in [J, B, A, T]:
    assert subprocess.run(["git", "--no-optional-locks", "-C", str(R), "merge-base", "--is-ancestor", commit, L], capture_output=True).returncode == 0
history = git("log", "--reverse", "--format=%H %P %s", B + ".." + T).decode().splitlines()
assert history == author["original_tail_history"] and len(history) == 8
before, after = tree(J), tree(L)
changed = sorted(path for path in set(before) | set(after) if before.get(path) != after.get(path))
assert changed == sorted(scope) and len(before) == 1606 and len(after) == 1610
outside = [path for path in before if path not in scope]
assert len(outside) == 1604 and all(before[path] == after[path] for path in outside)
numstat = git("diff", "--numstat", J, L).decode()
assert numstat == author["numstat"]
assert sum(int(line.split("\t")[0]) for line in numstat.splitlines()) == 1198
assert all(line.split("\t")[1] == "0" for line in numstat.splitlines())
saved_diff = (SOURCE / "source.diff").read_bytes()
diff_commands = [("diff", "--binary", "--full-index", J, L), ("diff", "--binary", J, L)]
matching_diff_commands = [list(args) for args in diff_commands if git(*args) == saved_diff]
assert matching_diff_commands
payloads = []
for entry in manifest["artifacts"]:
    actual = ident(SOURCE / entry["path"])
    assert all(actual[key] == entry[key] for key in ("bytes", "lines", "sha256"))
    payloads.append(actual)
assert len(payloads) == 14
refs = dict(line.split(" ", 1) for line in git("for-each-ref", "--format=%(refname) %(objectname)").decode().splitlines())
oldrefs = {entry["ref"]: entry["object"] for entry in baseline["all_prior_refs"]}
assert len(oldrefs) == 65 and all(refs[k] == v for k, v in oldrefs.items())
assert set(refs) - set(oldrefs) == {"refs/heads/work/fdsa-tail-integration"}
assert refs["refs/heads/work/fdsa-tail-integration"] == L and refs["refs/heads/work/fdsa-book"] == J
assert refs == {entry["ref"]: entry["object"] for entry in author["refs_after"]}
assert git("rev-parse", "HEAD", repo=W).decode().strip() == L
assert not git("status", "--porcelain=v1", "--untracked-files=all", repo=W)
protected = []
for entry in ready["six_corrected_predecessor_Lean_sources_to_preserve"] + ready["two_predecessor_public_notes_to_preserve"]:
    path = entry["path"]
    assert raw(L, path) == raw(J, path)
    protected.append(source_ident(L, path))

# Reconstruct the exact three held documentary recipes independently.
recipe = ready["documentary_proposal"]
root = "SquareApplications.lean"
assert raw(L, root) == raw(J, root).replace(b"import Examples.PermutationOrder\n", b"import Examples.PermutationOrder\nimport Examples.PermutationTail\n", 1)
note = "docs/research/fdsa-permutation-tail.md"
paragraphs = (C / recipe[note]["starting_proposal"]).read_bytes().split(b"\n\n")
slots = [n for n, paragraph in enumerate(paragraphs) if paragraph.startswith(b"**Validation snapshot")]
assert len(slots) == 1
paragraphs[slots[0]] = recipe[note]["replace_only_validation_snapshot_paragraph_with"].encode()
assert b"\n\n".join(paragraphs) == raw(L, note)
mapping = "docs/research/fdsa-reconstruction-map.md"
marker = b"\n## Shared conditional remaining orders (draft)\n"
oldmap = raw(T, mapping)
assert oldmap.count(marker) == 1
tail = oldmap[oldmap.index(marker):]
old_sentence = recipe[mapping]["replace_only_exact_old_sentence"].encode()
assert tail.count(old_sentence) == 1
tail = tail.replace(old_sentence, recipe[mapping]["replacement_sentence"].encode(), 1)
assert raw(L, mapping) == raw(J, mapping) + tail
conflict = json.loads((SOURCE / "03-conflict-before-resolution.json").read_text())
for line, commit in zip(conflict["actual_unmerged_index"].splitlines(), [B, J, T]):
    stageblob = line.split()[1]
    assert stageblob == git("rev-parse", commit + ":" + mapping).decode().strip()
conflict_bytes = (SOURCE / "actual-map-conflict.txt").read_bytes()
assert len(conflict_bytes) == conflict["bytes"] and sha(conflict_bytes) == conflict["sha256"]
assert conflict_bytes.count(b"<<<<<<< HEAD\n") == conflict_bytes.count(b"=======\n") == conflict_bytes.count(b">>>>>>> " + T.encode()) == 1
assert b"<<<<<<<" not in raw(L, mapping) and b">>>>>>>" not in raw(L, mapping)

# Derive all explicit authored declarations, keeping private/anonymous rows separate.
lean_paths = [p for p in scope if p.endswith(".lean") and p != root]
inventory = []
original_headers = {}
for commit in [A, L]:
    rows = []
    for path in lean_paths:
        data = raw(commit, path)
        if commit == L:
            assert data == raw(T, path) == raw(Z, path)
        text = data.decode()
        cleaned = executable(text)
        namespace = re.search(r"^namespace (\S+)", cleaned, re.M)[1]
        lines = text.splitlines(keepends=True)
        cleanlines = cleaned.splitlines(keepends=True)
        assert len(lines) == len(cleanlines)
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide)\b", cleaned)
        assert not re.search(r"^example\b", cleaned, re.M)
        for n, line in enumerate(cleanlines, 1):
            match = re.match(r"^((?:(?:private|noncomputable|local)\s+)*)(def|theorem|instance)\s+(.*)", line)
            if not match:
                continue
            modifiers, kind = match[1].split(), match[2]
            name = None if match[3].startswith(":") else match[3].split()[0]
            visibility = "anonymous_local" if name is None else ("private" if "private" in modifiers else "public")
            suffix = "".join(lines[n-1:])
            delimiter = re.search(r":=|\bwhere\b", "".join(cleanlines[n-1:]))
            assert delimiter
            header = suffix[:delimiter.start()]
            rows.append({"source": path, "line": n, "kind": kind, "modifiers": modifiers,
                         "visibility": visibility, "name": namespace + "." + name if name else None,
                         "header": header, "header_bytes": len(header.encode()),
                         "header_sha256": sha(header.encode()), "header_delimiter": delimiter[0]})
    if commit == A:
        original_headers = {row["name"]: row["header"] for row in rows if row["name"]}
    else:
        inventory = rows
assert Counter(row["visibility"] for row in inventory) == {"public": 61, "private": 19, "anonymous_local": 8}
assert Counter(row["kind"] for row in inventory if row["visibility"] == "public") == {"def": 15, "theorem": 46}
assert all(original_headers[row["name"]] == row["header"] for row in inventory if row["name"])
program_path = C / "provenance/shared-order-tail-acceptance-preparation-20261104/StatementsTail61.lean"
program = program_path.read_text()
names = re.findall(r"^#check\s+@([^\s]+)", program, re.M)
assert names == [row["name"] for row in inventory if row["visibility"] == "public"] == ready["public_names_in_existing_program_order"] == binding["program"]["names"]
assert len(names) == len(set(names)) == 61
assert all(f"set_option pp.{option} true" in program for option in ["universes", "explicit", "fullNames"])

# Independently parse the immutable local import closure without reading compiler outputs.
roots = imports(program)
assert roots == binding["roots"]
pending, sources, edges, external = list(roots), {}, [], set()
while pending:
    module = pending.pop()
    path = module.replace(".", "/") + ".lean"
    if path in sources:
        continue
    assert path in after
    item = source_ident(L, path)
    sources[path] = {key: item[key] for key in ("bytes", "sha256", "git_blob")}
    assert raw(L, path) == raw(Z, path)
    for imported in imports(raw(L, path).decode()):
        local = imported.replace(".", "/") + ".lean" in after
        edges.append({"from": module, "to": imported, "local": local})
        if local:
            pending.append(imported)
        else:
            external.add(imported)
assert sources == binding["local_sources"]
assert sorted(edges, key=lambda edge: (edge["from"], edge["to"])) == sorted(binding["import_edges"], key=lambda edge: (edge["from"], edge["to"]))
assert sorted(external) == binding["direct_external_imports"]
assert (len(sources), len(external), sum(e["local"] for e in edges), sum(not e["local"] for e in edges)) == (9, 19, 13, 26)
old_importers = []
for path in before:
    if path.endswith(".lean"):
        text = raw(J, path).decode()
        if "PermutationTail" not in text:
            continue
        if any("PermutationTail" in name for name in imports(text)):
            old_importers.append(path)
assert not old_importers

# Reproduce the concrete historical observation difference, preserving literal paths.
observations = {}
for label, directory in [("Z", "chapter02-statements815-input-observations-20261104-attempt1"), ("J", "shared-order53-input-observations-20261104-attempt1")]:
    pre = read("provenance/" + directory + "/pre-inputs.json")["identity"]
    post = read("provenance/" + directory + "/post-inputs.json")["identity"]
    assert pre == post
    observations[label] = pre
z, j = observations["Z"], observations["J"]
common = sorted(set(z["local_sources"]) & set(j["local_sources"]))
assert len(common) == 6 and all(z["local_sources"][path] == j["local_sources"][path] for path in common)
stems = {".lake/build/lib/lean/" + path[:-5] for path in common}
supported = {stem + suffix for stem in stems for suffix in (".olean", ".olean.hash", ".olean.private", ".olean.server", ".trace")}
zobjects = {k: v for k, v in z["local_compiler_objects_and_traces"].items() if k in supported}
jobjects = {k: v for k, v in j["local_compiler_objects_and_traces"].items() if k in supported}
assert zobjects.keys() == jobjects.keys() and len(zobjects) == 18
different = [{"path": key, "Z": zobjects[key], "J": jobjects[key]} for key in sorted(zobjects) if zobjects[key] != jobjects[key]]
assert len(different) == 6 and all(row["path"].endswith(".trace") for row in different)
deps = [{"name": key, "Z": z["dependencies"][key], "J": j["dependencies"][key]} for key in sorted(z["dependencies"]) if z["dependencies"][key] != j["dependencies"][key]]
assert len(deps) == 9 and z["configuration"] == j["configuration"] and z["runtime"] == j["runtime"]
root_history = read("provenance/shared-tail-resource-and-type-readiness-20261104/preparation.json")["old_Z_to_current_J_observation_comparison"]
assert different == root_history["artifact_differences"] and deps == root_history["complete_dependency_record_differences"]

# Reuse already completed instructions/source semantics only by exact stored identities.
instructions = read("provenance/shared-order-standards-integration-20261104/source-assessment.json")["unchanged_instructions"]
for entry in instructions:
    assert sha(raw(L, entry["path"])) == entry["sha256"]
retained = []
for entry in prior["retained_exact_same_reviewer_records"]:
    actual = ident(C / entry["path"])
    assert actual["sha256"] == entry["sha256"]
    retained.append(actual)
configuration = {}
for path, observation in j["configuration"].items():
    assert raw(L, path) == raw(J, path)
    data = raw(L, path)
    assert len(data) == observation["bytes"] and sha(data) == observation["sha256"]
    configuration[path] = observation
assert len(configuration) == 10

result = {
    "reviewer": "/root/chapter02_standards", "axis": "Standards", "unit": "FDSA-XU03",
    "recorded_utc": datetime.now(timezone.utc).isoformat(), "candidate": L, "base": J,
    "original_base": B, "original_candidate": A, "corrected_tip": T, "historical_Z": Z,
    "tree": git("rev-parse", L + "^{tree}").decode().strip(), "parents": [J, T],
    "history": history, "scope": scope, "numstat": numstat,
    "source_identities": [source_ident(L, path) for path in scope],
    "outside_scope": {"J_paths": 1606, "L_paths": 1610, "preserved": len(outside), "mismatches": []},
    "protected_predecessors": protected, "protected_refs": {"old_count": 65, "new_count": 66, "all_old_exact": True, "sole_added_ref": "refs/heads/work/fdsa-tail-integration", "accepted_ref": J},
    "author_package_payloads": payloads, "author_receipt": ident(SOURCE / "receipt.json"),
    "saved_diff": ident(SOURCE / "source.diff"), "matching_diff_commands": matching_diff_commands,
    "documentary_recipe": {"root_exact": True, "map_complete_J_prefix_plus_original_tail_with_one_status_replacement": True, "note_exact_held_proposal_with_one_paragraph_replacement": True, "conflict_stages_exact_B_J_T": True, "actual_merge_exit": 1, "sole_conflict": "docs/research/fdsa-reconstruction-map.md", "actual_commit_exit": 0},
    "declarations": inventory, "counts": {"public": 61, "public_theorems": 46, "public_definitions": 15, "private_theorems": 19, "anonymous_local_instances": 8, "anonymous_examples": 0},
    "all80_named_headers_unchanged_from_original": True,
    "header_convention": "Start at declaration command including modifiers; stop immediately before := or where; retain preceding whitespace/newlines; private names are source names, not guessed compiler manglings.",
    "program": {**ident(program_path), "roots": roots, "names": names, "executed_by_reviewer": False},
    "closure": {"sources": sources, "edges": edges, "external": sorted(external), "all_nine_equal_historical_Z": True, "existing_J_importers": old_importers},
    "historical_input_gap": {"common_sources": common, "all_source_bytes_equal": True, "complete_supported_keys": sorted(zobjects), "matching_olean_and_hash_entries": 12, "trace_differences": different, "dependency_differences": deps, "configuration_equal": True, "runtime_equal": True, "literal_paths_retained": True, "pre_post_pairs_exact": True},
    "unchanged_configurations": configuration, "unchanged_instructions": instructions,
    "retained_same_reviewer_records": retained,
    "source_only_result": "All independent immutable-source, exact recipe, scope, inventory and affected-source identity checks passed. This is no receiving compiler/type/audit/final acceptance credit.",
    "receiving_credit": 0, "overall": "Blocked pending matching full candidate validation and receiving statement evidence, then both final axes and acceptance steps.",
    "reviewer_source_ref_runtime_cache_compiler_changes": False,
}
out = P / "independent-source-reconciliation.json"
assert not out.exists()
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"saved": ident(out), "candidate": L, "source_paths": 6, "read_source_lines": 2073,
                  "declaration_rows": len(inventory), "closure": [9, 19, 13, 26],
                  "protected_refs": [65, 66], "source_checks_passed": True, "receiving_credit": 0}, indent=2))

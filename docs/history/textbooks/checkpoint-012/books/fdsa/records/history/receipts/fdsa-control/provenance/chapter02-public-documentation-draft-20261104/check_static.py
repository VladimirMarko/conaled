#!/usr/bin/env python3
"""Source-only documentation checks at one immutable Git snapshot; never builds Lean."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
REPO = BASE / "conaled-ch02-random-pivot"
SNAPSHOT = "f673ee87195e4aaeef4b41767a7468c70ad6214f"
ACCEPTED = "07e480f6ec9958d4975bb90151005b84f2907614"


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args])


def sources_at(ref):
    entries = []
    for line in git("ls-tree", "-r", ref).decode().splitlines():
        info, path = line.split("\t", 1)
        if path.endswith(".lean"):
            entries.append((path, info.split()[2]))
    payload = "".join(oid + "\n" for _, oid in entries).encode()
    raw = subprocess.check_output(["git", "-C", str(REPO), "cat-file", "--batch"], input=payload)
    result = {}
    off = 0
    for path, oid in entries:
        end = raw.index(b"\n", off)
        head = raw[off:end].decode().split()
        assert head[0] == oid and head[1] == "blob"
        size = int(head[2])
        data = raw[end + 1:end + 1 + size]
        assert raw[end + 1 + size:end + 2 + size] == b"\n"
        result[path] = data
        off = end + 2 + size
    assert off == len(raw)
    return result


def remove_comments(text):
    # Preserve newlines and strings; support nested Lean block comments.
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            result.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1
                result.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            if text[i] == '"':
                quoted = True
            i += 1
    assert depth == 0
    return "".join(result)


DECL = re.compile(r"(?m)^\s*(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+([A-Za-z_][A-Za-z0-9_'.?]*)")
IMPORT = re.compile(r"(?m)^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+([^\n]+)")


def module_path(name):
    return name.replace(".", "/") + ".lean"


def imports(text):
    return [name for group in IMPORT.findall(remove_comments(text)) for name in group.split()]


def closure(sources, proposed):
    graph = {p: imports(b.decode()) for p, b in sources.items()}
    graph["SquareApplications.lean"] += proposed
    graph["ProofAudit.lean"] += proposed
    todo = ["SquareApplications.lean", "ProofAudit.lean"]
    seen, missing = set(), set()
    project_roots = {p.split("/")[0] for p in sources if "/" in p}
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        for name in graph[path]:
            target = module_path(name)
            if target in sources:
                todo.append(target)
            elif name.split(".")[0] in project_roots:
                missing.add(name)
    return seen, sorted(missing)


data = json.loads((HERE / "correspondence-data.json").read_text())
assert data["snapshot"] == SNAPSHOT
doc = (HERE / "fdsa-sorting.md").read_text()
sources = sources_at(SNAPSHOT)
accepted_sources = sources_at(ACCEPTED)
aliases = {a["alias"]: a for a in data["aliases"]}
missing_alias_paths = [a["path"] for a in aliases.values() if a["path"] not in sources]
assert not missing_alias_paths
known = {k: set(DECL.findall(remove_comments(sources[a["path"]].decode()))) for k, a in aliases.items()}
refs = []
missing_refs = []
for match in re.finditer(r"\b(" + "|".join(sorted(aliases, key=len, reverse=True)) + r")\.([A-Za-z_][A-Za-z0-9_'?]*)", doc):
    alias, name = match.groups()
    entry = {"reference": alias + "." + name, "path": aliases[alias]["path"], "line": doc.count("\n", 0, match.start()) + 1}
    refs.append(entry)
    if name not in known[alias] and not any(n.endswith("." + name) for n in known[alias]):
        missing_refs.append(entry)
ids = re.findall(r"(?m)^\| (C02-\d{3}) \|", doc)
expected_ids = [f"C02-{i:03}" for i in range(1, 113)]
proposal = HERE / "public-example-imports.lean"
new_imports = imports(proposal.read_text()) if proposal.exists() else []
before, missing_before = closure(sources, [])
after, missing_after = closure(sources, new_imports)
accepted_reached, accepted_missing = closure(accepted_sources, [])
unreached = set(sources) - after
accepted_unreached = set(accepted_sources) - accepted_reached
identity_changes = [p for p in sorted(unreached & accepted_unreached) if sources[p] != accepted_sources[p]]
root_names = {p: imports(sources[p].decode()) for p in ("SquareApplications.lean", "ProofAudit.lean")}
report = {
    "status": "static source/reference/import check only; no Lean invocation, elaboration, audit or acceptance",
    "snapshot": SNAPSHOT,
    "accepted_reference": ACCEPTED,
    "doc_sha256": hashlib.sha256(doc.encode()).hexdigest(),
    "aliases": len(aliases),
    "obligation_rows": len(ids),
    "exact_ordered_ids": ids == expected_ids,
    "unique_ids": len(set(ids)),
    "explicit_alias_references": len(refs),
    "unique_alias_references": len({r["reference"] for r in refs}),
    "missing_alias_references": missing_refs,
    "proposal_present": proposal.exists(),
    "proposed_imports": new_imports,
    "proposed_import_count": len(new_imports),
    "proposed_imports_unique": len(new_imports) == len(set(new_imports)),
    "missing_import_files": [n for n in new_imports if module_path(n) not in sources],
    "already_direct_in_roots": {p: sorted(set(new_imports) & set(ns)) for p, ns in root_names.items()},
    "static_import_closure": {
        "candidate_tracked_lean": len(sources),
        "candidate_current_roots": len(before),
        "candidate_proposed_roots": len(after),
        "candidate_unreached": len(unreached),
        "accepted_tracked_lean": len(accepted_sources),
        "accepted_roots": len(accepted_reached),
        "accepted_unreached": len(accepted_unreached),
        "unreached_path_sets_match": unreached == accepted_unreached,
        "unreached_bytes_changed": identity_changes,
        "missing_project_imports_before": missing_before,
        "missing_project_imports_after": missing_after,
        "missing_project_imports_accepted": accepted_missing,
        "candidate_unreached_paths": sorted(unreached),
    },
    "source_identity": {a["path"]: {"bytes": len(sources[a["path"]]), "sha256": hashlib.sha256(sources[a["path"]]).hexdigest()} for a in aliases.values()},
    "limits": ["Source-name parser is not Lean elaboration.", "Grouped unqualified names require full manual readback.", "Import closure is textual project source reachability, not compiled module or declaration counts.", "No mutation of either root file or candidate source."],
}
(HERE / "static-check.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ("obligation_rows", "exact_ordered_ids", "explicit_alias_references", "unique_alias_references", "missing_alias_references", "proposed_import_count", "missing_import_files")}, indent=2))

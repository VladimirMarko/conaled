#!/usr/bin/env python3
"""Inventory the pinned official VFA sources without copying their prose.

This is a lexical coverage aid, not a Rocq parser or proof checker. Nested
comments and strings are respected. Every named declaration, exercise marker,
anonymous goal, module boundary, and proof terminator is retained by line.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

CHAPTERS = ["Preface", "Perm", "Sort", "Multiset", "BagPerm", "Selection", "Merge",
            "Maps", "SearchTree", "ADT", "Extract", "Redblack", "Trie", "Priqueue",
            "Binom", "Decide", "Color"]
VERSION = "2.1 (2026-08-24 10:11, Coq 9.0.0 or later)"
BASE_URL = "https://softwarefoundations.cis.upenn.edu/vfa-current/"
DECL = re.compile(r"^(?:(Fail|Local|Global|Program|Polymorphic|Monomorphic)\s+)*"
                  r"(Definition|Fixpoint|CoFixpoint|Function|Inductive|CoInductive|"
                  r"Record|Structure|Class|Instance|Theorem|Lemma|Corollary|Proposition|"
                  r"Fact|Remark|Example|Axiom|Axioms|Parameter|Parameters|Variable|Variables|"
                  r"Hypothesis|Hypotheses|Let|Ltac)\s+([\w']+)")
PROOFS = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Example"}
ASSUMPTIONS = {"Axiom", "Axioms", "Parameter", "Parameters", "Variable", "Variables",
               "Hypothesis", "Hypotheses"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mask_comments(text: str) -> tuple[str, list[dict]]:
    chars = list(text)
    comments = []
    i = 0
    while i < len(text):
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '"':
                    if text[i:i + 2] == '""':
                        i += 2
                    else:
                        i += 1
                        break
                else:
                    i += 1
        elif text[i:i + 2] == "(*":
            start = i
            depth = 1
            i += 2
            while depth:
                if i >= len(text):
                    raise ValueError("unclosed comment")
                if text[i:i + 2] == "(*":
                    depth += 1
                    i += 2
                elif text[i:i + 2] == "*)":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            comments.append({"start": start, "end": i, "text": text[start:i]})
            for j in range(start, i):
                if chars[j] != "\n":
                    chars[j] = " "
        else:
            i += 1
    return "".join(chars), comments


def commands(code: str):
    start = 0
    i = 0
    while i < len(code):
        if code[i] == '"':
            i += 1
            while i < len(code):
                if code[i] == '"':
                    if code[i:i + 2] == '""':
                        i += 2
                    else:
                        i += 1
                        break
                else:
                    i += 1
        elif code[i] == "." and (i + 1 == len(code) or code[i + 1].isspace()):
            raw = code[start:i + 1]
            if raw.strip():
                leading = len(raw) - len(raw.lstrip())
                yield start + leading, i + 1, raw.strip()
            start = i + 1
            i += 1
        else:
            i += 1
    if code[start:].strip():
        raise ValueError("unterminated final command")


def inventory(chapter: str, source: Path) -> dict:
    path = source / (chapter + ".v")
    text = path.read_text()
    code, comments = mask_comments(text)
    line = lambda offset: text.count("\n", 0, offset) + 1
    exercises = []
    exercise_re = re.compile(r"\*{4}\s*Exercise:\s*(\d+)\s+stars?,\s*([^()]*?)\(([^)]+)\)")
    for idx, comment in enumerate(comments):
        match = exercise_re.search(comment["text"])
        if not match:
            continue
        end = len(text)
        for following in comments[idx + 1:]:
            if re.fullmatch(r"\(\*\*\s*\[\]\s*\*\)", following["text"]):
                end = following["end"]
                break
            if exercise_re.search(following["text"]):
                end = following["start"]
                break
        tags = [s.strip() for s in match.group(2).split(",") if s.strip()]
        exercises.append({"name": match.group(3), "stars": int(match.group(1)),
                          "tags": tags, "optional": "optional" in tags,
                          "advanced": "advanced" in tags,
                          "start_line": line(comment["start"]), "end_line": line(end),
                          "_start": comment["start"], "_end": end,
                          "declaration_ids": [], "coverage_status": "pending"})
    declarations = []
    modules = []
    scope = []
    pedagogical_commands = []
    current = None
    proof_ends = Counter()
    for start, end, command in commands(code):
        match = re.match(r"^Module\s+(Type\s+)?([\w']+)\b", command)
        if match:
            is_alias = ":=" in command
            modules.append({"name": match.group(2), "kind": "module_type" if match.group(1) else "module",
                            "line": line(start), "alias": is_alias})
            if not is_alias:
                scope.append((match.group(2), bool(match.group(1))))
            current = None
            continue
        match = re.match(r"^End\s+([\w']+)\s*\.", command)
        if match:
            if scope and scope[-1][0] == match.group(1):
                scope.pop()
            current = None
            continue
        match = DECL.match(command)
        is_goal = bool(re.match(r"^Goal\b", command))
        if match or is_goal:
            kind = match.group(2) if match else "Goal"
            name = match.group(3) if match else f"goal_at_line_{line(start)}"
            failed = command.startswith("Fail ")
            qualified = ".".join([chapter] + [name for name, _ in scope] + [name])
            in_module_type = any(flag for _, flag in scope)
            if failed:
                status = "expected_command_failure"
            elif kind in ASSUMPTIONS:
                status = "interface_requirement" if in_module_type else "source_assumption"
            elif name.startswith("manual_grade_for_"):
                status = "grading_metadata"
            elif kind == "Ltac":
                status = "coq_tactic_definition"
            elif kind in PROOFS or kind == "Goal":
                status = "proved_by_term_in_source" if ":=" in command else "pending_proof_terminator"
            else:
                status = "definition"
            record = {"id": f"{qualified}@{line(start)}", "name": name,
                      "qualified_name": qualified, "kind": kind,
                      "start_line": line(start), "statement_end_line": line(end),
                      "source_status": status, "module_type_context": in_module_type,
                      "coverage_status": "pending", "lean_targets": []}
            for ex in exercises:
                if ex["_start"] <= start < ex["_end"]:
                    record["exercise"] = ex["name"]
                    ex["declaration_ids"].append(record["id"])
            declarations.append(record)
            current = record if not failed and kind not in ASSUMPTIONS and kind != "Ltac" else None
            continue
        ending = re.match(r"^(?:[-+*{}]\s*)*(Qed|Defined|Admitted|Abort)\s*\.", command)
        if ending:
            terminator = ending.group(1)
            proof_ends[terminator] += 1
            if current is None:
                raise ValueError(f"{chapter}:{line(start)} unmatched {terminator}")
            current["proof_end_line"] = line(start)
            current["source_terminator"] = terminator
            current["source_status"] = {"Qed": "proved_in_source", "Defined": "proved_transparent_in_source",
                                        "Admitted": "source_admission", "Abort": "pedagogical_abort"}[terminator]
            current = None
            continue
        if re.match(r"^(Check|Print|Search|Locate|Compute|Eval|Extraction|Recursive Extraction|Extract|Fail)\b", command):
            pedagogical_commands.append({"line": line(start), "command_kind": command.split()[0]})
    for declaration in declarations:
        if declaration["source_status"] == "pending_proof_terminator":
            raise ValueError(f"{declaration['id']}: unmatched declaration proof")
        if declaration["source_status"] == "pedagogical_abort":
            later = [d for d in declarations if d["qualified_name"] == declaration["qualified_name"]
                     and d["start_line"] > declaration["start_line"]
                     and d["source_status"] != "pedagogical_abort"]
            if later:
                declaration["abort_classification"] = "abandoned_attempt_with_later_declaration"
                declaration["replacement_source_id"] = later[0]["id"]
            else:
                declaration["abort_classification"] = "pedagogical_attempt_requires_individual_review"
    for exercise in exercises:
        del exercise["_start"]
        del exercise["_end"]
        exercise["has_named_declarations"] = bool(exercise["declaration_ids"])
    return {"chapter": chapter, "order": CHAPTERS.index(chapter),
            "source_file": chapter + ".v", "sha256": sha(path), "size_bytes": path.stat().st_size,
            "source_url": BASE_URL + chapter + ".html", "version": VERSION,
            "line_count": len(text.splitlines()), "coverage_status": "pending",
            "declarations": declarations, "exercises": exercises, "modules": modules,
            "pedagogical_commands": pedagogical_commands,
            "counts": {"declarations": len(declarations), "exercises": len(exercises),
                       "source_status": dict(Counter(d["source_status"] for d in declarations)),
                       "proof_terminators": dict(proof_ends)}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--archive", type=Path)
    args = parser.parse_args()
    chapters = [inventory(chapter, args.source) for chapter in CHAPTERS]
    # These are pedagogical failures, not missing claims to assume in Lean.
    abort_notes = {
        ("Merge", "split_len_first_try"): ("true_statement_inadequate_induction", "Covered by the successful split length theorem and an explanation of two-step induction."),
        ("SearchTree", "elements_complete_broken"): ("false_specification", "Refute using an empty tree and lookup's default value; do not assert the broken completeness specification."),
        ("Decide", "compute_with_lt_dec"): ("opaque_decision_procedure_computation_example", "Prove the mathematical result using decision correctness, and explicitly explain Lean's corresponding computation/proof boundary."),
    }
    for chapter in chapters:
        for declaration in chapter["declarations"]:
            key = (chapter["chapter"], declaration["name"])
            if declaration["source_status"] == "pedagogical_abort" and key in abort_notes:
                classification, note = abort_notes[key]
                declaration["abort_classification"] = classification
                declaration["coverage_obligation"] = note
            if declaration["qualified_name"] == "ADT.TreeETable_first_attempt.elements_correct":
                declaration["semantic_role"] = "pedagogical_invalid_contract"
                declaration["coverage_obligation"] = "Supply a malformed-tree counterexample and the corrected invariant-bearing ETable contract; this intentionally unsuccessful source admission must not become a Lean axiom."
    result = {"schema_version": 1, "inventory_date": "2026-11-02", "source": {
        "title": "Verified Functional Algorithms", "author": "Andrew W. Appel",
        "series": "Software Foundations", "volume": 3, "version": VERSION,
        "index_url": BASE_URL + "index.html", "toc_url": BASE_URL + "toc.html",
        "archive_url": BASE_URL + "vfa.tgz", "archive_sha256": sha(args.archive) if args.archive else None,
        "license": "MIT", "license_sha256": sha(args.source / "LICENSE"),
        "copyright_notice": "Copyright (c) 2026"},
        "scope": {"chapter_order": CHAPTERS, "includes_optional_and_advanced": True,
                  "includes_exercises": True, "preface_is_nonformal": True,
                  "coq_mechanics": "Explicitly map to appropriate Lean techniques; do not copy global source axioms.",
                  "algorithm_identity": "Preserve source algorithms or prove an explicitly scoped refinement bridge.",
                  "parser_limit": "Lexical reconnaissance, not a Rocq AST or proof validation; names, nested module qualification and exercises require review when implementing."},
        "chapters": chapters}
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "vfa-source-inventory.json").write_text(json.dumps(result, indent=2) + "\n")
    for chapter in chapters:
        (args.output / (chapter["chapter"] + ".inventory.json")).write_text(json.dumps(chapter, indent=2) + "\n")
    print(json.dumps({"chapters": [{"chapter": c["chapter"], **c["counts"]} for c in chapters]}, indent=2))


if __name__ == "__main__":
    main()

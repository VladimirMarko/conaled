#!/usr/bin/env python3
"""Independent finite-state reference traces for frozen delimiter fixtures.

This reads no Lean file and invokes no compiler. It interprets the phase/action
table fixed in EXPECTATIONS.md, stopping before the old controller starts.
The literal expected counts, frames and peaks below are fixed independently
from this interpreter. Its successful checks are design evidence only.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

# Each row contains literal expectations, not counts returned by the model.
ROWS = [
    ("empty_missing", "", "", 2, 0, False, False),
    ("delimiter_only", "#", "1", 4, 1, False, True),
    ("prefix_false", "0#", "001", 7, 3, False, True),
    ("prefix_true", "1#", "011", 7, 3, False, True),
    ("certificate_false", "#0", "10", 6, 2, False, True),
    ("certificate_true", "#1", "11", 6, 2, False, True),
    ("two_certificate_bits", "#01", "101", 8, 3, False, True),
    ("mixed_valid", "10#01", "0100101", 14, 7, False, True),
    ("missing_false", "0", "", 5, 2, False, False),
    ("missing_true", "1", "", 5, 2, False, False),
    ("missing_mixed", "10", "", 8, 4, False, False),
    ("repeated_empty", "##", "", 5, 2, False, False),
    ("repeated_tail", "##0", "", 6, 3, False, False),
    ("repeated_mixed", "1#0#1", "", 11, 6, False, False),
    ("repeated_tail_has_delimiter", "#1##0", "", 9, 5, False, False),
    ("mixed_valid_initial_true", "10#01", "0100101", 14, 7, True, True),
    ("repeated_mixed_initial_true", "1#0#1", "", 11, 6, True, False),
]


def raw_letters(word):
    return [None if x == "#" else x == "1" for x in word]


def bits(word):
    return [x == "1" for x in word]


def scratch_of_letter(letter):
    return "delimiter" if letter is None else "bit_true" if letter else "bit_false"


def trace(raw, initial):
    phase, scratch = "prefix", "empty"
    remaining, work, framed = list(raw), [], []
    states = []

    def boundary():
        states.append({
            "step": len(states), "phase": phase,
            "registers": {
                "old_all_eight_temporary_fields": "empty",
                "scratch": scratch, "base_user": initial,
            },
            "caller_input": list(remaining), "caller_work": list(work),
            "framedRaw": list(framed), "other_fifteen_old_stores": "empty",
            "total_stack_cells": len(remaining) + len(work) + len(framed),
        })

    boundary()
    while phase != "old_controller_main":
        if phase in ("prefix", "certificate", "drainInput"):
            occupied = bool(remaining)
            letter = remaining.pop(0) if occupied else None
            scratch = scratch_of_letter(letter) if occupied else "empty"
            if phase == "prefix":
                if not occupied:
                    phase = "drainWork"
                elif letter is None:
                    work.insert(0, True)
                    phase = "certificate"
                else:
                    work.insert(0, False)
                    work.insert(0, letter)
            elif phase == "certificate":
                if not occupied:
                    phase = "reverse"
                elif letter is None:
                    phase = "drainInput"
                else:
                    work.insert(0, letter)
            elif not occupied:
                phase = "drainWork"
        else:
            occupied = bool(work)
            letter = work.pop(0) if occupied else None
            scratch = scratch_of_letter(letter) if occupied else "empty"
            if occupied:
                if phase == "reverse":
                    framed.insert(0, letter)
            else:
                scratch = "empty"
                phase = "old_controller_main"
        boundary()
    return states


def write_new(name, value):
    with (ROOT / name).open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def descriptor(name):
    raw = (ROOT / name).read_bytes()
    return {"path": name, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


fixtures, traces = [], []
for name, raw, framed, steps, peak, initial, valid in ROWS:
    fixture = {
        "name": name, "raw_notation": raw, "raw": raw_letters(raw),
        "expected_frame_notation": framed, "expected_frame": bits(framed),
        "expected_steps": steps, "expected_peak_cells": peak,
        "initial_user": initial, "delimiter_valid": valid,
        "expected_final_caller_input": [], "expected_final_caller_work": [],
        "expected_final_scratch": "empty",
    }
    states = trace(fixture["raw"], initial)
    assert len(states) - 1 == steps, name
    assert max(state["total_stack_cells"] for state in states) == peak, name
    assert states[-1]["framedRaw"] == fixture["expected_frame"], name
    assert not states[-1]["caller_input"] and not states[-1]["caller_work"], name
    assert all(state["registers"]["base_user"] == initial for state in states), name
    assert states[-1]["registers"]["scratch"] == "empty", name
    assert steps <= 3 * len(raw) + 2, name
    assert peak <= 2 * len(raw), name
    fixtures.append(fixture)
    traces.append({"fixture": name, "boundaries": states})

write_new("FIXTURES.json", {"schema": "delimiter-prelude-fixed-cases-v1", "fixtures": fixtures})
write_new("INDEPENDENT-TRACES.json", {"schema": "delimiter-prelude-reference-traces-v1", "traces": traces})
write_new("EXPECTATIONS-STATUS.json", {
    "schema": "delimiter-prelude-expectations-freeze-v1",
    "frozen_utc": datetime.now(timezone.utc).isoformat(),
    "compiler_run": False, "lean_draft_written_before_freeze": False,
    "actual_installed_source_or_outputs_changed": False,
    "reference_model_checked_fixed_cases": len(fixtures),
    "boundary": "Independent phase/action model only; no theorem or actual Lean-machine execution is certified.",
    "artifacts": [descriptor(name) for name in [
        "EXPECTATIONS.md", "FIXTURES.json", "INDEPENDENT-TRACES.json", "derive_traces.py"]],
})
print(json.dumps({"fixed_cases": len(fixtures), "frozen": descriptor("EXPECTATIONS-STATUS.json")}))

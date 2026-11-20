#!/usr/bin/env python3
"""Public-command regression checks for the Extract textbook adaptation.

Set EXTRACT_TEST_COMMAND_JSON to the actual launch argv to run the same checks
against a standalone executable. The default invokes Lean's direct runner.
No process limits or performance thresholds are imposed by these checks.
Use --check-receipt FILE to independently validate a saved driver observation.
"""

import datetime
import copy
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import unittest

# Match Lean's unbounded Int/Nat interface rather than adding Python's default
# decimal-conversion digit limit to receipt validation.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


COMMAND = json.loads(os.environ.get(
    "EXTRACT_TEST_COMMAND_JSON",
    '["lake", "env", "lean", "--run", "scripts/ExtractSearchTree.lean"]',
))
if not isinstance(COMMAND, list) or not COMMAND or not all(
    isinstance(part, str) and part for part in COMMAND
):
    raise SystemExit("EXTRACT_TEST_COMMAND_JSON must be a nonempty argv array")


def expected_examples():
    """Independent literal/Python expectations for the fixed public examples."""
    def sorting(values):
        return {"input": list(map(str, values)), "output": list(map(str, sorted(values)))}

    finite = []
    for carrier, width in (("word63", 63), ("int64", 64)):
        minimum, maximum = -(1 << (width - 1)), (1 << (width - 1)) - 1
        finite.append({"carrier": carrier, "width": width, "minimum": str(minimum),
                       "maximum": str(maximum), **sorting([-1, maximum, minimum, 0, -1])})
    comparisons = []
    for carrier, exponent in (("int", 70), ("word63", 62), ("int64", 63)):
        endpoints = (-(1 << exponent), (1 << exponent) - 1)
        comparisons.append({"carrier": carrier, "cases": [
            {"left": str(left), "right": str(right), "lt": left < right, "le": left <= right}
            for left, right in [(-3, 0), (0, 0), (4, -1), endpoints, endpoints[::-1]]]})
    entries = [["-3", 9], ["0", 0], ["4", 8]]
    return {
        "schema": 1, "kind": "examples", "sortZ": sorting([-3, 2, -3, 0, 1]),
        "sortZBoundary": [sorting([]), sorting([-7])],
        "natSort": [sorting(values) for values in ([], [7], [4, 3, 2, 1], [3, 1, 3, 0, 1])],
        "finiteSort": finite,
        "stableSort": [{"carrier": carrier,
                        "input": [["2", "first"], ["1", "middle"], ["2", "last"]],
                        "output": [["1", "middle"], ["2", "first"], ["2", "last"]]}
                       for carrier in ("int", "word63", "int64")],
        "comparisons": comparisons,
        "fourBitComparison": {"left": "-1", "right": "0", "signedLt": True, "unsignedLt": False},
        "tables": [{"carrier": carrier, "writes": [["-3", 7], ["4", 8], ["-3", 9], ["0", 0]],
                    "queries": ["-3", "4", "0", "-1"], "optional": [9, 8, 0, None],
                    "default0": [9, 8, 0, 0], "default99": [9, 8, 0, 99],
                    "entries": entries, "withSuffix": entries + [["99", 123]],
                    "empty": {"entries": [], "optional": None, "default": 99}}
                   for carrier in ("int", "word63", "int64")],
        "wordBoundaries": {
            "overflow": {"width": 4, "left": "7", "right": "1", "sum": "-8",
                         "mathematicalSum": "8", "overflow": True},
            "safe": {"width": 4, "left": "2", "right": "1", "sum": "3",
                     "mathematicalSum": "3", "overflow": False},
            "zeroWidth": {"sourceIntegers": ["-3", "4", "99"], "decodedKeys": ["0", "0", "0"],
                          "strict": False, "nonstrict": True, "entries": [["0", 9]],
                          "optional": 9, "default99": 9},
        },
    }


def expected_redblack_examples():
    # The last write of zero rotates the two-child history to black root 0
    # with black children -3/4. A stored zero remains distinct from the miss -1.
    tree = {
        "nodes": 3, "height": 2, "bst": True,
        "redblack": {"rootBlack": True, "noRedRed": True, "equalBlackHeight": True,
                     "blackHeight": 2, "logHeightBound": True},
        "preorder": [["black", "0", 0], ["black", "-3", 9], None, None,
                     ["black", "4", 8], None, None],
    }
    return {"schema": 2, "kind": "redblack-examples",
            "tables": [{"observations": table, "tree": copy.deepcopy(tree)}
                       for table in expected_examples()["tables"]],
            "invariantCounterexamples": expected_invariant_counterexamples()}


def expected_invariant_counterexamples():
    def case(name, preorder, entries, nodes, height, bst, root_black, no_red_red, black_height):
        return {"name": name, "publicTreeAccepted": False, "entries": entries,
                "tree": {"nodes": nodes, "height": height, "bst": bst, "preorder": preorder,
                         "redblack": {"rootBlack": root_black, "noRedRed": no_red_red,
                                      "equalBlackHeight": black_height is not None,
                                      "blackHeight": black_height, "logHeightBound": True}}}

    return [
        case("deep-key-outside-bound",
             [["black", "0", 1], ["black", "-2", 1], None, ["red", "1", 1], None, None,
              ["black", "2", 1], None, None],
             [["-2", 1], ["1", 1], ["0", 1], ["2", 1]], 4, 3, False, True, True, 2),
        case("red-red",
             [["black", "0", 1], ["red", "-2", 1], ["red", "-3", 1], None, None, None, None],
             [["-3", 1], ["-2", 1], ["0", 1]], 3, 3, True, True, False, 1),
        case("unequal-black-height", [["black", "0", 1], ["black", "-1", 1], None, None, None],
             [["-1", 1], ["0", 1]], 2, 2, True, True, True, None),
        case("red-root", [["red", "0", 1], None, None], [["0", 1]], 1, 1, True, False, True, 0),
    ]


def typed_json(value):
    # Encoding keeps True distinct from 1 and 1.0 distinct from an integer.
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def object_fields(value, fields, label):
    require(isinstance(value, dict) and set(value) == set(fields.split()),
            f"{label}: missing or unexpected members")


def natural(value, label):
    require(type(value) is int and value >= 0, f"{label}: expected a natural-number integer")
    return value


def key_list(value, carrier, label):
    require(isinstance(value, list), f"{label}: expected a list of decimal keys")
    result = []
    for text in value:
        require(isinstance(text, str) and re.fullmatch(r"0|-?[1-9][0-9]*", text) is not None,
                f"{label}: key is not a canonical decimal string")
        key = int(text)
        if carrier != "int":
            limit = 1 << (62 if carrier == "word63" else 63)
            require(-limit <= key < limit, f"{label}: key is outside the signed carrier range")
        result.append(key)
    return result


def check_tree_observation(tree, carrier, realization, entries, require_valid=True):
    """Reconstruct observations from raw preorder; never replay insertion.

    An explicit stack avoids imposing a recursion-depth cap on ordinary chains.
    The token stream is an observation of an actual runtime tree. Authenticity
    still belongs to the separately retained command/source/executable receipt.
    """
    object_fields(tree, "nodes height bst redblack preorder", "tree")
    tokens = tree["preorder"]
    require(isinstance(tokens, list), "tree.preorder must be a flat token list")
    empty = {"nodes": 0, "height": 0, "minimum": None, "maximum": None,
             "bst": True, "root": None, "noRedRed": True, "blackHeight": 0, "index": None}
    stack, nodes = [], []
    for token in reversed(tokens):
        if token is None:
            stack.append(empty)
            continue
        require(isinstance(token, list) and len(token) == 3, "invalid node token")
        color, text, payload = token
        require(color is None if realization == "ordinary" else color in ("red", "black"),
                "node color differs from the selected realization")
        key = key_list([text], carrier, "tree.preorder")[0]
        natural(payload, "tree.preorder payload")
        require(len(stack) >= 2, "preorder node is missing a child")
        left, right = stack.pop(), stack.pop()
        bst = (left["bst"] and right["bst"]
               and (left["maximum"] is None or left["maximum"] < key)
               and (right["minimum"] is None or key < right["minimum"]))
        common = left["blackHeight"]
        black_height = (common + (1 if color == "black" else 0)
                        if common is not None and common == right["blackHeight"] else None)
        node = {"key": key, "payload": payload, "left": left["index"], "right": right["index"]}
        index = len(nodes)
        nodes.append(node)
        stack.append({
            "nodes": left["nodes"] + right["nodes"] + 1,
            "height": max(left["height"], right["height"]) + 1,
            "minimum": min(key, left["minimum"] if left["minimum"] is not None else key,
                           right["minimum"] if right["minimum"] is not None else key),
            "maximum": max(key, left["maximum"] if left["maximum"] is not None else key,
                           right["maximum"] if right["maximum"] is not None else key),
            "bst": bst, "root": color,
            "noRedRed": (left["noRedRed"] and right["noRedRed"]
                         and (color != "red" or (left["root"] != "red" and right["root"] != "red"))),
            "blackHeight": black_height, "index": index,
        })
    require(len(stack) == 1, "preorder must describe exactly one complete tree")
    actual = stack[0]
    require(natural(tree["nodes"], "tree.nodes") == actual["nodes"], "node count differs from preorder")
    require(natural(tree["height"], "tree.height") == actual["height"], "height differs from preorder")
    require(type(tree["bst"]) is bool and tree["bst"] == actual["bst"], "BST observation differs from preorder")
    if realization == "ordinary":
        require(tree["redblack"] is None, "ordinary tree cannot claim colored invariants")
    else:
        expected_rb = {
            "rootBlack": actual["index"] is None or actual["root"] == "black",
            "noRedRed": actual["noRedRed"], "equalBlackHeight": actual["blackHeight"] is not None,
            "blackHeight": actual["blackHeight"],
            "logHeightBound": actual["height"] <= 2 * ((actual["nodes"] + 1).bit_length() - 1),
        }
        require(typed_json(tree["redblack"]) == typed_json(expected_rb), "red-black observations differ from preorder")
        if require_valid:
            require(all(expected_rb[k] for k in ("rootBlack", "noRedRed", "equalBlackHeight", "logHeightBound")),
                    "workload tree violates a required red-black invariant")
    if require_valid:
        require(actual["bst"], "workload tree violates all-descendant ordering")
    ordered_entries, path, current = [], [], actual["index"]
    while current is not None or path:
        while current is not None:
            path.append(current)
            current = nodes[current]["left"]
        current = path.pop()
        node = nodes[current]
        ordered_entries.append([str(node["key"]), node["payload"]])
        current = node["right"]
    require(typed_json(ordered_entries) == typed_json(entries), "preorder bindings differ from the complete enumeration")


def check_workload(receipt):
    """Check recorded observations with Python's independent integer dictionary.

    This checks consistency and the pinned known stream, not arbitrary PRNG
    provenance, the authenticity of clock readings, or the origin of a file.
    The external execution receipt separately binds actual commands/input bytes.
    """
    object_fields(receipt, "schema kind config clock unit timedRegion samples", "workload")
    config = receipt["config"]
    current = receipt["schema"] == 2
    object_fields(config, "carrier pattern timing size queries universe seed warmups repetitions insertedFile queriesFile"
                  + (" realization" if current else ""), "config")
    realization = config["realization"] if current else "ordinary"
    require(realization in ("ordinary", "redblack"), "unsupported realization")
    carrier, pattern, timing = config["carrier"], config["pattern"], config["timing"]
    require(carrier in ("int", "word63", "int64"), "unsupported carrier")
    require(pattern in ("consecutive", "random", "replay"), "unsupported pattern")
    require(timing in ("controlled", "source"), "unsupported timing")
    for field in ("size", "queries", "warmups", "repetitions"):
        natural(config[field], f"config.{field}")
    require(config["repetitions"] > 0, "at least one measured repetition is required")
    size, count = config["size"], config["queries"]
    if timing == "source":
        require(size == count, "source timing requires equal construction and query counts")
    if pattern == "replay":
        require(timing == "controlled" and config["seed"] is None and config["universe"] is None,
                "replay must have controlled timing and no generator settings")
        require(all(isinstance(config[field], str) and config[field] for field in ("insertedFile", "queriesFile")),
                "replay must retain both input filenames")
    else:
        natural(config["seed"], "config.seed")
        natural(config["universe"], "config.universe")
        require(config["insertedFile"] is None and config["queriesFile"] is None,
                "generated workloads cannot have input filenames")
        if pattern == "random":
            require(config["universe"] > 0 or size == count == 0, "random draws need a positive universe")
        if carrier != "int":
            limit = 1 << (62 if carrier == "word63" else 63)
            require((size <= limit and count <= limit) if pattern == "consecutive" else config["universe"] <= limit,
                    "generated key domain exceeds the signed positive capacity")
    require(receipt["clock"] == "IO.monoNanosNow" and receipt["unit"] == "ns", "unexpected clock or unit")
    region = ("precomputed queries: traversal, lookup, hit count" if timing == "controlled" else
              "generated queries: descending schedule creation/traversal, key generation, checked conversion, lookup, hit count")
    require(receipt["timedRegion"] == region, "timed region differs from the selected mode")
    samples = receipt["samples"]
    require(isinstance(samples, list) and len(samples) == config["warmups"] + config["repetitions"],
            "sample count differs from warmups and repetitions")
    previous = None
    for position, sample in enumerate(samples):
        object_fields(sample, "phase index inserted queries entries queryOptions hits expectedHits distinct elapsedNs generator"
                      + (" tree" if current else ""), "sample")
        expected_phase = "warmup" if position < config["warmups"] else "measured"
        expected_index = position if expected_phase == "warmup" else position - config["warmups"]
        require(sample["phase"] == expected_phase and natural(sample["index"], "sample.index") == expected_index,
                "sample phase/index is out of sequence")
        natural(sample["elapsedNs"], "sample.elapsedNs")
        inserted, queries = [key_list(sample[field], carrier, f"sample.{field}") for field in ("inserted", "queries")]
        require(len(inserted) == size and len(queries) == count, "recorded input lengths differ from the configuration")
        if pattern == "consecutive":
            require(all(key == index for index, key in enumerate(inserted))
                    and all(key == index for index, key in enumerate(queries)), "consecutive keys differ from their prefixes")
        elif pattern == "random":
            require(all(0 <= key < config["universe"] for key in inserted + queries), "random key is outside its universe")
        model = dict.fromkeys(inserted, 1)
        entries = [[str(key), 1] for key in sorted(model)]
        options = [model.get(key) for key in queries]
        require(typed_json(sample["entries"]) == typed_json(entries), "entries differ from the independent canonical map")
        require(typed_json(sample["queryOptions"]) == typed_json(options), "optional results differ from the independent map")
        if current:
            check_tree_observation(sample["tree"], carrier, realization, entries)
        hits = options.count(1)
        for field, expected in (("hits", hits), ("expectedHits", hits), ("distinct", len(model))):
            require(natural(sample[field], f"sample.{field}") == expected, f"{field} differs from the independent map")
        generator = sample["generator"]
        if pattern == "replay":
            require(generator is None, "replay cannot report a generator")
        else:
            object_fields(generator, "name initial postBuild postQuery buildDraws queryDraws", "generator")
            require(generator["name"] == "StdGen/mkStdGen/randNat", "unexpected generator")
            for field in ("initial", "postBuild", "postQuery"):
                state = generator[field]
                require(isinstance(state, list) and len(state) == 2, "expected a two-component generator state")
                require(1 <= natural(state[0], field) <= 2147483562 and 1 <= natural(state[1], field) <= 2147483398,
                        "generator state is outside the pinned StdGen ranges")
            seed = config["seed"]
            initial = [seed % 2147483562 + 1, (seed // 2147483562) % 2147483398 + 1]
            require(generator["initial"] == initial, "initial state differs from the recorded seed")
            for field, expected in (("buildDraws", size if pattern == "random" else 0),
                                    ("queryDraws", count if pattern == "random" else 0)):
                require(natural(generator[field], field) == expected, "logical key draw count is incorrect")
            if generator["buildDraws"] == 0:
                require(generator["postBuild"] == initial, "zero-draw construction changed generator state")
            if generator["queryDraws"] == 0:
                require(generator["postQuery"] == generator["postBuild"], "zero-draw queries changed generator state")
            if pattern == "random" and (seed, config["universe"], size, count) == (1729, 13, 8, 8):
                require(inserted == [10, 0, 10, 11, 6, 10, 0, 0] and queries == [9, 7, 4, 11, 1, 8, 11, 8]
                        and generator["postBuild"] == [1689113473, 525453832]
                        and generator["postQuery"] == [1827515937, 1554910725],
                        "observations differ from the independently pinned StdGen stream")
        repeatable = typed_json({key: value for key, value in sample.items() if key not in ("phase", "index", "elapsedNs")})
        require(previous is None or repeatable == previous, "samples do not reproduce the same reset inputs and results")
        previous = repeatable
    return {"schema": 1, "status": "accepted", "kind": "workload", "samples": len(samples)}


def check_binomial_state(state, implementation, expected, expected_slots, label):
    """Check a finite raw observation; no linking/insertion algorithm is replayed."""
    object_fields(state, "contents slots forest", label)
    contents = key_list(state["contents"], "int64", label + ".contents")
    require(Counter(contents) == Counter(expected), label + ": occurrence model differs")
    if implementation == "list":
        require(state["slots"] is None and state["forest"] is None,
                label + ": list observation cannot report a tree forest")
        return
    slots = natural(state["slots"], label + ".slots")
    require(slots == expected_slots, label + ": retained slot capacity differs")
    forest = state["forest"]
    require(isinstance(forest, list) and len(forest) == slots, label + ": forest length differs")
    observed_contents = []
    for rank, tokens in enumerate(forest):
        require(isinstance(tokens, list), label + ": expected a flat preorder list")
        position = 0

        def parse_tree():
            nonlocal position
            require(position < len(tokens), label + ": incomplete tree observation")
            token = tokens[position]
            position += 1
            if token is None:
                return None
            key = key_list([token], "int64", label + ".forest.key")[0]
            observed_contents.append(key)
            return key, parse_tree(), parse_tree()

        tree = parse_tree()
        require(position == len(tokens), label + ": unused tree tokens")
        if tree is None:
            continue
        key, child, sibling = tree
        require(sibling is None, label + ": occupied slot has an outer right sibling")

        def check_children(node, remaining_rank, bound):
            if remaining_rank == 0:
                require(node is None, label + ": rank-zero child spine is not empty")
                return
            require(node is not None, label + ": child spine has insufficient rank")
            value, left, right = node
            require(value <= bound, label + ": heap bound is violated")
            check_children(left, remaining_rank - 1, value)
            check_children(right, remaining_rank - 1, bound)

        check_children(child, rank, key)
    require(contents == observed_contents, label + ": contents disagree with the raw forest")


def binomial_events(keys, schedule):
    """The public workload protocol, independent of either queue implementation."""
    insertions = [["insert", "main", str(key)] for key in keys]
    drain = [["delete", "main"] for _ in range(len(keys) + 1)]
    if schedule == "drain":
        return insertions + [["save", "built", "main"]] + drain
    if schedule == "mixed":
        events = []
        for key in keys:
            events.append(["insert", "main", str(key)])
            if key % 2 == 1:
                events.append(["delete", "main"])
        return events + [["save", "mixed-prefix", "main"]] + drain
    if schedule == "merge":
        return [["insert", "left" if index % 2 == 0 else "right", str(key)]
                for index, key in enumerate(keys)] + [
                    ["save", "left-before", "left"], ["save", "right-before", "right"],
                    ["merge", "main", "left", "right"], ["save", "merged", "main"],
                    ["delete", "left"], ["delete", "right"]] + drain
    if schedule == "padding":
        return insertions + [["save", "peak", "main"]] + drain + [
            ["save", "drained", "main"], ["insert", "main", "0"],
            ["delete", "main"], ["delete", "main"]]
    raise ValueError("unsupported queue schedule")


def check_binomial_workload(receipt):
    object_fields(receipt, "schema kind clock unit timedRegion config samples", "binomial workload")
    require(receipt["schema"] == 3, "binomial workload requires schema3")
    require(receipt["clock"] == "IO.monoNanosNow" and receipt["unit"] == "ns",
            "unexpected queue elapsed clock/unit")
    require(receipt["timedRegion"] ==
            "precomputed queue operations, persistent snapshots and result retention",
            "unexpected queue timing boundary")
    config = receipt["config"]
    object_fields(config, "implementation carrier pattern schedule size universe seed warmups repetitions keysFile",
                  "binomial config")
    implementation = config["implementation"]
    require(implementation in ("binomial", "list"), "unsupported queue implementation")
    require(config["carrier"] == "int64", "unsupported queue carrier")
    pattern = config["pattern"]
    require(pattern in ("random", "replay", "ascending", "descending", "equal") and
            config["schedule"] in ("drain", "mixed", "merge", "padding"),
            "unsupported queue input pattern or operation schedule")
    for field in ("size", "universe", "seed", "warmups", "repetitions"):
        natural(config[field], "config." + field)
    require(config["repetitions"] > 0, "queue repetitions must be positive")
    if pattern == "replay":
        require(config["universe"] == 32 and config["seed"] == 1729,
                "replay cannot override generator options")
        require(isinstance(config["keysFile"], str) and config["keysFile"], "replay requires a key file")
    elif pattern == "random":
        require(config["keysFile"] is None, "random generation cannot use a replay file")
        require(config["universe"] <= 1 << 63, "random universe exceeds the natural-key domain")
        require(config["size"] == 0 or config["universe"] > 0, "nonempty random input requires a positive universe")
    else:
        require(config["keysFile"] is None and config["universe"] == 32 and config["seed"] == 1729,
                "deterministic input cannot override generator or replay options")
        require(pattern == "equal" or config["size"] <= 1 << 63,
                "ordered input exceeds the natural-key domain")
    samples = receipt["samples"]
    require(isinstance(samples, list) and len(samples) == config["warmups"] + config["repetitions"],
            "queue sample count differs from the repetition policy")
    previous = None
    for position, sample in enumerate(samples):
        object_fields(sample, "phase index elapsedNs keys operations removals final saved generator", "queue sample")
        phase, index = (("warmup", position) if position < config["warmups"]
                        else ("measured", position - config["warmups"]))
        require(sample["phase"] == phase and natural(sample["index"], "sample.index") == index,
                "queue phase or index differs")
        natural(sample["elapsedNs"], "sample.elapsedNs")
        keys = key_list(sample["keys"], "int64", "sample.keys")
        require(len(keys) == config["size"], "queue key count differs from config")
        if pattern == "random":
            require(all(0 <= key < config["universe"] for key in keys), "generated key is outside its natural universe")
        elif pattern != "replay":
            ordered = list(range(len(keys)))
            expected = ordered if pattern == "ascending" else ordered[::-1] if pattern == "descending" else [0] * len(keys)
            require(keys == expected, "deterministic keys differ from the complete input pattern")
        events = binomial_events(keys, config["schedule"])
        require(typed_json(sample["operations"]) == typed_json(events), "queue schedule differs from input")
        model = {name: [] for name in ("main", "left", "right")}
        slots = dict.fromkeys(model, 0)
        expected_removals, expected_saved = [], []
        for event_index, event in enumerate(events):
            if event[0] == "insert":
                model[event[1]].append(int(event[2]))
                slots[event[1]] = max(slots[event[1]], len(model[event[1]]).bit_length())
            elif event[0] == "delete":
                key = max(model[event[1]]) if model[event[1]] else None
                if key is not None:
                    model[event[1]].remove(key)
                expected_removals.append([event_index, event[1], None if key is None else str(key)])
            elif event[0] == "merge":
                model[event[1]] = model[event[2]] + model[event[3]]
                slots[event[1]] = max(slots[event[2]], slots[event[3]], len(model[event[1]]).bit_length())
            else:
                expected_saved.append((event[1], event[2], model[event[2]].copy(), slots[event[2]]))
        require(typed_json(sample["removals"]) == typed_json(expected_removals),
                "removal sequence differs from the independent maximum/occurrence model")
        object_fields(sample["final"], "main left right", "sample.final")
        for name, expected in model.items():
            check_binomial_state(sample["final"][name], implementation, expected, slots[name], "final." + name)
        saved = sample["saved"]
        require(isinstance(saved, list) and len(saved) == len(expected_saved), "saved version count differs")
        for actual, (name, queue, expected, capacity) in zip(saved, expected_saved):
            require(isinstance(actual, list) and len(actual) == 3 and actual[:2] == [name, queue],
                    "saved version identity differs")
            check_binomial_state(actual[2], implementation, expected, capacity, "saved." + name)
        generator = sample["generator"]
        if pattern != "random":
            require(generator is None, "nonrandom queue input cannot report a generator")
        else:
            object_fields(generator, "name initial final draws", "queue generator")
            require(generator["name"] == "StdGen/mkStdGen/randNat", "unexpected queue generator")
            for field in ("initial", "final"):
                state = generator[field]
                require(isinstance(state, list) and len(state) == 2, "expected a two-component queue generator state")
                require(1 <= natural(state[0], field) <= 2147483562 and
                        1 <= natural(state[1], field) <= 2147483398, "queue generator state outside its pinned range")
            seed = config["seed"]
            initial = [seed % 2147483562 + 1, (seed // 2147483562) % 2147483398 + 1]
            require(generator["initial"] == initial, "queue generator initial state differs from its seed")
            require(natural(generator["draws"], "generator.draws") == len(keys), "queue generator draw count differs")
            if not keys:
                require(generator["final"] == initial, "zero-draw queue generation changed its state")
            if (seed, config["universe"], len(keys)) == (1729, 13, 8):
                require(keys == [10, 0, 10, 11, 6, 10, 0, 0] and
                        generator["final"] == [1689113473, 525453832],
                        "queue inputs differ from the independently pinned generator stream")
        repeatable = typed_json({key: value for key, value in sample.items()
                                if key not in ("phase", "index", "elapsedNs")})
        require(previous is None or repeatable == previous, "queue repeats changed their reset workload or results")
        previous = repeatable
    return {"schema": 1, "status": "accepted", "kind": "binomial-workload", "samples": len(samples)}


def check_receipt(path):
    def unique_members(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON member: {key}")
            result[key] = value
        return result

    def reject_constant(value):
        raise ValueError(f"non-finite JSON constant: {value}")

    receipt = json.loads(path.read_bytes().decode("utf-8"),
                         object_pairs_hook=unique_members, parse_constant=reject_constant)
    if not isinstance(receipt, dict) or type(receipt.get("schema")) is not int or receipt["schema"] not in (1, 2, 3):
        raise ValueError("expected a schema-1, schema-2 or schema-3 observation object")
    if receipt.get("kind") == "binomial-examples":
        if typed_json(receipt) != typed_json(expected_binomial_examples()):
            raise ValueError("binomial examples differ from the complete independent expectations")
        return {"schema": 1, "status": "accepted", "kind": "binomial-examples", "samples": 0}
    if receipt.get("kind") == "binomial-workload":
        return check_binomial_workload(receipt)
    if receipt.get("kind") == "workload":
        return check_workload(receipt)
    if receipt.get("kind") == "redblack-examples":
        if typed_json(receipt) != typed_json(expected_redblack_examples()):
            raise ValueError("redblack examples differ from the complete independent expectations")
        for table in receipt["tables"]:
            observations = table["observations"]
            check_tree_observation(table["tree"], observations["carrier"], "redblack", observations["entries"])
        for case in receipt["invariantCounterexamples"]:
            check_tree_observation(case["tree"], "int", "redblack", case["entries"], require_valid=False)
        return {"schema": 1, "status": "accepted", "kind": "redblack-examples", "samples": 0}
    if receipt.get("kind") != "examples":
        raise ValueError("unsupported observation kind")
    if typed_json(receipt) != typed_json(expected_examples()):
        raise ValueError("example observations differ from the complete independent expectations")
    return {"schema": 1, "status": "accepted", "kind": "examples", "samples": 0}


class ExtractRuntime(unittest.TestCase):
    def test_redblack_consecutive_shape(self):
        # Source rotations after keys 0..6 yield black root 3, black children
        # 1/5 and black grandchildren 0/2/4/6. Inserting 7 adds a red right
        # child to 6: eight nodes, height four, black height three.
        result = self.invoke("workload", "--realization", "redblack", "--size", "8", "--queries", "8")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual(receipt["schema"], 2)
        self.assertEqual(receipt["config"]["realization"], "redblack")
        sample = receipt["samples"][0]
        self.assertEqual(sample["entries"], [[str(key), 1] for key in range(8)])
        self.assertEqual(sample["queryOptions"], [1] * 8)
        self.assertEqual((sample["hits"], sample["expectedHits"], sample["distinct"]), (8, 8, 8))
        self.assertEqual((sample["tree"]["nodes"], sample["tree"]["height"]), (8, 4))
        self.assertIs(sample["tree"]["bst"], True)
        self.assertEqual(sample["tree"]["redblack"], {
            "rootBlack": True, "noRedRed": True, "equalBlackHeight": True,
            "blackHeight": 3, "logHeightBound": True,
        })

    def test_receipt_observer_accepts_redblack_workload(self):
        result = self.invoke("workload", "--realization", "redblack", "--size", "8", "--queries", "8")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory(prefix="redblack-receipt-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(json.loads(observed.stdout),
                             {"schema": 1, "status": "accepted", "kind": "workload", "samples": 1})

    def test_redblack_signed_presence_and_suffix(self):
        result = self.invoke("redblack-examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(typed_json(json.loads(result.stdout)), typed_json(expected_redblack_examples()))
        with tempfile.TemporaryDirectory(prefix="redblack-examples-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(json.loads(observed.stdout),
                             {"schema": 1, "status": "accepted", "kind": "redblack-examples", "samples": 0})

    def test_redblack_invariant_counterexamples(self):
        result = self.invoke("redblack-examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertIn("invariantCounterexamples", receipt)
        self.assertEqual(typed_json(receipt["invariantCounterexamples"]),
                         typed_json(expected_invariant_counterexamples()))
        with tempfile.TemporaryDirectory(prefix="redblack-invariants-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)

    def test_controlled_same_files_compare_ordinary_and_redblack(self):
        # These are stored inputs shared by both executions, including the
        # independently pinned random stream and both finite signed endpoints.
        cases = [
            ("int64", list(range(128)), list(range(128)) + [-1, 128, 64]),
            ("int", [10, 0, 10, 11, 6, 10, 0, 0], [9, 7, 4, 11, 1, 8, 11, 8]),
            ("word63", [-(1 << 62), 3, -3, (1 << 62) - 1, 0, -3],
             [-(1 << 62), (1 << 62) - 1, 0, -1, -3, 3]),
            ("int64", [-(1 << 63), 3, -3, (1 << 63) - 1, 0, -3],
             [-(1 << 63), (1 << 63) - 1, 0, -1, -3, 3]),
        ]
        with tempfile.TemporaryDirectory(prefix="redblack-shared-replay-") as folder:
            inserted_path, queries_path, receipt_path = [Path(folder) / name for name in
                                                        ("inserted.txt", "queries.txt", "receipt.json")]
            for carrier, inserted, queries in cases:
                with self.subTest(carrier=carrier, inserted=len(inserted)):
                    inserted_bytes = "".join(f"{key}\n" for key in inserted).encode()
                    queries_bytes = "".join(f"{key}\n" for key in queries).encode()
                    inserted_path.write_bytes(inserted_bytes)
                    queries_path.write_bytes(queries_bytes)
                    pair = []
                    for realization in ("ordinary", "redblack"):
                        result = self.invoke("workload", "--realization", realization, "--carrier", carrier,
                                             "--pattern", "replay", "--inserted-file", str(inserted_path),
                                             "--queries-file", str(queries_path), "--warmups", "1", "--repetitions", "2")
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertEqual(inserted_path.read_bytes(), inserted_bytes)
                        self.assertEqual(queries_path.read_bytes(), queries_bytes)
                        receipt_path.write_text(result.stdout, encoding="utf-8")
                        observed = self.observe(receipt_path)
                        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                        receipt = json.loads(result.stdout)
                        self.assertEqual(receipt["config"]["realization"], realization)
                        self.assertEqual(receipt["timedRegion"], "precomputed queries: traversal, lookup, hit count")
                        pair.append(receipt)
                    for ordinary, redblack in zip(pair[0]["samples"], pair[1]["samples"]):
                        for field in ("phase", "index", "inserted", "queries", "entries", "queryOptions",
                                      "hits", "expectedHits", "distinct", "generator"):
                            self.assertEqual(typed_json(ordinary[field]), typed_json(redblack[field]), field)
                        self.assertEqual(ordinary["inserted"], list(map(str, inserted)))
                        self.assertEqual(ordinary["queries"], list(map(str, queries)))
                        self.assertEqual((ordinary["tree"]["nodes"], redblack["tree"]["nodes"]),
                                         (len(set(inserted)), len(set(inserted))))
                        if inserted == list(range(128)):
                            self.assertEqual((ordinary["tree"]["height"], redblack["tree"]["height"]), (128, 8))
                            self.assertEqual(redblack["tree"]["redblack"]["blackHeight"], 7)
                            self.assertEqual((ordinary["hits"], redblack["hits"]), (129, 129))

    def test_source_mode_compare_ordinary_and_redblack(self):
        with tempfile.TemporaryDirectory(prefix="redblack-source-compare-") as folder:
            path = Path(folder) / "receipt.json"
            for pattern in ("random", "consecutive"):
                with self.subTest(pattern=pattern):
                    pair = []
                    for realization in ("ordinary", "redblack"):
                        result = self.invoke("workload", "--realization", realization, "--carrier", "int64",
                                             "--pattern", pattern, "--timing", "source", "--size", "32",
                                             "--queries", "32", "--universe", "32", "--seed", "1729",
                                             "--warmups", "1", "--repetitions", "2")
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        path.write_text(result.stdout, encoding="utf-8")
                        observed = self.observe(path)
                        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                        receipt = json.loads(result.stdout)
                        self.assertEqual(receipt["timedRegion"],
                                         "generated queries: descending schedule creation/traversal, key generation, checked conversion, lookup, hit count")
                        pair.append(receipt)
                    for ordinary, redblack in zip(pair[0]["samples"], pair[1]["samples"]):
                        for field in ("phase", "index", "inserted", "queries", "entries", "queryOptions",
                                      "hits", "expectedHits", "distinct", "generator"):
                            self.assertEqual(typed_json(ordinary[field]), typed_json(redblack[field]), field)
                        if pattern == "consecutive":
                            self.assertEqual((ordinary["tree"]["height"], redblack["tree"]["height"]), (32, 6))
                            self.assertEqual((ordinary["hits"], redblack["hits"]), (32, 32))

    def test_redblack_empty_singleton_and_missing_queries(self):
        with tempfile.TemporaryDirectory(prefix="redblack-endpoints-") as folder:
            path = Path(folder) / "receipt.json"
            for carrier, size, count in (("int", 0, 0), ("word63", 1, 2), ("int64", 1, 1)):
                with self.subTest(carrier=carrier, size=size, count=count):
                    result = self.invoke("workload", "--realization", "redblack", "--carrier", carrier,
                                         "--size", str(size), "--queries", str(count))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    receipt = json.loads(result.stdout)
                    sample = receipt["samples"][0]
                    self.assertEqual(sample["queryOptions"], [1 if key < size else None for key in range(count)])
                    self.assertEqual(sample["hits"], min(size, count))
                    self.assertEqual((sample["tree"]["nodes"], sample["tree"]["height"],
                                      sample["tree"]["redblack"]["blackHeight"]), (size, size, size))
                    self.assertEqual(sample["tree"]["preorder"],
                                     [None] if size == 0 else [["black", "0", 1], None, None])
                    path.write_text(result.stdout, encoding="utf-8")
                    observed = self.observe(path)
                    self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)

    def test_redblack_rejects_options_and_unrepresentable_keys(self):
        for args in (("workload", "--realization", "rb"),
                     ("workload", "--realization", "ordinary", "--realization", "redblack"),
                     ("redblack-examples", "extra")):
            with self.subTest(args=args):
                self.assert_rejected(self.invoke(*args))
        with tempfile.TemporaryDirectory(prefix="redblack-range-") as folder:
            inserted, queries = Path(folder) / "inserted.txt", Path(folder) / "queries.txt"
            for carrier, exponent in (("word63", 62), ("int64", 63)):
                for bad_path, bad_key in ((inserted, -(1 << exponent) - 1), (queries, 1 << exponent)):
                    with self.subTest(carrier=carrier, input=bad_path.name):
                        inserted.write_text("0\n", encoding="utf-8")
                        queries.write_text("0\n", encoding="utf-8")
                        bad_path.write_text(f"{bad_key}\n", encoding="utf-8")
                        self.assert_rejected(self.invoke("workload", "--realization", "redblack", "--carrier", carrier,
                                                         "--pattern", "replay", "--inserted-file", str(inserted),
                                                         "--queries-file", str(queries)))

    def test_receipt_observer_preserves_schema_one(self):
        # A well-formed historical-format observation carries no inferred
        # realization/shape fields. This conversion tests format compatibility,
        # not a claim that the current run was the historical039 execution.
        result = self.invoke("workload", "--size", "3", "--queries", "4")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        current = json.loads(result.stdout)
        legacy = copy.deepcopy(current)
        legacy["schema"] = 1
        del legacy["config"]["realization"]
        for sample in legacy["samples"]:
            del sample["tree"]
        with tempfile.TemporaryDirectory(prefix="extract-legacy-schema-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(json.dumps(legacy), encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            for field in ("realization", "tree"):
                changed = copy.deepcopy(legacy)
                if field == "realization":
                    changed["config"]["realization"] = "ordinary"
                else:
                    changed["samples"][0]["tree"] = current["samples"][0]["tree"]
                path.write_text(json.dumps(changed), encoding="utf-8")
                self.assert_observer_rejected(self.observe(path))

    def test_receipt_observer_rejects_false_tree_observations(self):
        result = self.invoke("workload", "--realization", "redblack", "--size", "8", "--queries", "8")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        original = json.loads(result.stdout)
        tree = ("samples", 0, "tree")
        changes = [(("config", "realization"), "ordinary"),
                   (tree + ("nodes",), 7), (tree + ("height",), 3),
                   (tree + ("height",), True), (tree + ("height",), 4.0),
                   (tree + ("bst",), 1), (tree + ("bst",), False),
                   (tree + ("redblack", "rootBlack"), False),
                   (tree + ("redblack", "noRedRed"), 1),
                   (tree + ("redblack", "equalBlackHeight"), False),
                   (tree + ("redblack", "blackHeight"), 4),
                   (tree + ("redblack", "blackHeight"), 3.0),
                   (tree + ("redblack", "logHeightBound"), False),
                   (tree + ("preorder",), []),
                   (tree + ("preorder", 0), None),
                   (tree + ("preorder", 0), ["black", "3"]),
                   (tree + ("preorder", 0, 0), "green"),
                   (tree + ("preorder", 0, 0), None),
                   (tree + ("preorder", 0, 1), "3.0"),
                   (tree + ("preorder", 0, 1), str(1 << 63)),
                   (tree + ("preorder", 0, 2), True),
                   (tree + ("preorder", 0, 2), 0)]
        with tempfile.TemporaryDirectory(prefix="redblack-wrong-shape-") as folder:
            path = Path(folder) / "receipt.json"
            for location, value in changes:
                with self.subTest(location=location, value=value):
                    changed = copy.deepcopy(original)
                    target = changed
                    for key in location[:-1]:
                        target = target[key]
                    target[location[-1]] = value
                    path.write_text(json.dumps(changed), encoding="utf-8")
                    self.assert_observer_rejected(self.observe(path))
            for label in ("extra-nil", "missing-nil", "extra-field", "coherent-red-root", "coherent-unequal-black-height"):
                with self.subTest(case=label):
                    changed = copy.deepcopy(original)
                    observed_tree = changed["samples"][0]["tree"]
                    if label == "extra-nil":
                        observed_tree["preorder"].append(None)
                    elif label == "missing-nil":
                        observed_tree["preorder"].pop()
                    elif label == "extra-field":
                        observed_tree["unproved"] = True
                    elif label == "coherent-red-root":
                        observed_tree["preorder"][0][0] = "red"
                        observed_tree["redblack"]["rootBlack"] = False
                        observed_tree["redblack"]["blackHeight"] = 2
                    else:
                        # Preserve every binding, size and height while changing
                        # the red leaf7 to black. Report the resulting failure
                        # honestly; successful workloads must still reject it.
                        leaf = next(token for token in observed_tree["preorder"]
                                    if isinstance(token, list) and token[1] == "7")
                        leaf[0] = "black"
                        observed_tree["redblack"]["equalBlackHeight"] = False
                        observed_tree["redblack"]["blackHeight"] = None
                    path.write_text(json.dumps(changed), encoding="utf-8")
                    self.assert_observer_rejected(self.observe(path))

    def run_recorded(self, kind, command, arguments, input_paths=()):
        inputs = []
        for option, name in input_paths:
            path = Path(name)
            if path.is_file():
                data = path.read_bytes()
                inputs.append(({"option": option, "path": name, "bytes": len(data),
                                "sha256": hashlib.sha256(data).hexdigest()}, data))
            else:
                inputs.append(({"option": option, "path": name, "missing": True}, None))
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        clock = time.monotonic()
        result = subprocess.run(command, capture_output=True, check=False)
        seconds = time.monotonic() - clock
        log_folder = os.environ.get("EXTRACT_TEST_LOG_DIR")
        if log_folder:
            folder = Path(log_folder)
            folder.mkdir(parents=True, exist_ok=True)
            self._invocations = getattr(self, "_invocations", 0) + 1
            prefix = f"{self._testMethodName}-{self._invocations:03d}"

            def retain(name, data):
                with (folder / name).open("xb") as stream:
                    stream.write(data)

            stdout_file, stderr_file = prefix + ".stdout", prefix + ".stderr"
            retain(stdout_file, result.stdout)
            retain(stderr_file, result.stderr)
            for index, (record, data) in enumerate(inputs):
                if data is not None:
                    record["retained_file"] = f"{prefix}.input-{index}"
                    retain(record["retained_file"], data)
            metadata = {
                "kind": kind, "test": self.id(), "invocation": self._invocations,
                "command": command, "arguments": list(arguments),
                "returncode": result.returncode, "started_utc": started, "seconds": seconds,
                "stdout_file": stdout_file, "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
                "stderr_file": stderr_file, "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
                "input_files": [record for record, _ in inputs],
            }
            retain(prefix + ".json", (json.dumps(metadata, indent=2) + "\n").encode())
        return subprocess.CompletedProcess(
            command, result.returncode, result.stdout.decode("utf-8"), result.stderr.decode("utf-8"),
        )

    def invoke(self, *args):
        paths = [(flag, args[index + 1]) for index, flag in enumerate(args[:-1])
                 if flag in ("--inserted-file", "--queries-file", "--keys-file")]
        return self.run_recorded("driver", COMMAND + list(args), args, paths)

    def assert_rejected(self, result):
        self.assertIn(result.returncode, (1, 2), result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertTrue(result.stderr.strip())

    def observe(self, path):
        args = ["--check-receipt", str(path)]
        return self.run_recorded("observer", [sys.executable, "-B", __file__, *args], args,
                                 [("--check-receipt", str(path))])

    def assert_observer_rejected(self, result):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertTrue(result.stderr.startswith("receipt rejected:"), result.stderr)

    def test_examples_sort_z(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual(receipt["schema"], 1)
        self.assertEqual(receipt["kind"], "examples")
        self.assertEqual(receipt["sortZ"]["input"], ["-3", "2", "-3", "0", "1"])
        self.assertEqual(receipt["sortZ"]["output"], ["-3", "-3", "0", "1", "2"])

    def test_examples_nat_lists(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        cases = receipt["natSort"]
        inputs = [[], [7], [4, 3, 2, 1], [3, 1, 3, 0, 1]]
        self.assertEqual(len(cases), len(inputs))
        for case, original in zip(cases, inputs):
            with self.subTest(original=original):
                self.assertEqual(case["input"], list(map(str, original)))
                self.assertEqual(case["output"], list(map(str, sorted(original))))

    def test_examples_finite_signed_sort(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        cases = json.loads(result.stdout)["finiteSort"]
        self.assertEqual([case["carrier"] for case in cases], ["word63", "int64"])
        for case, width in zip(cases, (63, 64)):
            with self.subTest(carrier=case["carrier"]):
                minimum = -(1 << (width - 1))
                maximum = (1 << (width - 1)) - 1
                original = [-1, maximum, minimum, 0, -1]
                self.assertEqual(case["width"], width)
                self.assertEqual(case["minimum"], str(minimum))
                self.assertEqual(case["maximum"], str(maximum))
                self.assertEqual(case["input"], list(map(str, original)))
                self.assertEqual(case["output"], list(map(str, sorted(original))))

    def test_examples_stable_labelled_ties(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        cases = json.loads(result.stdout)["stableSort"]
        self.assertEqual([case["carrier"] for case in cases], ["int", "word63", "int64"])
        for case in cases:
            with self.subTest(carrier=case["carrier"]):
                self.assertEqual(case["input"], [["2", "first"], ["1", "middle"], ["2", "last"]])
                self.assertEqual(case["output"], [["1", "middle"], ["2", "first"], ["2", "last"]])

    def test_examples_signed_comparison_branches(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        groups = receipt["comparisons"]
        self.assertEqual([group["carrier"] for group in groups], ["int", "word63", "int64"])
        for group, exponent in zip(groups, (70, 62, 63)):
            endpoints = (-(1 << exponent), (1 << exponent) - 1)
            inputs = [(-3, 0), (0, 0), (4, -1), endpoints, endpoints[::-1]]
            self.assertEqual(len(group["cases"]), len(inputs))
            for case, (left, right) in zip(group["cases"], inputs):
                with self.subTest(carrier=group["carrier"], left=left, right=right):
                    self.assertEqual(case["left"], str(left))
                    self.assertEqual(case["right"], str(right))
                    self.assertIs(case["lt"], left < right)
                    self.assertIs(case["le"], left <= right)
        self.assertEqual(receipt["fourBitComparison"], {
            "left": "-1", "right": "0", "signedLt": True, "unsignedLt": False,
        })

    def test_examples_table_observations(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        tables = json.loads(result.stdout)["tables"]
        self.assertEqual([table["carrier"] for table in tables], ["int", "word63", "int64"])
        writes = [["-3", 7], ["4", 8], ["-3", 9], ["0", 0]]
        expected_entries = [["-3", 9], ["0", 0], ["4", 8]]
        for table in tables:
            with self.subTest(carrier=table["carrier"]):
                self.assertEqual(table["writes"], writes)
                self.assertEqual(table["queries"], ["-3", "4", "0", "-1"])
                self.assertEqual(table["optional"], [9, 8, 0, None])
                self.assertEqual(table["default0"], [9, 8, 0, 0])
                self.assertEqual(table["default99"], [9, 8, 0, 99])
                self.assertEqual(table["entries"], expected_entries)
                self.assertEqual(table["withSuffix"], expected_entries + [["99", 123]])
                self.assertEqual(table["empty"], {"entries": [], "optional": None, "default": 99})

    def test_examples_word_boundaries(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        boundaries = json.loads(result.stdout)["wordBoundaries"]
        self.assertEqual(boundaries["overflow"], {
            "width": 4, "left": "7", "right": "1", "sum": "-8",
            "mathematicalSum": "8", "overflow": True,
        })
        self.assertEqual(boundaries["safe"], {
            "width": 4, "left": "2", "right": "1", "sum": "3",
            "mathematicalSum": "3", "overflow": False,
        })
        self.assertEqual(boundaries["zeroWidth"], {
            "sourceIntegers": ["-3", "4", "99"],
            "decodedKeys": ["0", "0", "0"],
            "strict": False, "nonstrict": True,
            "entries": [["0", 9]], "optional": 9, "default99": 9,
        })

    def test_examples_int_empty_and_singleton(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout)["sortZBoundary"], [
            {"input": [], "output": []},
            {"input": ["-7"], "output": ["-7"]},
        ])

    def test_workload_defaults(self):
        result = self.invoke("workload")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual((receipt["schema"], receipt["kind"]), (2, "workload"))
        self.assertEqual(receipt["config"], {
            "realization": "ordinary",
            "carrier": "int64", "pattern": "consecutive", "timing": "controlled",
            "size": 32, "queries": 32, "universe": 32, "seed": 1729,
            "warmups": 0, "repetitions": 1, "insertedFile": None, "queriesFile": None,
        })
        self.assertEqual((receipt["clock"], receipt["unit"]), ("IO.monoNanosNow", "ns"))
        self.assertEqual(receipt["timedRegion"], "precomputed queries: traversal, lookup, hit count")
        self.assertEqual(len(receipt["samples"]), 1)
        sample = receipt["samples"][0]
        self.assertEqual((sample["phase"], sample["index"]), ("measured", 0))
        expected_keys = list(map(str, range(32)))
        self.assertEqual(sample["inserted"], expected_keys)
        self.assertEqual(sample["queries"], expected_keys)
        self.assertEqual(sample["entries"], [[key, 1] for key in expected_keys])
        self.assertEqual(sample["queryOptions"], [1] * 32)
        self.assertEqual((sample["hits"], sample["expectedHits"], sample["distinct"]), (32, 32, 32))
        self.assertIs(type(sample["elapsedNs"]), int)
        self.assertGreaterEqual(sample["elapsedNs"], 0)
        self.assertEqual(sample["generator"], {
            "name": "StdGen/mkStdGen/randNat", "initial": [1730, 1],
            "postBuild": [1730, 1], "postQuery": [1730, 1],
            "buildDraws": 0, "queryDraws": 0,
        })

    def test_workload_consecutive_configuration(self):
        for carrier, size, count in (("int", 0, 0), ("word63", 1, 1), ("int64", 4, 4), ("int", 3, 5)):
            with self.subTest(carrier=carrier, size=size, queries=count):
                result = self.invoke("workload", "--carrier", carrier, "--pattern", "consecutive",
                                     "--timing", "controlled", "--size", str(size), "--queries", str(count))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                receipt = json.loads(result.stdout)
                config = receipt["config"]
                self.assertEqual((config["carrier"], config["size"], config["queries"]), (carrier, size, count))
                sample = receipt["samples"][0]
                self.assertEqual(sample["inserted"], list(map(str, range(size))))
                self.assertEqual(sample["queries"], list(map(str, range(count))))
                self.assertEqual(sample["entries"], [[str(key), 1] for key in range(size)])
                options = [1 if key < size else None for key in range(count)]
                self.assertEqual(sample["queryOptions"], options)
                self.assertEqual(sample["hits"], min(size, count))
                self.assertEqual(sample["expectedHits"], min(size, count))
                self.assertEqual(sample["distinct"], size)
        # Invalid prefixes must be rejected before constructing their lists.
        for carrier, size, count in (("word63", (1 << 62) + 1, 0), ("int64", 0, (1 << 63) + 1)):
            with self.subTest(out_of_range=carrier):
                result = self.invoke("workload", "--carrier", carrier, "--size", str(size), "--queries", str(count))
                self.assert_rejected(result)

    def test_workload_replays_independent_lists(self):
        cases = [
            ("int", [3, 1, 3], [3, 2, 1, 3, 7]),
            ("word63", [-3, 0, 4, -3], [-3, -1, 4, 0, 4]),
            ("int64", [-(1 << 63), (1 << 63) - 1], [-(1 << 63), 0, (1 << 63) - 1, -(1 << 63)]),
            ("int64", [], []),
        ]
        with tempfile.TemporaryDirectory(prefix="extract-replay-") as folder:
            inserted_path = Path(folder) / "inserted.txt"
            query_path = Path(folder) / "queries.txt"
            for carrier, inserted, queries in cases:
                with self.subTest(carrier=carrier, inserted=inserted, queries=queries):
                    inserted_path.write_text("".join(f"{key}\n" for key in inserted), encoding="utf-8")
                    query_path.write_text("".join(f"{key}\n" for key in queries), encoding="utf-8")
                    result = self.invoke("workload", "--carrier", carrier, "--pattern", "replay",
                                         "--inserted-file", str(inserted_path), "--queries-file", str(query_path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    receipt = json.loads(result.stdout)
                    config = receipt["config"]
                    self.assertEqual((config["size"], config["queries"]), (len(inserted), len(queries)))
                    self.assertEqual((config["pattern"], config["timing"]), ("replay", "controlled"))
                    self.assertIsNone(config["seed"])
                    self.assertIsNone(config["universe"])
                    self.assertEqual((config["insertedFile"], config["queriesFile"]), (str(inserted_path), str(query_path)))
                    sample = receipt["samples"][0]
                    model = dict.fromkeys(inserted, 1)
                    options = [model.get(key) for key in queries]
                    self.assertEqual(sample["inserted"], list(map(str, inserted)))
                    self.assertEqual(sample["queries"], list(map(str, queries)))
                    self.assertEqual(sample["entries"], [[str(key), model[key]] for key in sorted(model)])
                    self.assertEqual(sample["queryOptions"], options)
                    self.assertEqual((sample["hits"], sample["expectedHits"]), (options.count(1), options.count(1)))
                    self.assertEqual(sample["distinct"], len(model))
                    self.assertIsNone(sample["generator"])

    def test_workload_seeded_fresh_random_queries(self):
        # Literal stream observed directly from pinned Init.Data.Random before
        # the driver implemented generation; see the runtime evidence record.
        inserted = [10, 0, 10, 11, 6, 10, 0, 0]
        queries = [9, 7, 4, 11, 1, 8, 11, 8]
        for carrier in ("int", "word63", "int64"):
            with self.subTest(carrier=carrier):
                result = self.invoke("workload", "--carrier", carrier, "--pattern", "random",
                                     "--size", "8", "--queries", "8", "--universe", "13", "--seed", "1729")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                receipt = json.loads(result.stdout)
                self.assertEqual((receipt["config"]["seed"], receipt["config"]["universe"]), (1729, 13))
                sample = receipt["samples"][0]
                self.assertEqual(sample["inserted"], list(map(str, inserted)))
                self.assertEqual(sample["queries"], list(map(str, queries)))
                self.assertEqual(sample["entries"], [["0", 1], ["6", 1], ["10", 1], ["11", 1]])
                self.assertEqual(sample["queryOptions"], [None, None, None, 1, None, None, 1, None])
                self.assertEqual((sample["hits"], sample["expectedHits"], sample["distinct"]), (2, 2, 4))
                self.assertEqual(sample["generator"], {
                    "name": "StdGen/mkStdGen/randNat", "initial": [1730, 1],
                    "postBuild": [1689113473, 525453832], "postQuery": [1827515937, 1554910725],
                    "buildDraws": 8, "queryDraws": 8,
                })
        result = self.invoke("workload", "--pattern", "random", "--size", "0", "--queries", "0", "--universe", "0")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        sample = json.loads(result.stdout)["samples"][0]
        self.assertEqual((sample["inserted"], sample["queries"], sample["entries"], sample["hits"]), ([], [], [], 0))
        self.assertEqual(sample["generator"], {
            "name": "StdGen/mkStdGen/randNat", "initial": [1730, 1],
            "postBuild": [1730, 1], "postQuery": [1730, 1], "buildDraws": 0, "queryDraws": 0,
        })
        for options in (("--universe", "0"), ("--carrier", "word63", "--universe", str((1 << 62) + 1))):
            with self.subTest(invalid_range=options):
                result = self.invoke("workload", "--pattern", "random", "--size", "1", "--queries", "1", *options)
                self.assert_rejected(result)

    def test_workload_source_query_region(self):
        cases = [("int", "consecutive", 0, 0), ("word63", "consecutive", 1, 1),
                 ("int64", "consecutive", 4, 4), ("int64", "random", 0, 0)]
        cases += [(carrier, "random", 8, 13) for carrier in ("int", "word63", "int64")]
        for carrier, pattern, size, universe in cases:
            with self.subTest(carrier=carrier, pattern=pattern, size=size):
                result = self.invoke("workload", "--carrier", carrier, "--pattern", pattern,
                                     "--timing", "source", "--size", str(size), "--queries", str(size),
                                     "--universe", str(universe), "--seed", "1729")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                receipt = json.loads(result.stdout)
                self.assertEqual(receipt["config"]["timing"], "source")
                self.assertEqual(receipt["timedRegion"],
                    "generated queries: descending schedule creation/traversal, key generation, checked conversion, lookup, hit count")
                sample = receipt["samples"][0]
                if pattern == "random" and size:
                    inserted = [10, 0, 10, 11, 6, 10, 0, 0]
                    queries = [9, 7, 4, 11, 1, 8, 11, 8]
                    self.assertEqual(sample["generator"]["postBuild"], [1689113473, 525453832])
                    self.assertEqual(sample["generator"]["postQuery"], [1827515937, 1554910725])
                else:
                    inserted = list(range(size))
                    queries = list(range(size))
                    self.assertEqual(sample["generator"]["postBuild"], [1730, 1])
                    self.assertEqual(sample["generator"]["postQuery"], [1730, 1])
                model = dict.fromkeys(inserted, 1)
                options = [model.get(key) for key in queries]
                self.assertEqual(sample["inserted"], list(map(str, inserted)))
                self.assertEqual(sample["queries"], list(map(str, queries)))
                self.assertEqual(sample["queryOptions"], options)
                self.assertEqual(sample["entries"], [[str(key), model[key]] for key in sorted(model)])
                self.assertEqual((sample["hits"], sample["expectedHits"]), (options.count(1), options.count(1)))
                self.assertEqual(sample["distinct"], len(model))
                self.assertIs(type(sample["elapsedNs"]), int)
                self.assertGreaterEqual(sample["elapsedNs"], 0)
        result = self.invoke("workload", "--timing", "source", "--size", "2", "--queries", "3")
        self.assert_rejected(result)

    def test_workload_warmups_and_repetitions(self):
        result = self.invoke("workload", "--pattern", "random", "--timing", "source",
                             "--size", "8", "--queries", "8", "--universe", "13", "--seed", "1729",
                             "--warmups", "1", "--repetitions", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual((receipt["config"]["warmups"], receipt["config"]["repetitions"]), (1, 2))
        samples = receipt["samples"]
        self.assertEqual([(s["phase"], s["index"]) for s in samples],
                         [("warmup", 0), ("measured", 0), ("measured", 1)])
        for sample in samples:
            self.assertEqual(sample["inserted"], ["10", "0", "10", "11", "6", "10", "0", "0"])
            self.assertEqual(sample["queries"], ["9", "7", "4", "11", "1", "8", "11", "8"])
            self.assertEqual((sample["hits"], sample["expectedHits"]), (2, 2))
            self.assertEqual(sample["generator"]["initial"], [1730, 1])
            self.assertEqual(sample["generator"]["postBuild"], [1689113473, 525453832])
            self.assertEqual(sample["generator"]["postQuery"], [1827515937, 1554910725])
            self.assertIs(type(sample["elapsedNs"]), int)
            self.assertGreaterEqual(sample["elapsedNs"], 0)
        with tempfile.TemporaryDirectory(prefix="extract-repeated-replay-") as folder:
            inserted = Path(folder) / "inserted.txt"
            queries = Path(folder) / "queries.txt"
            inserted.write_text("3\n1\n3\n", encoding="utf-8")
            queries.write_text("3\n2\n1\n3\n7\n", encoding="utf-8")
            result = self.invoke("workload", "--pattern", "replay", "--inserted-file", str(inserted),
                                 "--queries-file", str(queries), "--warmups", "1", "--repetitions", "2")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            receipt = json.loads(result.stdout)
            self.assertEqual([(s["phase"], s["index"]) for s in receipt["samples"]],
                             [("warmup", 0), ("measured", 0), ("measured", 1)])
            for sample in receipt["samples"]:
                self.assertEqual(sample["inserted"], ["3", "1", "3"])
                self.assertEqual(sample["queries"], ["3", "2", "1", "3", "7"])
                self.assertEqual((sample["hits"], sample["expectedHits"]), (3, 3))
                self.assertIsNone(sample["generator"])

    def test_workload_source_random_specialization(self):
        # The companion's test_random n uses the same positive n for the
        # construction count, fresh query count, and half-open key universe.
        result = self.invoke("workload", "--pattern", "random", "--timing", "source")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual((receipt["config"]["size"], receipt["config"]["queries"],
                          receipt["config"]["universe"]), (32, 32, 32))
        sample = receipt["samples"][0]
        inserted, queries = [list(map(int, sample[field])) for field in ("inserted", "queries")]
        self.assertEqual((len(inserted), len(queries)), (32, 32))
        self.assertTrue(all(0 <= key < 32 for key in inserted + queries))
        model = dict.fromkeys(inserted, 1)
        options = [model.get(key) for key in queries]
        self.assertEqual(sample["queryOptions"], options)
        self.assertEqual(sample["entries"], [[str(key), 1] for key in sorted(model)])
        self.assertEqual((sample["hits"], sample["expectedHits"], sample["distinct"]),
                         (options.count(1), options.count(1), len(model)))
        self.assertEqual((sample["generator"]["buildDraws"], sample["generator"]["queryDraws"]), (32, 32))

    def test_rejects_invalid_commands_and_options(self):
        cases = [(), ("unknown",), ("examples", "extra"),
                 ("workload", "--unknown", "1"), ("workload", "--size"),
                 ("workload", "--size", "1", "--size", "2"),
                 ("workload", "--carrier", "uint64"),
                 ("workload", "--pattern", "sorted"),
                 ("workload", "--timing", "build"),
                 ("workload", "--size", "1.5"), ("workload", "--queries", "x"),
                 ("workload", "--repetitions", "0")]
        cases += [("workload", flag, "-1") for flag in
                  ("--size", "--queries", "--universe", "--seed", "--warmups", "--repetitions")]
        for args in cases:
            with self.subTest(args=args):
                self.assert_rejected(self.invoke(*args))

    def test_rejects_conflicting_replay_options(self):
        with tempfile.TemporaryDirectory(prefix="extract-conflicting-replay-") as folder:
            path = Path(folder) / "keys.txt"
            path.write_text("1\n", encoding="utf-8")
            base = ("workload", "--pattern", "replay", "--inserted-file", str(path), "--queries-file", str(path))
            cases = [base + (flag, "1") for flag in ("--size", "--queries", "--seed", "--universe")]
            cases += [base + ("--timing", "source"),
                      ("workload", "--pattern", "replay"),
                      ("workload", "--pattern", "replay", "--inserted-file", str(path)),
                      ("workload", "--inserted-file", str(path), "--queries-file", str(path))]
            for args in cases:
                with self.subTest(args=args):
                    self.assert_rejected(self.invoke(*args))

    def test_replay_accepts_crlf_and_missing_final_newline(self):
        with tempfile.TemporaryDirectory(prefix="extract-text-replay-") as folder:
            inserted, queries = Path(folder) / "inserted.txt", Path(folder) / "queries.txt"
            inserted.write_bytes(b"-3\r\n0\r\n4\r\n-3")
            queries.write_bytes(b"-3\r\n-1\r\n4\r\n0")
            result = self.invoke("workload", "--pattern", "replay", "--inserted-file", str(inserted),
                                 "--queries-file", str(queries))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            sample = json.loads(result.stdout)["samples"][0]
            self.assertEqual(sample["inserted"], ["-3", "0", "4", "-3"])
            self.assertEqual(sample["queries"], ["-3", "-1", "4", "0"])
            self.assertEqual(sample["queryOptions"], [1, None, 1, 1])
            self.assertEqual((sample["hits"], sample["expectedHits"]), (3, 3))

    def test_replay_rejects_malformed_and_missing_files(self):
        with tempfile.TemporaryDirectory(prefix="extract-bad-replay-") as folder:
            inserted, queries = Path(folder) / "inserted.txt", Path(folder) / "queries.txt"
            queries.write_bytes(b"1\n")
            for data in (b"1\n\n2\n", b"1.5\n", b"one\n", b"\xff\n", b"1 2\n", b" \n"):
                with self.subTest(data=data):
                    inserted.write_bytes(data)
                    self.assert_rejected(self.invoke("workload", "--pattern", "replay", "--inserted-file", str(inserted),
                                                     "--queries-file", str(queries)))
            inserted.unlink()
            self.assert_rejected(self.invoke("workload", "--pattern", "replay", "--inserted-file", str(inserted),
                                             "--queries-file", str(queries)))

    def test_replay_rejects_adjacent_out_of_range_keys(self):
        with tempfile.TemporaryDirectory(prefix="extract-range-replay-") as folder:
            inserted, queries = Path(folder) / "inserted.txt", Path(folder) / "queries.txt"
            for carrier, exponent in (("word63", 62), ("int64", 63)):
                for key in (-(1 << exponent) - 1, 1 << exponent):
                    for bad_path in (inserted, queries):
                        with self.subTest(carrier=carrier, key=key, input=bad_path.name):
                            inserted.write_text("0\n", encoding="utf-8")
                            queries.write_text("0\n", encoding="utf-8")
                            bad_path.write_text(f"{key}\n", encoding="utf-8")
                            self.assert_rejected(self.invoke("workload", "--carrier", carrier, "--pattern", "replay",
                                                             "--inserted-file", str(inserted), "--queries-file", str(queries)))

    def test_receipt_observer_accepts_examples(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory(prefix="extract-receipt-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(json.loads(observed.stdout),
                             {"schema": 1, "status": "accepted", "kind": "examples", "samples": 0})
            self.assertEqual(observed.stderr, "")

    def test_receipt_observer_accepts_workloads(self):
        with tempfile.TemporaryDirectory(prefix="extract-workload-receipts-") as folder:
            path = Path(folder) / "receipt.json"
            inserted, queries = Path(folder) / "inserted.txt", Path(folder) / "queries.txt"
            inserted.write_text("3\n1\n3\n", encoding="utf-8")
            queries.write_text("3\n2\n1\n3\n7\n", encoding="utf-8")
            cases = [((), 1),
                     (("--pattern", "random", "--timing", "source", "--size", "8", "--queries", "8",
                       "--universe", "13", "--warmups", "1", "--repetitions", "2"), 3),
                     (("--carrier", "word63", "--pattern", "random", "--size", "0", "--queries", "0",
                       "--universe", "0"), 1),
                     (("--carrier", "int", "--pattern", "replay", "--inserted-file", str(inserted),
                       "--queries-file", str(queries)), 1)]
            for args, samples in cases:
                with self.subTest(args=args):
                    result = self.invoke("workload", *args)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    path.write_text(result.stdout, encoding="utf-8")
                    observed = self.observe(path)
                    self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                    self.assertEqual(json.loads(observed.stdout),
                                     {"schema": 1, "status": "accepted", "kind": "workload", "samples": samples})
                    self.assertEqual(observed.stderr, "")

    def test_receipt_observer_rejects_invalid_json(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        original = result.stdout.strip()
        cases = [b"", b"{", b"[]", b"null", b"\xff", original[:-1].encode(),
                 (original + "\n{}").encode(), ('{"schema":1,' + original[1:]).encode(),
                 original.replace('"input":', '"input":[],"input":', 1).encode(),
                 b'{"schema":NaN}', b'{"schema":Infinity}', b'{"schema":-Infinity}',
                 b'{"schema":1e309}']
        with tempfile.TemporaryDirectory(prefix="extract-invalid-receipts-") as folder:
            path = Path(folder) / "receipt.json"
            for index, data in enumerate(cases):
                with self.subTest(case=index):
                    path.write_bytes(data)
                    self.assert_observer_rejected(self.observe(path))
            path.unlink()
            self.assert_observer_rejected(self.observe(path))

    def test_receipt_observer_rejects_wrong_examples(self):
        result = self.invoke("examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        original = json.loads(result.stdout)
        changes = [(("schema",), True), (("schema",), 1.0),
                   (("sortZ", "output", 0), "-2"), (("natSort", 2, "output"), ["4", "3", "2", "1"]),
                   (("finiteSort", 0, "minimum"), str(-(1 << 62) + 1)),
                   (("stableSort", 0, "output"), [["1", "middle"], ["2", "last"], ["2", "first"]]),
                   (("comparisons", 2, "cases", 1, "lt"), True),
                   (("fourBitComparison", "unsignedLt"), True), (("tables", 0, "optional", 3), 0),
                   (("tables", 1, "entries"), [["-3", 9], ["0", 0], ["0", 0]]),
                   (("tables", 2, "withSuffix", 3, 1), True),
                   (("wordBoundaries", "overflow", "overflow"), False),
                   (("wordBoundaries", "zeroWidth", "entries", 0, 1), 8)]
        with tempfile.TemporaryDirectory(prefix="extract-wrong-examples-") as folder:
            path = Path(folder) / "receipt.json"
            for location, value in changes:
                with self.subTest(location=location, value=value):
                    changed = copy.deepcopy(original)
                    parent = changed
                    for key in location[:-1]:
                        parent = parent[key]
                    parent[location[-1]] = value
                    path.write_text(json.dumps(changed), encoding="utf-8")
                    self.assert_observer_rejected(self.observe(path))
            for change in ("missing", "extra"):
                changed = copy.deepcopy(original)
                if change == "missing":
                    del changed["tables"]
                else:
                    changed["unreported"] = 1
                path.write_text(json.dumps(changed), encoding="utf-8")
                self.assert_observer_rejected(self.observe(path))

    def test_receipt_observer_rejects_wrong_workloads(self):
        result = self.invoke("workload", "--pattern", "random", "--timing", "source", "--size", "8",
                             "--queries", "8", "--universe", "13", "--warmups", "1", "--repetitions", "2")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        original = json.loads(result.stdout)
        sample = ("samples", 0)
        changes = [(("clock",), "CPU"), (("unit",), "ms"), (("timedRegion",), "build and lookup"),
                   (("config", "carrier"), "uint64"), (("config", "pattern"), "rand"),
                   (("config", "timing"), "build"), (("config", "queries"), 7),
                   (("config", "universe"), 11), (("config", "repetitions"), 0),
                   (("config", "warmups"), True), (("config", "size"), 8.0),
                   (("config", "seed"), 1728), (("config", "insertedFile"), "invented.txt"),
                   (sample + ("phase",), "measured"), (sample + ("index",), True),
                   (sample + ("elapsedNs",), -1), (sample + ("elapsedNs",), True),
                   (sample + ("elapsedNs",), 1.0), (sample + ("elapsedNs",), float("nan")),
                   (sample + ("hits",), 8), (sample + ("expectedHits",), 8),
                   (sample + ("distinct",), 5), (sample + ("queryOptions", 0), 1),
                   (sample + ("queryOptions", 3), True),
                   (sample + ("entries",), [["11", 1], ["10", 1], ["6", 1], ["0", 1]]),
                   (sample + ("entries",), [["0", 1], ["6", 1], ["10", 1]]),
                   (sample + ("entries", 0, 1), 1.0),
                   (sample + ("generator", "name"), "different"),
                   (sample + ("generator", "initial", 0), 1729),
                   (sample + ("generator", "postBuild", 0), 0),
                   (sample + ("generator", "postQuery", 0), 1827515938),
                   (sample + ("generator", "buildDraws"), True),
                   (sample + ("generator", "queryDraws"), 9),
                   (sample + ("generator",), None), (("samples",), [])]
        changes += [(sample + ("inserted", 0), value)
                    for value in ("-0", "+10", "010", "1e1", " 10", "10.0", str(1 << 63), 10)]
        with tempfile.TemporaryDirectory(prefix="extract-wrong-workloads-") as folder:
            path = Path(folder) / "receipt.json"
            for location, value in changes:
                with self.subTest(location=location, value=value):
                    changed = copy.deepcopy(original)
                    parent = changed
                    for key in location[:-1]:
                        parent = parent[key]
                    parent[location[-1]] = value
                    path.write_text(json.dumps(changed), encoding="utf-8")
                    self.assert_observer_rejected(self.observe(path))
            for label in ("self-consistent-wrong-hits", "missing-sample-member", "extra-sample-member",
                          "nonrepeatable-input", "coherent-wrong-random-stream"):
                with self.subTest(case=label):
                    changed = copy.deepcopy(original)
                    if label == "self-consistent-wrong-hits":
                        changed["samples"][0]["hits"] = changed["samples"][0]["expectedHits"] = 8
                    elif label == "missing-sample-member":
                        del changed["samples"][0]["entries"]
                    elif label == "extra-sample-member":
                        changed["samples"][0]["extra"] = 1
                    elif label == "nonrepeatable-input":
                        # Outside the pinned stream case, changing one repeated
                        # input can preserve its map/results but violates reset.
                        changed["config"]["universe"] = 14
                        changed["samples"][2]["inserted"][0] = "11"
                    else:
                        # Keep every repeated map/result internally consistent;
                        # the independent pinned stream must still reject it.
                        for sample in changed["samples"]:
                            sample["inserted"][0] = "12"
                            sample["entries"].append(["12", 1])
                            sample["distinct"] = 5
                    path.write_text(json.dumps(changed), encoding="utf-8")
                    self.assert_observer_rejected(self.observe(path))

    def test_receipt_observer_accepts_unbounded_integer_replay(self):
        # This exceeds Python's former default decimal-conversion limit.
        positive = "1" + "0" * 4400
        negative = "-" + positive
        with tempfile.TemporaryDirectory(prefix="extract-large-int-receipt-") as folder:
            inserted, queries, receipt = [Path(folder) / name for name in ("inserted.txt", "queries.txt", "receipt.json")]
            inserted.write_text(f"{positive}\n{negative}\n{positive}\n", encoding="utf-8")
            queries.write_text(f"{negative}\n0\n{positive}\n", encoding="utf-8")
            result = self.invoke("workload", "--carrier", "int", "--pattern", "replay", "--inserted-file", str(inserted),
                                 "--queries-file", str(queries))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            sample = json.loads(result.stdout)["samples"][0]
            self.assertEqual(sample["inserted"], [positive, negative, positive])
            self.assertEqual(sample["entries"], [[negative, 1], [positive, 1]])
            self.assertEqual(sample["queryOptions"], [1, None, 1])
            self.assertEqual((sample["hits"], sample["expectedHits"], sample["distinct"]), (2, 2, 2))
            receipt.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(receipt)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(json.loads(observed.stdout),
                             {"schema": 1, "status": "accepted", "kind": "workload", "samples": 1})


def expected_binomial_examples():
    """Literal source Eval shape; no insertion or linking algorithm is replayed."""
    def preorder(tree):
        if tree is None:
            return [None]
        key, left, right = tree
        return [str(key), *preorder(left), *preorder(right)]

    rank_three = (9,
                  (4, (3, (1, None, None), (1, None, None)),
                   (3, (2, None, None), (5, None, None))),
                  None)
    return {
        "schema": 3,
        "kind": "binomial-examples",
        "sourceFold": {
            "input": list(map(str, [3, 1, 4, 1, 5, 9, 2, 3, 5])),
            "forest": [preorder((5, None, None)), [None], [None], preorder(rank_three)],
            "slots": 4,
            "maximum": "9",
        },
    }


class BinomialRuntime(unittest.TestCase):
    run_recorded = ExtractRuntime.run_recorded
    invoke = ExtractRuntime.invoke
    observe = ExtractRuntime.observe
    assert_rejected = ExtractRuntime.assert_rejected
    assert_observer_rejected = ExtractRuntime.assert_observer_rejected

    def test_source_fold(self):
        result = self.invoke("binom-examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(typed_json(json.loads(result.stdout)),
                         typed_json(expected_binomial_examples()))

    def test_source_fold_observer(self):
        result = self.invoke("binom-examples")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory(prefix="binom-source-observer-") as folder:
            path = Path(folder) / "receipt.json"
            path.write_text(result.stdout, encoding="utf-8")
            observed = self.observe(path)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(json.loads(observed.stdout),
                             {"schema": 1, "status": "accepted", "kind": "binomial-examples", "samples": 0})
            changed = json.loads(result.stdout)
            changed["sourceFold"]["forest"][3][0] = "8"
            path.write_text(json.dumps(changed), encoding="utf-8")
            self.assert_observer_rejected(self.observe(path))

    def test_replay_drain(self):
        # Exact duplicate multiplicity, zero, a final failed removal and the
        # still-live saved version are checked at the public command boundary.
        keys = [3, 1, 3, 0]
        with tempfile.TemporaryDirectory(prefix="binom-drain-") as folder:
            path = Path(folder) / "keys.txt"
            path.write_text("".join(f"{key}\n" for key in keys), encoding="utf-8")
            for implementation in ("binomial", "list"):
                with self.subTest(implementation=implementation):
                    result = self.invoke("binom-workload", "--implementation", implementation,
                                         "--pattern", "replay", "--keys-file", str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    receipt = json.loads(result.stdout)
                    self.assertEqual((receipt["schema"], receipt["kind"]), (3, "binomial-workload"))
                    self.assertEqual(receipt["config"]["implementation"], implementation)
                    self.assertEqual(receipt["config"]["schedule"], "drain")
                    self.assertEqual(len(receipt["samples"]), 1)
                    sample = receipt["samples"][0]
                    self.assertEqual((sample["phase"], sample["index"]), ("measured", 0))
                    self.assertEqual(sample["keys"], list(map(str, keys)))
                    self.assertEqual(sample["operations"],
                                     [["insert", "main", str(key)] for key in keys] +
                                     [["save", "built", "main"]] + [["delete", "main"]] * 5)
                    self.assertEqual(sample["removals"],
                                     [[5 + index, "main", key] for index, key in
                                      enumerate(["3", "3", "1", "0", None])])
                    self.assertEqual(sample["final"]["main"]["contents"], [])
                    self.assertEqual(sample["saved"][0][:2], ["built", "main"])
                    self.assertEqual(sorted(map(int, sample["saved"][0][2]["contents"])), sorted(keys))
                    if implementation == "binomial":
                        self.assertEqual(sample["final"]["main"]["slots"], 3)
                        self.assertEqual(sample["final"]["main"]["forest"], [[None]] * 3)
                    else:
                        self.assertIsNone(sample["final"]["main"]["slots"])
                        self.assertIsNone(sample["final"]["main"]["forest"])

    def test_generated_drain(self):
        keys = [10, 0, 10, 11, 6, 10, 0, 0]
        receipts = []
        for implementation in ("binomial", "list"):
            with self.subTest(implementation=implementation):
                result = self.invoke("binom-workload", "--implementation", implementation,
                                     "--pattern", "random", "--size", "8", "--universe", "13",
                                     "--seed", "1729", "--warmups", "1", "--repetitions", "2")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                receipt = json.loads(result.stdout)
                receipts.append(receipt)
                self.assertEqual(receipt["config"]["keysFile"], None)
                samples = receipt["samples"]
                self.assertEqual([(sample["phase"], sample["index"]) for sample in samples],
                                 [("warmup", 0), ("measured", 0), ("measured", 1)])
                for sample in samples:
                    self.assertEqual(sample["keys"], list(map(str, keys)))
                    self.assertEqual(sample["generator"], {
                        "name": "StdGen/mkStdGen/randNat", "initial": [1730, 1],
                        "final": [1689113473, 525453832], "draws": 8})
                    self.assertEqual([removal[2] for removal in sample["removals"]],
                                     list(map(str, sorted(keys, reverse=True))) + [None])
                    self.assertEqual(sample["final"]["main"]["contents"], [])
                    self.assertEqual(sorted(map(int, sample["saved"][0][2]["contents"])), sorted(keys))
                    self.assertGreaterEqual(sample["elapsedNs"], 0)
        if len(receipts) == 2:
            self.assertEqual(receipts[0]["samples"][0]["operations"],
                             receipts[1]["samples"][0]["operations"])

    def test_deterministic_patterns(self):
        # Ordered inputs have no random generator: their complete key sequence
        # is fixed by size, and all-equal inputs exercise every tie repeatedly.
        with tempfile.TemporaryDirectory(prefix="binom-patterns-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for pattern, keys in (("ascending", list(range(9))),
                                  ("descending", list(reversed(range(9)))),
                                  ("equal", [0] * 9)):
                for implementation in ("binomial", "list"):
                    with self.subTest(pattern=pattern, implementation=implementation):
                        result = self.invoke("binom-workload", "--implementation", implementation,
                                             "--pattern", pattern, "--size", "9",
                                             "--schedule", "merge", "--warmups", "1", "--repetitions", "2")
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        receipt = json.loads(result.stdout)
                        self.assertEqual(receipt["config"]["pattern"], pattern)
                        for sample in receipt["samples"]:
                            self.assertEqual(sample["keys"], list(map(str, keys)))
                            self.assertIsNone(sample["generator"])
                        receipt_path.write_text(result.stdout, encoding="utf-8")
                        observed = self.observe(receipt_path)
                        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                        changed = copy.deepcopy(receipt)
                        changed["config"]["pattern"] = "descending" if pattern != "descending" else "ascending"
                        receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                        self.assert_observer_rejected(self.observe(receipt_path))

        with tempfile.TemporaryDirectory(prefix="binom-pattern-endpoints-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for pattern in ("ascending", "descending", "equal"):
                for size in (0, 1):
                    result = self.invoke("binom-workload", "--pattern", pattern, "--size", str(size))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    receipt = json.loads(result.stdout)
                    self.assertEqual(receipt["samples"][0]["keys"], ["0"] * size)
                    receipt_path.write_text(result.stdout, encoding="utf-8")
                    observed = self.observe(receipt_path)
                    self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                for flag, value in (("--seed", "1729"), ("--universe", "32")):
                    result = self.invoke("binom-workload", "--pattern", pattern, "--size", "0", flag, value)
                    self.assert_rejected(result)
                    self.assertIn("do not accept random generator options", result.stderr)
                result = self.invoke("binom-workload", "--pattern", pattern, "--size", "0",
                                     "--keys-file", "unused-deterministic-file")
                self.assert_rejected(result)
                self.assertIn("key files require", result.stderr)
            for pattern in ("ascending", "descending"):
                result = self.invoke("binom-workload", "--pattern", pattern, "--size", str((1 << 63) + 1))
                self.assert_rejected(result)
                self.assertIn("ordered input size exceeds", result.stderr)

    def test_comparative_measurement(self):
        # Finite, explicitly sized comparative observations; no elapsed-time
        # threshold or asymptotic/native-allocation conclusion is asserted.
        # The command retains all raw warmup/measured timings and queue states.
        with tempfile.TemporaryDirectory(prefix="binom-comparison-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for size_index, size in enumerate((32, 128, 512)):
                for schedule_index, schedule in enumerate(("drain", "mixed", "merge", "padding")):
                    order = ("binomial", "list") if (size_index + schedule_index) % 2 == 0 else ("list", "binomial")
                    paired = {}
                    for implementation in order:
                        with self.subTest(size=size, schedule=schedule, implementation=implementation):
                            result = self.invoke("binom-workload", "--implementation", implementation,
                                                 "--pattern", "random", "--size", str(size),
                                                 "--universe", "17", "--seed", "1729", "--schedule", schedule,
                                                 "--warmups", "1", "--repetitions", "3")
                            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                            receipt = json.loads(result.stdout)
                            self.assertEqual([(sample["phase"], sample["index"]) for sample in receipt["samples"]],
                                             [("warmup", 0), ("measured", 0), ("measured", 1), ("measured", 2)])
                            receipt_path.write_text(result.stdout, encoding="utf-8")
                            observed = self.observe(receipt_path)
                            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                            sample = receipt["samples"][0]
                            paired[implementation] = (sample["keys"], sample["operations"], sample["removals"],
                                                      {name: sorted(state["contents"], key=int)
                                                       for name, state in sample["final"].items()},
                                                      [(label, name, sorted(state["contents"], key=int))
                                                       for label, name, state in sample["saved"]])
                    self.assertEqual(set(paired), {"binomial", "list"})
                    self.assertEqual(paired["binomial"], paired["list"])

    def test_generated_observer(self):
        with tempfile.TemporaryDirectory(prefix="binom-generated-observer-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for implementation in ("binomial", "list"):
                with self.subTest(implementation=implementation):
                    result = self.invoke("binom-workload", "--implementation", implementation,
                                         "--pattern", "random", "--size", "8", "--universe", "13",
                                         "--seed", "1729", "--warmups", "1", "--repetitions", "2")
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    original = json.loads(result.stdout)
                    receipt_path.write_text(result.stdout, encoding="utf-8")
                    observed = self.observe(receipt_path)
                    self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                    self.assertEqual(json.loads(observed.stdout), {
                        "schema": 1, "status": "accepted", "kind": "binomial-workload", "samples": 3})
                    for location, value in [(("generator", "name"), "different"),
                                            (("generator", "draws"), 9),
                                            (("generator", "initial", 0), 1729),
                                            (("generator", "final", 0), 0),
                                            (("elapsedNs",), True), (("index",), True)]:
                        changed = copy.deepcopy(original)
                        parent = changed["samples"][0]
                        for key in location[:-1]:
                            parent = parent[key]
                        parent[location[-1]] = value
                        receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                        self.assert_observer_rejected(self.observe(receipt_path))

    def test_mixed_merge_padding(self):
        keys = [7, 2, 7, 0, 3]
        expected = {
            "mixed": ["7", "7", "3", "2", "0", None, None, None, None],
            "merge": ["7", "2", "7", "7", "3", "2", "0", None],
            "padding": ["7", "7", "3", "2", "0", None, "0", None],
        }
        with tempfile.TemporaryDirectory(prefix="binom-schedules-") as folder:
            path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            path.write_text("".join(f"{key}\n" for key in keys), encoding="utf-8")
            for schedule in ("mixed", "merge", "padding"):
                observations = []
                for implementation in ("binomial", "list"):
                    with self.subTest(schedule=schedule, implementation=implementation):
                        result = self.invoke("binom-workload", "--implementation", implementation,
                                             "--pattern", "replay", "--keys-file", str(path),
                                             "--schedule", schedule)
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        receipt = json.loads(result.stdout)
                        sample = receipt["samples"][0]
                        self.assertEqual(receipt["config"]["schedule"], schedule)
                        self.assertEqual([item[2] for item in sample["removals"]], expected[schedule])
                        self.assertEqual(sample["final"]["main"]["contents"], [])
                        if schedule == "merge":
                            self.assertEqual(sorted(map(int, sample["final"]["left"]["contents"])), [3, 7])
                            self.assertEqual(sample["final"]["right"]["contents"], ["0"])
                            self.assertEqual([item[:2] for item in sample["saved"]],
                                             [["left-before", "left"], ["right-before", "right"], ["merged", "main"]])
                        elif schedule == "padding" and implementation == "binomial":
                            self.assertEqual(sample["saved"][1][:2], ["drained", "main"])
                            self.assertEqual(sample["saved"][1][2]["contents"], [])
                            self.assertEqual(sample["saved"][1][2]["slots"], 3)
                            self.assertEqual(sample["final"]["main"]["slots"], 3)
                        receipt_path.write_text(result.stdout, encoding="utf-8")
                        observed = self.observe(receipt_path)
                        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                        observations.append((sample["keys"], sample["operations"], sample["removals"]))
                if len(observations) == 2:
                    self.assertEqual(observations[0], observations[1])

    def test_replay_observer(self):
        with tempfile.TemporaryDirectory(prefix="binom-receipt-") as folder:
            path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            for keys in ([3, 1, 3, 0], [], [0], [-(1 << 63), -1, (1 << 63) - 1, 0, -1]):
                path.write_text("".join(f"{key}\n" for key in keys), encoding="utf-8")
                for implementation in ("binomial", "list"):
                    with self.subTest(keys=keys, implementation=implementation):
                        result = self.invoke("binom-workload", "--implementation", implementation,
                                             "--pattern", "replay", "--keys-file", str(path))
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        original = json.loads(result.stdout)
                        receipt_path.write_text(result.stdout, encoding="utf-8")
                        observed = self.observe(receipt_path)
                        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                        self.assertEqual(json.loads(observed.stdout), {
                            "schema": 1, "status": "accepted", "kind": "binomial-workload", "samples": 1})
                        changed = copy.deepcopy(original)
                        changed["samples"][0]["removals"][-1][2] = "0"
                        receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                        self.assert_observer_rejected(self.observe(receipt_path))
                        if keys:
                            changed = copy.deepcopy(original)
                            changed["samples"][0]["saved"][0][2]["contents"].pop()
                            receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                            self.assert_observer_rejected(self.observe(receipt_path))
                        if implementation == "binomial":
                            changed = copy.deepcopy(original)
                            changed["samples"][0]["final"]["main"]["slots"] += 1
                            receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                            self.assert_observer_rejected(self.observe(receipt_path))

    def _binom_run_observed(self, receipt_path, *options):
        result = self.invoke("binom-workload", *options)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads(result.stdout)
        self.assertEqual((receipt["schema"], receipt["kind"]), (3, "binomial-workload"))
        receipt_path.write_text(result.stdout, encoding="utf-8")
        observed = self.observe(receipt_path)
        self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
        self.assertEqual(json.loads(observed.stdout), {
            "schema": 1, "status": "accepted", "kind": "binomial-workload",
            "samples": receipt["config"]["warmups"] + receipt["config"]["repetitions"],
        })
        return receipt

    def _binom_compare_receipts(self, first, second):
        # Shape/order may differ; literal inputs, public events, every removal,
        # generator evidence and every saved/final occurrence bag must agree.
        self.assertEqual(len(first["samples"]), len(second["samples"]))
        for left, right in zip(first["samples"], second["samples"]):
            for field in ("phase", "index", "keys", "operations", "removals", "generator"):
                self.assertEqual(typed_json(left[field]), typed_json(right[field]), field)
            for name in ("main", "left", "right"):
                self.assertEqual(Counter(left["final"][name]["contents"]),
                                 Counter(right["final"][name]["contents"]), name)
            self.assertEqual(len(left["saved"]), len(right["saved"]))
            for old_left, old_right in zip(left["saved"], right["saved"]):
                self.assertEqual(old_left[:2], old_right[:2])
                self.assertEqual(Counter(old_left[2]["contents"]),
                                 Counter(old_right[2]["contents"]))

    def _binom_set_path(self, receipt, location, value):
        parent = receipt
        for key in location[:-1]:
            parent = parent[key]
        parent[location[-1]] = copy.deepcopy(value)

    def _binom_reject_edit(self, receipt_path, original, label, edit, reason=None):
        with self.subTest(mutation=label):
            changed = copy.deepcopy(original)
            edit(changed)
            receipt_path.write_text(json.dumps(changed), encoding="utf-8")
            observed = self.observe(receipt_path)
            self.assert_observer_rejected(observed)
            if reason is not None:
                self.assertIn(reason, observed.stderr)

    def test_binom_rejects_cli_shape_and_bad_counts(self):
        options = [
            ("--implementation", "list"), ("--pattern", "random"),
            ("--schedule", "drain"), ("--size", "0"), ("--universe", "1"),
            ("--seed", "0"), ("--warmups", "0"), ("--repetitions", "1"),
            ("--keys-file", "unused-replay-path"),
        ]
        for flag, value in options:
            with self.subTest(case="missing-value", flag=flag):
                result = self.invoke("binom-workload", flag)
                self.assert_rejected(result)
                self.assertIn("missing value", result.stderr)
            with self.subTest(case="duplicate", flag=flag):
                result = self.invoke("binom-workload", flag, value, flag, value)
                self.assert_rejected(result)
                self.assertIn("duplicate option", result.stderr)
        for options, reason in [
            (("--not-an-option", "0"), "unknown option"),
            (("--implementation", "map"), "unsupported implementation"),
            (("--pattern", "not-a-pattern"), "unsupported binomial pattern"),
            (("--schedule", "not-a-schedule"), "unsupported binomial schedule"),
            (("--size", "1.5"), "natural number"),
            (("--size", "0", "--repetitions", "0"), "repetitions must be positive"),
            (("--size", "1", "--universe", "0"), "positive universe"),
            (("--size", "0", "--universe", str((1 << 63) + 1)), "signed positive capacity"),
            (("--size", "1", "--universe", str((1 << 63) + 1)), "signed positive capacity"),
        ]:
            with self.subTest(options=options):
                result = self.invoke("binom-workload", *options)
                self.assert_rejected(result)
                self.assertIn(reason, result.stderr)
        for flag in ("--size", "--universe", "--seed", "--warmups", "--repetitions"):
            with self.subTest(case="negative-natural", flag=flag):
                result = self.invoke("binom-workload", flag, "-1")
                self.assert_rejected(result)
                self.assertIn("natural number", result.stderr)

    def test_binom_rejects_replay_text_range_and_option_mixing(self):
        with tempfile.TemporaryDirectory(prefix="binom-reject-replay-") as folder:
            keys_path = Path(folder) / "keys.txt"
            keys_path.write_text("0\n", encoding="utf-8")
            base = ("--pattern", "replay", "--keys-file", str(keys_path))
            result = self.invoke("binom-workload", "--pattern", "replay")
            self.assert_rejected(result)
            self.assertIn("requires --keys-file", result.stderr)
            for flag, value in (("--size", "0"), ("--universe", "32"), ("--seed", "1729")):
                # Supplying even a default value is forbidden in replay mode.
                with self.subTest(case="replay-generator-option", flag=flag):
                    result = self.invoke("binom-workload", *base, flag, value)
                    self.assert_rejected(result)
                    self.assertIn("does not accept generator options", result.stderr)
            result = self.invoke("binom-workload", "--pattern", "random", "--size", "0",
                                 "--keys-file", str(keys_path))
            self.assert_rejected(result)
            self.assertIn("key files require --pattern replay", result.stderr)
            missing = Path(folder) / "does-not-exist.txt"
            self.assert_rejected(self.invoke("binom-workload", "--pattern", "replay",
                                             "--keys-file", str(missing)))
            for text in ("not-a-number\n", "1.5\n", "0x10\n", "1e3\n", "1 2\n",
                         "1\n\n2\n", "1\n+\n", "1\n-\n", "\u22121\n"):
                keys_path.write_text(text, encoding="utf-8")
                with self.subTest(case="invalid-decimal", text=text):
                    result = self.invoke("binom-workload", *base)
                    self.assert_rejected(result)
                    self.assertIn("invalid decimal key", result.stderr)
            for key in (-(1 << 63) - 1, 1 << 63, 10 ** 80):
                keys_path.write_text(f"0\n{key}\n", encoding="utf-8")
                for implementation in ("binomial", "list"):
                    with self.subTest(case="out-of-signed-range", key=key,
                                      implementation=implementation):
                        result = self.invoke("binom-workload", *base,
                                             "--implementation", implementation)
                        self.assert_rejected(result)
                        self.assertIn("outside the signed range", result.stderr)

    def test_binom_generated_domain_boundary(self):
        # The generator domain is [0, universe), so universe=2^63 is legal.
        # The keys themselves must be strictly below 2^63. No huge workload is run.
        with tempfile.TemporaryDirectory(prefix="binom-domain-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for size, universe in ((0, 0), (0, 1 << 63), (3, 1 << 63)):
                pair = []
                for implementation in ("binomial", "list"):
                    with self.subTest(size=size, universe=universe, implementation=implementation):
                        receipt = self._binom_run_observed(
                            receipt_path, "--implementation", implementation,
                            "--pattern", "random", "--size", str(size),
                            "--universe", str(universe), "--seed", "0")
                        sample = receipt["samples"][0]
                        self.assertEqual(len(sample["keys"]), size)
                        self.assertTrue(all(0 <= int(key) < universe for key in sample["keys"]))
                        if size == 0:
                            self.assertEqual(sample["generator"]["draws"], 0)
                            self.assertEqual(sample["generator"]["initial"],
                                             sample["generator"]["final"])
                            self.assertEqual(sample["removals"], [[1, "main", None]])
                        pair.append(receipt)
                self._binom_compare_receipts(*pair)

    def test_binom_all_schedules_empty_singleton_and_signed_edges(self):
        # Covers N=0, N=1, negative odd parity, both signed endpoints and
        # duplicate minima/maxima without adding deterministic pattern modes.
        cases = [[], [0], [-1], [-(1 << 63), (1 << 63) - 1, -(1 << 63), 0, -1, 7, 7]]
        empty_removals = {
            "drain": [None], "mixed": [None], "merge": [None, None, None],
            "padding": [None, "0", None],
        }
        zero_removals = {
            "drain": ["0", None], "mixed": ["0", None],
            "merge": ["0", None, "0", None], "padding": ["0", None, "0", None],
        }
        with tempfile.TemporaryDirectory(prefix="binom-small-schedules-") as folder:
            keys_path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            for keys in cases:
                key_bytes = "".join(f"{key}\n" for key in keys).encode()
                keys_path.write_bytes(key_bytes)
                for schedule in ("drain", "mixed", "merge", "padding"):
                    pair = []
                    for implementation in ("binomial", "list"):
                        with self.subTest(keys=keys, schedule=schedule, implementation=implementation):
                            receipt = self._binom_run_observed(
                                receipt_path, "--implementation", implementation,
                                "--pattern", "replay", "--keys-file", str(keys_path),
                                "--schedule", schedule)
                            self.assertEqual(keys_path.read_bytes(), key_bytes)
                            self.assertEqual(receipt["config"]["size"], len(keys))
                            sample = receipt["samples"][0]
                            self.assertEqual(sample["keys"], list(map(str, keys)))
                            self.assertIsNone(sample["generator"])
                            self.assertEqual(sample["final"]["main"]["contents"], [])
                            removed = [record[2] for record in sample["removals"]]
                            if not keys:
                                self.assertEqual(removed, empty_removals[schedule])
                            elif keys == [0]:
                                self.assertEqual(removed, zero_removals[schedule])
                            elif keys == [-1] and schedule == "mixed":
                                self.assertEqual(removed, ["-1", None, None])
                            if implementation == "binomial" and schedule in ("drain", "padding"):
                                peak = len(keys).bit_length()
                                final_slots = max(peak, 1) if schedule == "padding" else peak
                                self.assertEqual(sample["final"]["main"]["slots"], final_slots)
                                self.assertEqual(sample["final"]["main"]["forest"], [[None]] * final_slots)
                                if schedule == "padding":
                                    drained = sample["saved"][1]
                                    self.assertEqual(drained[:2], ["drained", "main"])
                                    self.assertEqual(drained[2]["contents"], [])
                                    self.assertEqual(drained[2]["slots"], peak)
                            pair.append(receipt)
                    self._binom_compare_receipts(*pair)

    def test_binom_random_schedules_repeat_and_compare(self):
        # Bounded logical workloads, not wall-clock/process resource limits.
        # Universe=1 forces duplicates; a large Nat seed is not an Int64 key.
        cases = [(0, 0, 0), (1, 1, 0), (8, 1, 31), (9, 3, 0),
                 (16, 5, 1729), (7, 7, (1 << 70) + 17)]
        with tempfile.TemporaryDirectory(prefix="binom-random-schedules-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            for size, universe, seed in cases:
                for schedule in ("drain", "mixed", "merge", "padding"):
                    pair = []
                    for implementation in ("binomial", "list"):
                        with self.subTest(size=size, universe=universe, seed=seed,
                                          schedule=schedule, implementation=implementation):
                            receipt = self._binom_run_observed(
                                receipt_path, "--implementation", implementation, "--pattern", "random",
                                "--size", str(size), "--universe", str(universe), "--seed", str(seed),
                                "--schedule", schedule, "--warmups", "1", "--repetitions", "2")
                            self.assertEqual([(sample["phase"], sample["index"])
                                              for sample in receipt["samples"]],
                                             [("warmup", 0), ("measured", 0), ("measured", 1)])
                            for sample in receipt["samples"]:
                                self.assertEqual(len(sample["keys"]), size)
                                self.assertTrue(all(0 <= int(key) < universe for key in sample["keys"]))
                                self.assertEqual(sample["generator"]["draws"], size)
                                if universe == 1:
                                    self.assertEqual(sample["keys"], ["0"] * size)
                                if size == 0:
                                    self.assertEqual(sample["generator"]["initial"],
                                                     sample["generator"]["final"])
                            pair.append(receipt)
                    self._binom_compare_receipts(*pair)

    def test_binom_observer_rejects_raw_forest_corruption(self):
        with tempfile.TemporaryDirectory(prefix="binom-raw-mutations-") as folder:
            keys_path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            keys_path.write_text("7\n1\n7\n2\n", encoding="utf-8")
            original = self._binom_run_observed(receipt_path, "--pattern", "replay",
                                                "--keys-file", str(keys_path))
            saved_path = ("samples", 0, "saved", 0, 2)
            state = original["samples"][0]["saved"][0][2]
            self.assertEqual(state["forest"], [
                [None], [None], ["7", "7", "2", None, None, "1", None, None, None]])

            def saved(receipt):
                return receipt["samples"][0]["saved"][0][2]

            def sync_contents(state):
                # This only reads the flat serialized labels, not queue operations.
                state["contents"] = [key for tree in state["forest"] for key in tree if key is not None]

            def wrong_rank(receipt):
                forest = saved(receipt)["forest"]
                forest[0], forest[2] = forest[2], forest[0]

            def heap_violation(receipt):
                state = saved(receipt)
                tree = state["forest"][2]
                tree[0], tree[2] = tree[2], tree[0]
                sync_contents(state)

            mutations = [
                ("truncated-tree", lambda r: saved(r)["forest"][2].pop(), "incomplete tree observation"),
                ("extra-tree-token", lambda r: saved(r)["forest"][2].append(None), "unused tree tokens"),
                ("missing-slot", lambda r: saved(r)["forest"].pop(), "forest length differs"),
                ("extra-slot", lambda r: saved(r)["forest"].append([None]), "forest length differs"),
                ("rank-mismatch", wrong_rank, "rank-zero child spine is not empty"),
                ("outer-right-sibling",
                 lambda r: self._binom_set_path(r, saved_path + ("forest", 2),
                                               ["7", "7", "2", None, None, None, "1", None, None]),
                 "outer right sibling"),
                ("insufficient-inner-rank",
                 lambda r: self._binom_set_path(r, saved_path + ("forest", 2),
                                               ["7", "7", None, "2", "1", None, None, None, None]),
                 "child spine has insufficient rank"),
                ("heap-order-with-same-bag", heap_violation, "heap bound is violated"),
                ("contents-order-not-raw-preorder", lambda r: saved(r)["contents"].reverse(),
                 "contents disagree with the raw forest"),
                ("tree-token-not-decimal", lambda r: saved(r)["forest"][2].__setitem__(0, True),
                 "canonical decimal string"),
            ]
            for label, edit, reason in mutations:
                self._binom_reject_edit(receipt_path, original, label, edit, reason)

    def test_binom_observer_rejects_bags_slots_and_saved_states(self):
        with tempfile.TemporaryDirectory(prefix="binom-state-mutations-") as folder:
            keys_path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            keys_path.write_text("7\n2\n7\n0\n3\n", encoding="utf-8")
            for implementation in ("binomial", "list"):
                with self.subTest(implementation=implementation):
                    original = self._binom_run_observed(
                        receipt_path, "--implementation", implementation, "--pattern", "replay",
                        "--keys-file", str(keys_path), "--schedule", "merge")

                    def sample(receipt):
                        return receipt["samples"][0]

                    mutations = [
                        ("lost-duplicate-in-saved-left",
                         lambda r: sample(r)["saved"][0][2]["contents"].remove("7")),
                        ("spurious-final-occurrence", lambda r: sample(r)["final"]["main"]["contents"].append("0")),
                        ("saved-label-changed", lambda r: sample(r)["saved"][0].__setitem__(0, "after")),
                        ("saved-queue-changed", lambda r: sample(r)["saved"][0].__setitem__(1, "right")),
                        ("missing-saved-version", lambda r: sample(r)["saved"].pop()),
                        ("extra-saved-version", lambda r: sample(r)["saved"].append(copy.deepcopy(sample(r)["saved"][0]))),
                        ("saved-versions-reordered", lambda r: sample(r)["saved"].reverse()),
                        ("old-left-overwritten-by-deleted-left",
                         lambda r: sample(r)["saved"][0].__setitem__(2, copy.deepcopy(sample(r)["final"]["left"]))),
                        ("old-merged-overwritten-by-drained-main",
                         lambda r: sample(r)["saved"][2].__setitem__(2, copy.deepcopy(sample(r)["final"]["main"]))),
                    ]
                    if implementation == "binomial":
                        mutations += [
                            ("stored-capacity-changed", lambda r: sample(r)["final"]["main"].__setitem__("slots", 4)),
                            ("boolean-slot-count", lambda r: sample(r)["final"]["left"].__setitem__("slots", True)),
                            ("padding-silently-trimmed", lambda r: sample(r)["final"]["main"].__setitem__("forest", [])),
                        ]
                    else:
                        mutations += [
                            ("list-fabricated-slots", lambda r: sample(r)["final"]["main"].__setitem__("slots", 0)),
                            ("list-fabricated-forest", lambda r: sample(r)["final"]["main"].__setitem__("forest", [])),
                        ]
                    for label, edit in mutations:
                        self._binom_reject_edit(receipt_path, original, label, edit)

    def test_binom_observer_rejects_schema_and_noncanonical_decimals(self):
        with tempfile.TemporaryDirectory(prefix="binom-schema-mutations-") as folder:
            receipt_path = Path(folder) / "receipt.json"
            original = self._binom_run_observed(receipt_path, "--pattern", "random",
                                                "--size", "4", "--universe", "3", "--seed", "31")
            object_locations = [
                ((), "unit"), (("config",), "size"), (("samples", 0), "removals"),
                (("samples", 0, "final"), "left"),
                (("samples", 0, "final", "main"), "forest"),
                (("samples", 0, "saved", 0, 2), "contents"),
                (("samples", 0, "generator"), "draws"),
            ]

            def alter_member(receipt, location, field, remove):
                parent = receipt
                for key in location:
                    parent = parent[key]
                if remove:
                    parent.pop(field)
                else:
                    parent["unexpected"] = 0

            for location, field in object_locations:
                for remove in (True, False):
                    self._binom_reject_edit(
                        receipt_path, original, (location, "missing" if remove else "extra"),
                        lambda r, loc=location, name=field, drop=remove: alter_member(r, loc, name, drop))
            for text in ("00", "-0", "+1", "01", "1.0", "1e0", " 1", "1 ", 1, True, None):
                self._binom_reject_edit(
                    receipt_path, original, ("noncanonical-key", text),
                    lambda r, value=text: self._binom_set_path(r, ("samples", 0, "keys", 0), value),
                    "canonical decimal string")
            for location, value in [
                (("schema",), 3.0), (("schema",), True), (("kind",), "binomial-workloads"),
                (("clock",), "process-cpu"), (("unit",), "ms"), (("timedRegion",), "whole process"),
                (("config", "size"), True), (("config", "warmups"), -1),
                (("config", "repetitions"), 0), (("config", "carrier"), "word63"),
                (("config", "implementation"), "map"), (("config", "schedule"), "not-a-schedule"),
                (("config", "keysFile"), "unexpected-file"),
                (("samples", 0, "elapsedNs"), -1), (("samples", 0, "elapsedNs"), 1.0),
                (("samples", 0, "phase"), "warmup"), (("samples", 0, "index"), 1),
                (("samples", 0, "saved", 0, 2, "contents", 0), "00"),
            ]:
                self._binom_reject_edit(
                    receipt_path, original, (location, value),
                    lambda r, loc=location, new=value: self._binom_set_path(r, loc, new))
            # Duplicate JSON members and non-finite numbers are loader errors,
            # distinct from a missing/extra member in an already parsed object.
            text = json.dumps(original, separators=(",", ":"))
            for label, changed in [
                ("duplicate-schema", text.replace('"schema":3', '"schema":3,"schema":3', 1)),
                ("nonfinite-elapsed", re.sub(r'"elapsedNs":\d+', '"elapsedNs":NaN', text, count=1)),
            ]:
                with self.subTest(mutation=label):
                    self.assertNotEqual(changed, text)
                    receipt_path.write_text(changed, encoding="utf-8")
                    self.assert_observer_rejected(self.observe(receipt_path))

    def test_binom_observer_rejects_input_event_and_removal_tampering(self):
        with tempfile.TemporaryDirectory(prefix="binom-trace-mutations-") as folder:
            keys_path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            keys_path.write_text("7\n2\n7\n0\n3\n", encoding="utf-8")
            original = self._binom_run_observed(
                receipt_path, "--implementation", "list", "--pattern", "replay",
                "--keys-file", str(keys_path), "--schedule", "merge")
            first = original["samples"][0]
            merge_index = next(i for i, event in enumerate(first["operations"]) if event[0] == "merge")

            def sample(receipt):
                return receipt["samples"][0]

            mutations = [
                ("input-key-changed", lambda r: sample(r)["keys"].__setitem__(0, "8")),
                ("input-key-missing", lambda r: sample(r)["keys"].pop()),
                ("input-order-changed", lambda r: sample(r)["keys"].reverse()),
                ("event-missing", lambda r: sample(r)["operations"].pop(0)),
                ("event-extra", lambda r: sample(r)["operations"].append(["delete", "main"])),
                ("event-action-changed", lambda r: sample(r)["operations"][0].__setitem__(0, "drop")),
                ("insert-destination-changed", lambda r: sample(r)["operations"][0].__setitem__(1, "main")),
                ("insert-key-changed", lambda r: sample(r)["operations"][0].__setitem__(2, "8")),
                ("merge-destination-changed", lambda r: sample(r)["operations"][merge_index].__setitem__(1, "left")),
                ("merge-operands-swapped", lambda r: sample(r)["operations"].__setitem__(
                    merge_index, ["merge", "main", "right", "left"])),
                ("removal-key-changed", lambda r: sample(r)["removals"][0].__setitem__(2, "2")),
                ("removal-index-changed", lambda r: sample(r)["removals"][0].__setitem__(0, 0)),
                ("removal-destination-changed", lambda r: sample(r)["removals"][0].__setitem__(1, "right")),
                ("none-replaced-by-zero", lambda r: sample(r)["removals"][-1].__setitem__(2, "0")),
                ("removal-missing", lambda r: sample(r)["removals"].pop()),
                ("removal-extra", lambda r: sample(r)["removals"].append(copy.deepcopy(sample(r)["removals"][0]))),
                ("removals-reordered", lambda r: sample(r)["removals"].reverse()),
                ("replay-fabricates-generator", lambda r: sample(r).__setitem__("generator", {})),
            ]
            for label, edit in mutations:
                self._binom_reject_edit(receipt_path, original, label, edit)

    def test_binom_observer_rejects_nonrepeatable_valid_snapshots(self):
        # Each changed snapshot is a valid representation of the same bag.
        # Accept it alone, then require rejection only when repetitions differ.
        with tempfile.TemporaryDirectory(prefix="binom-repeat-mutations-") as folder:
            keys_path, receipt_path = [Path(folder) / name for name in ("keys.txt", "receipt.json")]
            keys_path.write_text("7\n1\n7\n2\n", encoding="utf-8")
            for implementation in ("binomial", "list"):
                with self.subTest(implementation=implementation):
                    original = self._binom_run_observed(
                        receipt_path, "--implementation", implementation,
                        "--pattern", "replay", "--keys-file", str(keys_path), "--repetitions", "2")
                    changed = copy.deepcopy(original)
                    state = changed["samples"][1]["saved"][0][2]
                    if implementation == "binomial":
                        tree = state["forest"][2]
                        self.assertEqual(tree, ["7", "7", "2", None, None, "1", None, None, None])
                        tree[2], tree[5] = tree[5], tree[2]
                        state["contents"] = [key for raw in state["forest"] for key in raw if key is not None]
                    else:
                        state["contents"].reverse()
                    self.assertNotEqual(typed_json(changed["samples"][0]["saved"]),
                                        typed_json(changed["samples"][1]["saved"]))
                    isolated = copy.deepcopy(changed)
                    isolated["config"]["repetitions"] = 1
                    isolated["samples"] = [copy.deepcopy(changed["samples"][1])]
                    isolated["samples"][0]["index"] = 0
                    receipt_path.write_text(json.dumps(isolated), encoding="utf-8")
                    observed = self.observe(receipt_path)
                    self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                    self.assertEqual(json.loads(observed.stdout), {
                        "schema": 1, "status": "accepted", "kind": "binomial-workload", "samples": 1})
                    receipt_path.write_text(json.dumps(changed), encoding="utf-8")
                    observed = self.observe(receipt_path)
                    self.assert_observer_rejected(observed)
                    self.assertIn("repeats changed", observed.stderr)


if __name__ == "__main__":
    if "--check-receipt" in sys.argv[1:]:
        try:
            if len(sys.argv) != 3 or sys.argv[1] != "--check-receipt":
                raise ValueError("usage: test-extract-searchtree.py --check-receipt FILE")
            print(json.dumps(check_receipt(Path(sys.argv[2])), allow_nan=False))
        except (OSError, UnicodeError, ValueError, TypeError, RecursionError) as error:
            print(f"receipt rejected: {error}", file=sys.stderr)
            raise SystemExit(1)
    else:
        unittest.main()

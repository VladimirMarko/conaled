"""Independent finite source-call/choice enumeration, not Lean validation."""

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path
import hashlib
import json


def length_run(xs):
    if not xs:
        return 0, 1
    n, calls = length_run(xs[1:])
    return n + 1, calls + 1


def lookup_run(xs, index):
    if index == 0:
        return xs[0], 1
    value, calls = lookup_run(xs[1:], index - 1)
    return value, calls + 1


def partition_run(pivot, xs):
    if not xs:
        return ((), (), ()), 1
    (left, equal, right), calls = partition_run(pivot, xs[1:])
    x = xs[0]
    if x < pivot:
        left = (x,) + left
    elif x == pivot:
        equal = (x,) + equal
    else:
        right = (x,) + right
    return (left, equal, right), calls + 1


def step(k, xs, index):
    n, size_calls = length_run(xs)
    pivot, lookup_calls = lookup_run(xs, index)
    (left, equal, right), partition_calls = partition_run(pivot, xs)
    nl, left_calls = length_run(left)
    calls = 1 + size_calls + lookup_calls + partition_calls + left_calls
    if k < nl:
        return {"child": (k, left), "calls": calls, "pivot": pivot}
    ne, equal_calls = length_run(equal)
    calls += equal_calls
    if k < nl + ne:
        return {"value": pivot, "calls": calls, "pivot": pivot}
    return {"child": (k - nl - ne, right), "calls": calls, "pivot": pivot}


@lru_cache(None)
def run(k, xs):
    if not xs:
        return {(None, (), 1 + length_run(xs)[1]): Fraction(1)}
    n = len(xs)
    outcomes = defaultdict(Fraction)
    for i in range(n):
        action = step(k, xs, i)
        if "value" in action:
            outcomes[(action["value"], ((n, i),), action["calls"])] += Fraction(1, n)
        else:
            j, child = action["child"]
            for (value, trace, calls), mass in run(j, child).items():
                outcomes[(value, ((n, i),) + trace, action["calls"] + calls)] += mass / n
    assert sum(outcomes.values()) == 1
    return dict(outcomes)


def endpoint(k, xs):
    original_k, original_xs = k, xs
    choices, trace, calls, path_mass = [], (), 0, Fraction(1)
    while xs:
        pivot = min(xs) if k > 0 else max(xs)
        i = xs.index(pivot)
        action = step(k, xs, i)
        choices.append({"input": xs, "rank": k, "index": i, **action})
        trace += ((len(xs), i),)
        calls += action["calls"]
        path_mass /= len(xs)
        if "value" in action:
            outcome = (action["value"], trace, calls)
            break
        k, xs = action["child"]
    else:
        outcome = (None, trace, calls + 1 + length_run(xs)[1])
    actual_atom = run(original_k, original_xs)[outcome]
    return {
        "input": original_xs,
        "rank": original_k,
        "choices": choices,
        "outcome": outcome,
        "scan": sum(n for n, _ in trace),
        "path_mass": str(path_mass),
        "actual_uniform_run_atom": str(actual_atom),
    }


rows = []
for n in range(1, 6):
    for xs in permutations(range(n)):
        for k in range(n):
            row = endpoint(k, xs)
            assert row["outcome"][0] == sorted(xs)[k]
            assert row["scan"] == n * (n + 1) // 2
            assert row["path_mass"] == row["actual_uniform_run_atom"] == str(Fraction(1, factorial(n)))
            assert row["scan"] <= row["outcome"][2] <= 9 * row["scan"] + 2
            assert [len(c["input"]) for c in row["choices"]] == list(range(n, 0, -1))
            rows.append(row)

illustrative = [endpoint(k, xs) for xs, k in [
    ((7,), 0), ((1, 0), 0), ((1, 0), 1),
    ((3, 1, 2), 0), ((3, 1, 2), 1), ((3, 1, 2), 2),
    ((4, 1, 3, 2), 0), ((4, 1, 3, 2), 3),
    ((3, -2, 8, 0, 5), 0), ((3, -2, 8, 0, 5), 3),
    ((4, 4, 4), 1), ((), 0), ((7,), 1),
]]
result = {
    "scope": "Independent expected cases, saved before any new Lean source; no universal proof or compiler credit.",
    "model": "Recursively count actual length, lookup and stable partition calls, execute actual branch tests, and enumerate every fresh current occurrence with exact Fraction mass.",
    "distinct_permutation_rank_cases": len(rows),
    "exhaustive_rows_sha256": hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
    "sizes": [1, 2, 3, 4, 5],
    "illustrative": illustrative,
    "local_steps": [
        {"input": xs, "rank": k, "index": i, "result": step(k, xs, i)}
        for xs, k, i in [
            ((3, 1, 2), 1, 1), ((3, 1, 2), 0, 0),
            ((3, -2, 8, 0, 5), 3, 1), ((3, -2, 8, 0, 5), 0, 2),
            ((7,), 0, 0), ((4, 4, 4), 1, 0), ((7,), 1, 0),
        ]
    ],
    "boundary_notes": [
        "No valid rank exists on the empty list; its actual worker law is still none/empty trace/source2.",
        "Invalid singleton rank1 has the actual empty child; it is excluded by the universal valid-rank hypothesis.",
        "Three equal entries at rank1 terminate after one active size3 call with first atom1/3, not a length3 endpoint-removal path with1/6 mass.",
        "The full Lean factorial witness and unbounded family remain a later stage; finite checks alone do not establish them.",
    ],
}
target = Path(__file__).with_name("expected-cases.json")
assert not target.exists()
target.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"case_count": len(rows), "illustrative": len(illustrative), "local_steps": result["local_steps"], "output": str(target), "bytes": target.stat().st_size, "sha256": hashlib.sha256(target.read_bytes()).hexdigest()}, indent=2))

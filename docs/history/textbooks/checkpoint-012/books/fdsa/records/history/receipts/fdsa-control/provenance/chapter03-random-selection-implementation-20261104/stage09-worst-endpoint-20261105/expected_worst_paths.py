"""Pre-source endpoint/path/family cases from the unchanged source-call model.

The original 719-case output remains untouched. Load only the model's imports
and function definitions, reuse saved illustrative rows, and calculate one new
small natural-range interior-rank case. This is not Lean validation.
"""

import ast
from fractions import Fraction
from math import factorial
from pathlib import Path
import hashlib
import json

previous = Path(__file__).parent.parent / "stage07-endpoints-20261104"
source = previous / "expected_case_model.py"
saved = previous / "expected-cases.json"
assert hashlib.sha256(source.read_bytes()).hexdigest() == "7edb978daacc882721553f8a5f0a2b094f36b8571988e405e28703be5fdaa2c7"
assert hashlib.sha256(saved.read_bytes()).hexdigest() == "69f3d90737a56bff4719f8c4c208b1f65ea585c8d9e94d72216ac4f9b77506fe"
parsed = ast.parse(source.read_text())
definitions = ast.Module(body=[node for node in parsed.body if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))], type_ignores=[])
scope = {}
exec(compile(definitions, str(source), "exec"), scope)
step = scope["step"]


def endpoint_trace(k, xs, trace):
    if not trace:
        return False
    n, i = trace[0]
    if n != len(xs) or not 0 <= i < len(xs):
        return False
    pivot = max(xs) if k == 0 else min(xs)
    if xs[i] != pivot:
        return False
    action = step(k, tuple(xs), i)
    if "value" in action:
        return len(xs) == 1 and len(trace) == 1
    j, ys = action["child"]
    return endpoint_trace(j, ys, trace[1:])


rows = json.loads(saved.read_text())["illustrative"]
new_range = scope["endpoint"](2, tuple(range(4)))
assert new_range["outcome"] == (2, ((4, 0), (3, 0), (2, 1), (1, 0)), 48)
assert new_range["scan"] == 10 and new_range["actual_uniform_run_atom"] == "1/24"
rows.append(new_range)
reviewed = []
for row in rows:
    xs, k = row["input"], row["rank"]
    value, trace, calls = row["outcome"]
    n = len(xs)
    distinct_valid = len(set(xs)) == n and k < n
    structural = endpoint_trace(k, xs, trace)
    assert structural == distinct_valid
    targets = [sorted(choice["input"])[choice["rank"]] for choice in row["choices"] if choice["rank"] < len(choice["input"])]
    if distinct_valid:
        assert targets and all(target == value for target in targets)
        assert len(trace) == n
        assert 2 * row["scan"] == n * (n + 1)
        assert row["actual_uniform_run_atom"] == str(Fraction(1, factorial(n)))
        assert row["scan"] <= calls <= 9 * row["scan"] + 2
        assert n * n <= 2 * calls and calls <= 11 * n * n
    reviewed.append({
        "input": xs, "rank": k, "outcome": row["outcome"], "scan": row["scan"],
        "complete_atom": row["actual_uniform_run_atom"],
        "structural_endpoint_trace_expected": structural,
        "all_stage_targets": targets,
        "distinct_valid_universal_domain": distinct_valid,
    })

result = {
    "scope": "Expected cases saved before new Lean source; finite cases do not establish the universal theorem.",
    "model_source": str(source), "model_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "saved_cases": str(saved), "saved_cases_sha256": hashlib.sha256(saved.read_bytes()).hexdigest(),
    "original719_matrix_rerun": False,
    "newly_calculated_range_case": "n=4,k=2,value2,trace[(4,0),(3,0),(2,1),(1,0)],W10,T48,mass1/24",
    "cases": reviewed,
    "universal_expected_claim": "Every arbitrary distinct input and every valid worker rank admits the actual specified endpoint trace to singleton, exact trace probability1/n!, W=n(n+1)/2, and W<=T<=9W+2.",
    "range_family_expected_claim": "For every Nat n>0 and every k<n, the actual range(n) execution has a positive-mass endpoint witness satisfying n*n<=2*T and T<=11*n*n. Choosing n=B+1 gives unbounded sizes, with all valid k retained.",
    "boundary_notes": [
        "The purely structural predicate contains no desired mass, work bound or assumed target equation; target preservation is derived from actual step semantics.",
        "Empty and invalid inputs retain the total actual run, but cannot end this endpoint path at a valid singleton.",
        "The valid three-equal case terminates at size3, so it is not the specified singleton-ending worst path; W3 and first trace mass1/3 remain unchanged.",
        "T is the actual source observation, not assigned triangular W; the range4 case has T48 while W10.",
        "The projected trace atom will use the checked on-support trace-to-outcome uniqueness theorem; a full atom alone is insufficient.",
    ],
}
target = Path(__file__).with_name("expected-cases.json")
assert not target.exists()
target.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
print(json.dumps({"bytes": target.stat().st_size, "sha256": hashlib.sha256(target.read_bytes()).hexdigest()}))

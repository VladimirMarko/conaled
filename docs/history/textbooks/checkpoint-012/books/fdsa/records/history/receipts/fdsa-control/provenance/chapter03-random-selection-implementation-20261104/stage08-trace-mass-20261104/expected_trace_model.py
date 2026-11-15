"""Pre-code finite trace observations of the unchanged independent source model.

Only the original model's imports and function definitions are loaded. Its saved
719-case output is neither regenerated nor overwritten. No Lean is executed.
"""

import ast
from collections import defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json

source = Path(__file__).parent.parent / "stage07-endpoints-20261104" / "expected_case_model.py"
assert hashlib.sha256(source.read_bytes()).hexdigest() == "7edb978daacc882721553f8a5f0a2b094f36b8571988e405e28703be5fdaa2c7"
tree = ast.parse(source.read_text())
definitions = ast.Module(body=[node for node in tree.body if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))], type_ignores=[])
scope = {}
exec(compile(definitions, str(source), "exec"), scope)
run = scope["run"]
endpoint = scope["endpoint"]

states = atoms = 0
rows = []
for n in range(5):
    for xs in product((-1, 0, 1), repeat=n):
        for k in range(n + 2):
            law = run(k, xs)
            traces = defaultdict(list)
            for outcome, mass in law.items():
                assert mass > 0
                traces[outcome[1]].append((outcome, mass))
            assert all(len(group) == 1 for group in traces.values())
            for outcome, mass in law.items():
                trace_mass = sum(m for (_, trace, _), m in law.items() if trace == outcome[1])
                assert trace_mass == mass
            states += 1
            atoms += len(law)
            rows.append([xs, k, [(outcome, str(mass)) for outcome, mass in law.items()]])

cases = []
for xs, k in [((7,), 0), ((3, 1, 2), 1), ((3, -2, 8, 0, 5), 3), ((4, 4, 4), 1), ((), 0), ((7,), 1)]:
    row = endpoint(k, xs)
    expected = row["outcome"]
    trace_mass = sum(m for (_, trace, _), m in run(k, xs).items() if trace == expected[1])
    assert str(trace_mass) == row["actual_uniform_run_atom"]
    cases.append({"input": xs, "rank": k, "outcome": expected, "scan": row["scan"], "outcome_mass": row["actual_uniform_run_atom"], "trace_mass": str(trace_mass)})
assert cases[1]["outcome"] == (2, ((3, 1), (2, 0), (1, 0)), 33)
assert cases[1]["trace_mass"] == "1/6"
assert cases[2]["outcome"] == (5, ((5, 1), (4, 2), (3, 0), (2, 0), (1, 0)), 67)
assert cases[2]["trace_mass"] == "1/120"
result = {
    "scope": "Independent finite expectations saved before new Lean source; no universal proof or compiler credit.",
    "model_source": str(source),
    "model_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "new_observation": "For a fixed initial state, supported full outcomes have distinct traces, including duplicates, empty inputs and invalid ranks. Aggregate trace mass therefore equals the supported full atom mass.",
    "finite_states": states,
    "finite_supported_atoms": atoms,
    "finite_rows_sha256": hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
    "cases": cases,
    "nonclaim": "Traces need not identify outcomes across different initial input/rank states. A general unsupported outcome is not a valid witness for exact trace-atom equality.",
}
target = Path(__file__).with_name("expected-cases.json")
assert not target.exists()
target.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
print(json.dumps({"bytes": target.stat().st_size, "sha256": hashlib.sha256(target.read_bytes()).hexdigest()}))

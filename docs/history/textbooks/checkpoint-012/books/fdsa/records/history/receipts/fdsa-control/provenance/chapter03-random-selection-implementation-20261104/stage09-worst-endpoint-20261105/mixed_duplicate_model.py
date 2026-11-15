"""One additional pre-source boundary; reuse the exact saved source model."""

import ast
from pathlib import Path
import hashlib
import json

here = Path(__file__).parent
model = here.parent / "stage07-endpoints-20261104/expected_case_model.py"
assert hashlib.sha256(model.read_bytes()).hexdigest() == "7edb978daacc882721553f8a5f0a2b094f36b8571988e405e28703be5fdaa2c7"
tree = ast.parse(model.read_text())
definitions = ast.Module(body=[node for node in tree.body if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))], type_ignores=[])
scope = {}
exec(compile(definitions, str(model), "exec"), scope)
case = scope["endpoint"](2, (1, 1, 2))
assert case["outcome"] == (2, ((3, 0), (1, 0)), 23)
assert case["scan"] == 4 and case["actual_uniform_run_atom"] == "1/3"
assert case["choices"][0]["child"] == (0, (2,))
assert case["choices"][1]["value"] == 2
result = {
    "scope": "Additional expected case saved before the new EndpointTrace source; no Lean validation.",
    "reason": "A structural singleton-ending endpoint path can exist on mixed duplicates. Structure alone does not imply Nodup, one-element decrements, triangular work, or factorial mass.",
    "model": str(model),
    "model_sha256": hashlib.sha256(model.read_bytes()).hexdigest(),
    "case": case,
    "expected_structural_endpoint_trace": True,
    "expected_nodup": False,
    "distinct_size3_triangular_comparison": {"actual_scan": 4, "triangular": 6, "actual_trace_mass": "1/3", "inverse_factorial": "1/6"},
    "source_cost": "Actual source calls14+9=23; W4 is a separate observation.",
}
target = here / "mixed-duplicate-precode.json"
assert not target.exists()
target.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
print(json.dumps({"bytes": target.stat().st_size, "sha256": hashlib.sha256(target.read_bytes()).hexdigest()}))

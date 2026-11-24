"""Bounded #699 decision evidence; not a verified checker or production bridge.

Reuse the unchanged #490 diagnostic and enumerate the selected pure decoder.
The production native correspondence and finite-checker proofs remain proposed.
"""
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
import json
from pathlib import Path
import runpy


def main():
    root = Path(__file__).resolve().parents[2]
    prior_path = root / "experiments/compiler-evidence/probe.py"
    prior = runpy.run_path(str(prior_path))
    capture = StringIO()
    with redirect_stdout(capture):
        prior["self_test"]()
    evaluate = prior["evaluate"]
    decode = prior["decode"]
    direct = ["q", ["*", 3, "q"]]
    alternate = ["q", ["+", "q", ["+", "q", "q"]]]
    changed = ["q", ["*", 5, "q"]]
    # The submitted table is explicit data, checked against both syntax forms.
    table = [(q, (q, (3 * q) % 16)) for q in range(16)]
    for q, output in table:
        assert decode(direct, q, 16) == output
        assert decode(alternate, q, 16) == output
        assert output[0] == q  # E(D(q)) = q
    counterexamples = []
    for q, output in table:
        if decode(changed, q, 16) != output:
            counterexamples.append(q)
    assert 1 in counterexamples
    # The stronger recovery promise fails outside the selected invariant.
    assert decode(direct, 0, 16) != (0, 1)
    # The quotient does not reflect equality of integers.
    assert 0 % 16 == 16 % 16 and 0 != 16
    try:
        evaluate(["oracle", 3, "q"], {"q": 1})
    except prior["Failure"] as error:
        unsupported = str(error)
        assert unsupported == "unsupported-primitive"
    else:
        raise AssertionError("unsupported primitive accepted")
    output = {
        "source_base": "0d3865b344940510428e01f6907cb03dedbfe256",
        "prior_probe_sha256": sha256(prior_path.read_bytes()).hexdigest(),
        "probe_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "status": "Python diagnostics and source inspection only; no new kernel theorem",
        "prior_490_replay": json.loads(capture.getvalue()),
        "pure": {
            "modulus": 16, "coefficient": 3, "inputs": list(range(16)),
            "direct": direct, "different_syntax": alternate,
            "submitted_table": table, "changed_coefficient": 5,
            "changed_coefficient_counterexamples": counterexamples,
            "unsupported_primitive": unsupported,
            "outside_invariant_state": [0, 1],
            "lost_integer_distinction": [0, 16],
        },
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

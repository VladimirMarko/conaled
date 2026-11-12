"""Disposable #490 comparison, not a verified checker or production compiler.

Run from the repository: direnv exec . python3 experiments/compiler-evidence/probe.py
Only this fixed polynomial/residue machine fragment is supported.
"""
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json


def blob(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return sha256(blob(value)).hexdigest()


def add(a, b):
    return ["+", a, b]


def mul(a, b):
    return ["*", a, b]


SOURCE = {"schema": "pair-residue-v1", "modulus": 16,
          "primitive": "exact-nonnegative-int-v1", "inputs": [0, 1, 2, 3],
          "initial": [0, 0], "next": [add("x", "d"), add("y", mul(3, "d"))],
          "observe": "next-y", "temporary_bits": 6}
ARTIFACT = {"schema": "one-register-v1", "modulus": 16,
            "primitive": "exact-nonnegative-int-v1", "initial": 0,
            "next": add("q", "d"), "output": mul(3, "q"),
            "temporary_bits": 6, "state_bits": 4}
DECODER = ["q", mul(3, "q")]


class Failure(Exception):
    pass


def need(condition, diagnostic):
    if not condition:
        raise Failure(diagnostic)


def evaluate(expr, env):
    if type(expr) is int:
        need(expr >= 0, "unsupported-negative-literal")
        return expr
    if isinstance(expr, str):
        need(expr in env, "unsupported-variable")
        return env[expr]
    need(isinstance(expr, list) and len(expr) == 3, "unsupported-expression")
    op, a, b = expr
    x, y = evaluate(a, env), evaluate(b, env)
    need(op in ("+", "*"), "unsupported-primitive")
    return x + y if op == "+" else x * y


def upper(expr, env, limit):
    # Nonnegative +/* are monotone; checking every node covers temporaries.
    if type(expr) is int or isinstance(expr, str):
        n = evaluate(expr, env)
    else:
        need(isinstance(expr, list) and len(expr) == 3, "unsupported-expression")
        op, a, b = expr
        x, y = upper(a, env, limit), upper(b, env, limit)
        need(op in ("+", "*"), "unsupported-primitive")
        n = x + y if op == "+" else x * y
    need(n < limit, "temporary-overflow")
    return n


def source_step(source, state, d):
    env = dict(zip(("x", "y"), state)) | {"d": d}
    result = tuple(evaluate(e, env) % source["modulus"] for e in source["next"])
    return result, result[1]


def target_step(artifact, q, d):
    m = artifact["modulus"]
    q1 = evaluate(artifact["next"], {"q": q, "d": d}) % m
    return q1, evaluate(artifact["output"], {"q": q1}) % m


def decode(decoder, q, modulus):
    return tuple(evaluate(e, {"q": q}) % modulus for e in decoder)


def binding(source, artifact, decoder):
    return {"source": digest(source), "artifact": digest(artifact),
            "decoder": digest(decoder), "interpretation": "congruence-ring-bits-v1"}


def common(source, artifact, decoder):
    need(source["schema"] == "pair-residue-v1", "unsupported-source")
    need(artifact["schema"] == "one-register-v1", "unsupported-artifact")
    need(source["primitive"] == artifact["primitive"] == "exact-nonnegative-int-v1",
         "unsupported-primitive-meaning")
    need(source["observe"] == "next-y", "unsupported-observation")
    m = source["modulus"]
    need(m == artifact["modulus"] == 16, "unsupported-modulus")
    need(source["inputs"] == [0, 1, 2, 3], "unsupported-input-contract")
    need(artifact["state_bits"] == 4, "invalid-representation")
    need(len(source["next"]) == 2 and len(source["initial"]) == 2,
         "invalid-source-shape")
    need(all(type(x) is int and 0 <= x < m for x in source["initial"]),
         "invalid-source-initial")
    need(type(artifact["initial"]) is int and 0 <= artifact["initial"] < m,
         "invalid-artifact-initial")
    need(decoder is not None and len(decoder) == 2, "missing-selected-witness")
    for e in source["next"]:
        upper(e, {"x": 15, "y": 15, "d": 3}, 2 ** source["temporary_bits"])
    upper(artifact["next"], {"q": 15, "d": 3}, 2 ** artifact["temporary_bits"])
    upper(artifact["output"], {"q": 15}, 2 ** artifact["temporary_bits"])
    for e in decoder:
        upper(e, {"q": 15}, 2 ** artifact["temporary_bits"])


# Route A: sparse polynomials over Z/16Z in q,d, with a supplied relational
# substitution y=k*q. It does not enumerate the state/input transition graph.
def normalize(expr, env, modulus):
    if type(expr) is int:
        return {(0, 0): expr % modulus} if expr % modulus else {}
    if isinstance(expr, str):
        return env[expr]
    op, a, b = expr
    p, r = normalize(a, env, modulus), normalize(b, env, modulus)
    out = dict(p) if op == "+" else {}
    if op == "+":
        for monomial, coefficient in r.items():
            out[monomial] = (out.get(monomial, 0) + coefficient) % modulus
    else:
        need(op == "*", "unsupported-polynomial-rule")
        for (i, j), c in p.items():
            for (k, l), d in r.items():
                monomial = (i + k, j + l)
                out[monomial] = (out.get(monomial, 0) + c * d) % modulus
    return {key: value for key, value in out.items() if value}


def algebra(source, artifact, decoder, certificate):
    m, k = source["modulus"], certificate["multiplier"]
    need(type(k) is int and 0 <= k < m, "invalid-multiplier")
    q, d = {(1, 0): 1}, {(0, 1): 1}
    env = {"q": q, "d": d}
    n = lambda expr, values=env: normalize(expr, values, m)
    need(n(decoder[0]) == q and n(decoder[1]) == n(mul(k, "q")),
         "decoder-does-not-realize-relation")
    need(decode(decoder, artifact["initial"], m) == tuple(source["initial"]),
         "initial-correspondence")
    source_env = {"x": q, "y": n(mul(k, "q")), "d": d}
    next_q = n(artifact["next"])
    need(n(source["next"][0], source_env) == next_q, "x-polynomial-correspondence")
    next_y = n(source["next"][1], source_env)
    need(next_y == n(mul(k, artifact["next"])), "y-polynomial-correspondence")
    need(n(artifact["output"], {"q": next_q}) == next_y,
         "output-polynomial-correspondence")
    return {"method": "polynomial-identities", "enumerated_edges": 0}


# Route B: supplied finite simulation relation. No polynomial normalization,
# inferred multiplier, or trusted user Boolean is used here.
def finite(source, artifact, decoder, certificate):
    rows = certificate["relation"]
    need(all(len(row) == 3 and all(type(v) is int and 0 <= v < 16 for v in row)
             for row in rows), "invalid-relation-row")
    relation = set(map(tuple, rows))
    need(len(relation) == len(rows), "duplicate-relation-row")
    need(tuple(source["initial"]) + (artifact["initial"],) in relation,
         "initial-not-in-relation")
    for x, y, q in relation:
        need(decode(decoder, q, 16) == (x, y), "lost-selected-witness")
        for d in source["inputs"]:
            (x1, y1), output = source_step(source, (x, y), d)
            q1, target_output = target_step(artifact, q, d)
            need((x1, y1, q1) in relation, f"relation-not-closed:{x},{y},{q},{d}")
            need(output == target_output, f"output-mismatch:{x},{y},{q},{d}")
    return {"method": "finite-simulation", "enumerated_edges": 4 * len(relation)}


def evidence(source, artifact, decoder, route):
    cert = {"binding": binding(source, artifact, decoder), "route": route}
    if route == "algebra":
        cert["multiplier"] = 3
    else:
        cert["relation"] = [[q, (3*q) % 16, q] for q in range(16)]
    return cert


def admit(source, artifact, decoder, certificate, require_resource=False, resource=None):
    if certificate is None:
        return {"status": "unknown", "reason": "missing-evidence"}
    try:
        need(certificate["binding"] == binding(source, artifact, decoder), "stale-binding")
        common(source, artifact, decoder)
        route = certificate["route"]
        need(route in ("algebra", "finite"), "unsupported-evidence-format")
        checked = (algebra if route == "algebra" else finite)(source, artifact, decoder, certificate)
        if require_resource:
            if resource is None:
                return {"status": "unknown", "reason": "missing-resource-evidence"}
            need(resource == {"model": "declared-state-bits-v1", "bound": 4},
                 "unsupported-resource-claim")
            need(artifact["state_bits"] <= resource["bound"], "state-capacity")
        return {"status": "accepted", **checked}
    except Failure as ex:
        return {"status": "unknown" if str(ex).startswith("unsupported-") else "rejected-evidence",
                "reason": str(ex)}


def select(source, artifact, decoder, certificate, resource):
    result = admit(source, artifact, decoder, certificate, True, resource)
    # Baseline is the exact source interpreter with two declared four-bit
    # registers. Its ordinary structural path needs no extra user proof.
    return ("compressed", result) if result["status"] == "accepted" else ("baseline", result)


def execute_selected(source, artifact, decoder, certificate, inputs, resource):
    selected, result = select(source, artifact, decoder, certificate, resource)
    state = artifact["initial"] if selected == "compressed" else tuple(source["initial"])
    outputs = []
    for d in inputs:
        need(type(d) is int and d in source["inputs"], "unmet-input-premise")
        state, output = (target_step(artifact, state, d) if selected == "compressed"
                         else source_step(source, state, d))
        outputs.append(output)
    return selected, outputs, result


# Two nonidentity interpretations: integer expression -> canonical polynomial
# over Z/16Z -> little-endian four-bit values. Bit arithmetic is independent of
# integer % evaluation; direct evaluation is compared with the composite.
def bits(n):
    return tuple((n >> i) & 1 for i in range(4))


def unbits(v):
    return sum(b << i for i, b in enumerate(v))


def bitadd(x, y):
    result, carry = [], 0
    for a, b in zip(x, y):
        result.append(a ^ b ^ carry)
        carry = (a & b) | (a & carry) | (b & carry)
    return tuple(result)


def bitmul(x, y):
    result = bits(0)
    for i, b in enumerate(y):
        if b:
            result = bitadd(result, (0,) * i + x[:4-i])
    return result


def polybits(poly, q, d):
    result = bits(0)
    for (i, j), coefficient in poly.items():
        term = bits(coefficient)
        for _ in range(i):
            term = bitmul(term, bits(q))
        for _ in range(j):
            term = bitmul(term, bits(d))
        result = bitadd(result, term)
    return result


def self_test():
    results = {}
    resource = {"model": "declared-state-bits-v1", "bound": 4}
    for route in ("algebra", "finite"):
        cert = evidence(SOURCE, ARTIFACT, DECODER, route)
        accepted = admit(SOURCE, ARTIFACT, DECODER, cert)
        assert accepted["status"] == "accepted", accepted
        results[route] = accepted
        for count in range(5):
            for trace in product(SOURCE["inputs"], repeat=count):
                chosen, outputs, _ = execute_selected(SOURCE, ARTIFACT, DECODER, cert, trace, resource)
                fallback, expected, _ = execute_selected(SOURCE, ARTIFACT, DECODER, None, trace, None)
                assert chosen == "compressed" and fallback == "baseline" and outputs == expected
        assert admit(SOURCE, ARTIFACT, DECODER, cert, True)["reason"] == "missing-resource-evidence"
        assert select(SOURCE, ARTIFACT, DECODER, cert, None)[0] == "baseline"
        assert admit(SOURCE, ARTIFACT, DECODER, cert, True,
                     {"model": "elapsed-time", "bound": 4})["status"] == "unknown"
        changes = [
            ("source-coefficient", "source", lambda s: s["next"].__setitem__(1, add("y", mul(2, "d")))),
            ("initialization", "source", lambda s: s.__setitem__("initial", [0, 1])),
            ("primitive-meaning", "source", lambda s: s.__setitem__("primitive", "saturating-v1")),
            ("parameters", "source", lambda s: s.__setitem__("modulus", 8)),
            ("artifact-output", "artifact", lambda a: a.__setitem__("output", mul(2, "q"))),
            ("overflow", "artifact", lambda a: a.__setitem__("temporary_bits", 4)),
            ("representation", "artifact", lambda a: a.__setitem__("state_bits", 3)),
            ("witness", "decoder", lambda w: w.__setitem__(1, "q")),
        ]
        for label, which, mutate in changes:
            objects = {"source": deepcopy(SOURCE), "artifact": deepcopy(ARTIFACT), "decoder": deepcopy(DECODER)}
            mutate(objects[which])
            args = (objects["source"], objects["artifact"], objects["decoder"])
            assert admit(*args, cert)["reason"] == "stale-binding"
            rebound = deepcopy(cert)
            rebound["binding"] = binding(*args)
            outcome = admit(*args, rebound)
            expected_status = "unknown" if label in ("primitive-meaning", "parameters") else "rejected-evidence"
            assert outcome["status"] == expected_status, (label, outcome)
            results[f"{route}:{label}"] = outcome["reason"]
        missing = deepcopy(cert)
        missing["binding"] = binding(SOURCE, ARTIFACT, None)
        assert admit(SOURCE, ARTIFACT, None, missing)["reason"] == "missing-selected-witness"
        # Distinct source bytes, same polynomial meaning: correspondence admits.
        different = deepcopy(SOURCE)
        different["next"][1] = add("y", add("d", add("d", "d")))
        new_cert = evidence(different, ARTIFACT, DECODER, route)
        assert digest(different) != digest(SOURCE)
        assert admit(different, ARTIFACT, DECODER, new_cert)["status"] == "accepted"
        try:
            execute_selected(SOURCE, ARTIFACT, DECODER, cert, [16], resource)
            raise AssertionError("input check did not reject")
        except Failure as ex:
            assert str(ex) == "unmet-input-premise"
    broken = evidence(SOURCE, ARTIFACT, DECODER, "finite")
    broken["relation"].pop()
    assert admit(SOURCE, ARTIFACT, DECODER, broken)["status"] == "rejected-evidence"
    results["finite:missing-row"] = admit(SOURCE, ARTIFACT, DECODER, broken)["reason"]
    expressions = [add("q", "d"), mul(3, add("q", "d")), add(mul(3, "q"), mul(3, "d")),
                   add(16, "q"), mul(add("q", "d"), add("q", 1))]
    env = {"q": {(1, 0): 1}, "d": {(0, 1): 1}}
    comparisons = 0
    for expr in expressions:
        polynomial = normalize(expr, env, 16)
        for q, d in product(range(16), repeat=2):
            direct = evaluate(expr, {"q": q, "d": d}) % 16
            assert unbits(polybits(polynomial, q, d)) == direct
            comparisons += 1
    # Interval abstraction admits this state; selected decoder cannot recover it.
    assert decode(DECODER, 0, 16) != (0, 1)
    # Algebraic impossibility of recovering x from 2*x while observing x.
    assert (2 * 0) % 16 == (2 * 8) % 16 and 0 != 8
    results["composition-comparisons"] = comparisons
    results["trace-comparisons-per-route"] = sum(4 ** i for i in range(5))
    results["bindings"] = binding(SOURCE, ARTIFACT, DECODER)
    results["status"] = "diagnostic Python checks only; no kernel proof"
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    self_test()

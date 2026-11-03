"""Finite evidence for docs/research/uncomputation-contracts.md, not a proof kernel.

Run with Python 3 in the repository's pinned development shell. State vectors
use exact real amplitudes, left unnormalized; reduced density matrices divide
by squared norm. The circuits tested are signed permutations, with no rounding.
"""
from fractions import Fraction
from itertools import product


def flip(state, controls, target):
    result = list(state)
    result[target] ^= int(all(state[c] for c in controls))
    return tuple(result)


def run(state, gates):
    for controls, target in gates:
        state = flip(state, controls, target)
    return state


def lift(vector, gates):
    result = {}
    for state, amplitude in vector.items():
        target = run(state, gates)
        result[target] = result.get(target, 0) + amplitude
    return {state: amplitude for state, amplitude in result.items() if amplitude}


def reduced(vector, keep):
    """Partial trace of a pure real vector, computed by matching traced bits."""
    norm = sum(a * a for a in vector.values())
    assert norm > 0
    traced = tuple(i for i in range(len(next(iter(vector)))) if i not in keep)
    result = {}
    for left, a in vector.items():
        for right, b in vector.items():
            if tuple(left[i] for i in traced) == tuple(right[i] for i in traced):
                key = (tuple(left[i] for i in keep), tuple(right[i] for i in keep))
                result[key] = result.get(key, 0) + Fraction(a * b, norm)
    return {key: value for key, value in result.items() if value}


# Wire order a,b,t,y. Independent specification is y XOR (a AND b), t=0.
compute = [((0, 1), 2)]
use = [((2,), 3)]
clean = compute + use + compute
for state in product((0, 1), repeat=4):
    assert run(run(state, clean), list(reversed(clean))) == state
for a, b, y in product((0, 1), repeat=3):
    assert run((a, b, 0, y), clean) == (a, b, 0, y ^ (a & b))
assert run((0, 0, 1, 0), clean) != (0, 0, 0, 0)  # Dirty ancilla.
mutate_control = compute + use + [((), 0)] + compute
assert run((1, 1, 0, 0), mutate_control)[2] == 1

# Reference r is entangled with a; it is never touched by any gate.
vector = {(0, 1, 0, 0, 0): 1, (1, 1, 0, 0, 1): 1}
expected = {(0, 1, 0, 0, 0): 1, (1, 1, 0, 1, 1): 1}
assert lift(vector, clean) == expected
assert all(state[2] == 0 for state in lift(vector, clean))
keep = (0, 1, 3, 4)
dirty = lift(vector, compute + use)
assert reduced(dirty, keep) != reduced(expected, keep)
# Equal computational-basis probabilities conceal lost coherences.
assert {x: v for (x, y), v in reduced(dirty, keep).items() if x == y} == {
    x: v for (x, y), v in reduced(expected, keep).items() if x == y
}

# A Z phase on computed scratch must survive cleanup on the data.
phase_input = {(0, 0): 1, (1, 0): 1}
cnot = [((0,), 1)]
computed = lift(phase_input, cnot)
phased = {state: amplitude * (-1 if state[1] else 1)
          for state, amplitude in computed.items()}
assert lift(phased, cnot) == {(0, 0): 1, (1, 0): -1}
assert computed != {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): 1}
# Same mixed marginal does not imply independence.
bell = {(0, 0): 1, (1, 1): 1}
assert reduced(bell, (0,)) == {((0,), (0,)): Fraction(1, 2),
                              ((1,), (1,)): Fraction(1, 2)}
assert reduced(bell, (0, 1)) != {
    ((a, b), (a, b)): Fraction(1, 4) for a, b in product((0, 1), repeat=2)
}

# Independently specified two AND outputs on four input bits.
parallel_layers = [[((0, 1), 4), ((2, 3), 5)],
                   [((4,), 6), ((5,), 7)],
                   [((0, 1), 4), ((2, 3), 5)]]
serial_layers = [[gate] for gate in [((0, 1), 4), ((4,), 5), ((0, 1), 4),
                                    ((2, 3), 4), ((4,), 6), ((2, 3), 4)]]
for layer in parallel_layers + serial_layers:
    occupied = set()
    for controls, target in layer:
        wires = set(controls) | {target}
        assert occupied.isdisjoint(wires)
        occupied |= wires
for a, b, c, d, y, z in product((0, 1), repeat=6):
    par = run((a, b, c, d, 0, 0, y, z), sum(parallel_layers, []))
    seq = run((a, b, c, d, 0, y, z), sum(serial_layers, []))
    assert par == (a, b, c, d, 0, 0, y ^ (a & b), z ^ (c & d))
    assert seq == (a, b, c, d, 0, y ^ (a & b), z ^ (c & d))
assert sum(map(len, parallel_layers)) == sum(map(len, serial_layers)) == 6
assert len(parallel_layers) == 3 and len(serial_layers) == 6

# Two separated uses of the same computed AND: keep versus recompute.
retained = [((0, 1), 2), ((2,), 3), ((2,), 4), ((0, 1), 2)]
recomputed = [((0, 1), 2), ((2,), 3), ((0, 1), 2),
              ((0, 1), 2), ((2,), 4), ((0, 1), 2)]
for a, b, y, z in product((0, 1), repeat=4):
    initial = (a, b, 0, y, z)
    expected_reuse = (a, b, 0, y ^ (a & b), z ^ (a & b))
    assert run(initial, retained) == run(initial, recomputed) == expected_reuse
    assert run(initial, recomputed[:3])[2] == 0
assert len(retained) == 4 and len(recomputed) == 6

# #251 W=1, K>=3: different forgotten prefixes, same complete snapshot.
def snapshot(history):
    prefix = history[:-1]
    return len(history), sum(prefix) % 2, tuple(history[-1:])


assert (0, 0, 0) != (1, 1, 0)
assert snapshot((0, 0, 0)) == snapshot((1, 1, 0)) == (3, 0, (0,))
print("PASS: 16 inverse cases; 8 clean oracle cases; 64 paired schedules;")
print("16 repeated-use schedules; coherence/reference, phase, dirty/mutated scratch,")
print("marginal and retention counterexamples")

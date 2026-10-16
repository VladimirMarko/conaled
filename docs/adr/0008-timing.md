# ADR 0008: Stable-signal squares, interval-linear timing, and typed circuits

- Status: Accepted
- Date: 2026-10-10
- Scope: `Applications/Timing/`, `Applications/Circuits/`
- Primary source: Conal Elliott, [*Timely Computation* (2023)](https://conal.net/papers/timely-computation/paper.pdf).
- Supporting source: [Felix](https://github.com/conal/felix).

## Context

An ordinary function on Boolean values forgets when its output becomes valid.
A circuit with reconvergent paths can temporarily compute the wrong Boolean
value even when its abstract Boolean function is constant across an input
transition.  The 2023 paper adds signal semantics, stability witnesses, and
compositional timing calculations to the earlier categorical compiler.

The main test of this translation is therefore whether a single local gate
proof yields a proof for every generated circuit, while retaining independent
value and timing functions and allowing a finite matrix representation of the
timing function.  A handful of closed truth tables would not establish this.

## Decisions

### 1. Use a stability relation, then derive a literal commuting square

Time is the rational numbers.  A signal is an arbitrary function from rational
time to `Bool`.  This is a dense, unclocked time model; it does not assert that
the Boolean-valued signal is mathematically continuous.  `Stable a s τ v`
states that each signal port agrees with its corresponding Boolean value at
every time in its supplied stability interval.

The signal-to-value interpretation is relational.  An arbitrary unstable
signal has no globally valid Boolean denotation, and an empty interval does
not determine a unique value.  Choosing an arbitrary representative value
would therefore lose the intended specification.  `Digital.object` packages
the stability relation as the shared `Relational.RelRep`.  `Digital.relation`
gives its relation-preserving arrow, and `Digital.square` uses the core's
proved witness construction to obtain an ordinary `Squares.Square`.
`Digital.square_compose` proves that composition agrees with pasting squares.

### 2. Retain both bounds, including inverted intervals

`Interval` is a product of two existing proved tropical commutative semirings:

```
MinTropical (WithTop (OrderDual ℚ)) × MinTropical (WithTop ℚ)
```

The lower factor is max-plus with negative infinity; the upper factor is
min-plus with positive infinity.  Addition intersects bounds, multiplication
adds endpoints, zero is the universal interval, and one is the point zero.
`contains_add`, `contains_shift`, `finite_add`, and `finite_mul` prove these
interpretations.  The full semiring laws come from Mathlib's constructions;
they are not added as application-specific axioms.

There is deliberately no invariant that the lower endpoint precedes the upper
endpoint.  The full adder has a carry coefficient `[17/20,3/5]`, whose negative
width records a minimum input-stability requirement.  Multiplying it by the
input interval `[0,1]` yields the useful output interval `[17/20,8/5]`.

Consequently, endpoint multiplication must not be described as the Minkowski
sum of arbitrary *sets* of times.  Distinct inverted bounds all denote the
empty set but can have different products after being combined with a wide
input interval.  `empty_product_counterexample` formally demonstrates why
quotienting all such bounds to one empty set would destroy the algebra.

### 3. Put independence and linearity in the morphism type

`Digital a b` contains four fields:

- `analog`: transformation of rational-time signals;
- `value`: Boolean function;
- `timing`: an `Interval`-linear map on port-indexed interval vectors;
- `correct`: preservation of stability for every input signal, timing vector,
  Boolean value, and time in the computed output intervals.

The timing map cannot inspect Boolean values, and the Boolean function cannot
inspect timing vectors.  This makes the paper's data-independent timing
separation structural.  The laws for composition, identities, terminal
objects, projections, pairing, and products are all proved.  Each gate
template proves stability and linearity locally, after which the structural
operations compose those proofs.

`unary d op` samples its input at `t-d`.  `binary d₁ d₂ op` permits distinct
pin delays and intersects the shifted input stability intervals.  The
mathematical templates permit signed rational shifts.  The named physical
examples use the paper's nonnegative delays: inverter `1/10`, NAND and NOR
`1/5`, XOR `1/4`, with AND and OR built by following NAND and NOR by an
inverter.  This development does not prove causality for arbitrary signed
templates or a transistor-level interpretation of the chosen constants.

### 4. Represent timing by exact finite matrices

`Port` follows the source product type: a bit has one port, unit has none, and
a product has a disjoint union of ports.  This avoids assigning arbitrary
numeric offsets during categorical composition.

`Digital.matrix` uses Mathlib's proved linear-map/matrix equivalence.
`matrix_correct` says that applying the matrix is exactly the timing function,
`matrix_compose` calculates composition by matrix multiplication, and
`matrix_identity` calculates identities.  `matrix_stable` transports the
all-times signal theorem through this representation.  `timing_add`,
`timing_scale`, and `timing_zero` expose the linear laws directly.

`timingRep` interprets a complete digital morphism by its timing linear map.
`timingMatrixSquare` then maps it to the shared `MatrixBackend.representation`
from `Applications/Linear/Matrix.lean`.  This is an actual cross-library square:
the generic matrix backend's application and composition squares work for
timing without any changes to their definitions or proofs.

This is exact arithmetic over the setup/hold interval semiring.  The matrix
entries record path-delay bounds; they are not probabilistic estimates or
floating-point approximations.

### 5. Keep an inspectable circuit AST and reuse the source compiler

`Circuit` is intrinsically typed syntax for gate labels and cartesian
operations.  `Gate` records the operation and rational pin delays.
`Circuit.interpret` folds this syntax into any target implementing the same
vocabulary, and `interpret_compile` proves that the source compiler commutes
with this fold for every source term and target algebra.

The digital target supplies all primitive proof obligations.  The existing
first-order frontend then gives `compile_value`, `compile_stable`, and
`compile_matrix_stable` for arbitrary source programs, including free
variables and let bindings.  `compileSquare` exposes the certificate through
the shared square interface.  This is cartesian first-order compilation;
circuits are not incorrectly claimed to support arbitrary exponentials or
general recursion.

Category laws for raw circuit data are semantic equalities, not equalities of
syntax trees.  `Circuit.Equivalent` identifies equality of the complete
digital interpretation, including analog behavior and timing.  Syntactically
different circuits need not be equivalent merely because their Boolean truth
tables agree.

### 6. Reproduce both the adder result and its hazard

The half adder has a sum row `[1/4,1/4]` and carry row `[3/10,3/10]`, where
individual scalar delays abbreviate point intervals.  The full adder first
combines inputs `b,c`, then combines `a` with that sum.  Its matrix is

| Output | `a` | `b` | `c` |
|---|---|---|---|
| Sum | `[1/4,1/4]` | `[1/2,1/2]` | `[1/2,1/2]` |
| Carry | `[3/5,3/5]` | `[17/20,3/5]` | `[17/20,3/5]` |

`halfAdder_matrix` and `fullAdder_matrix` prove these values from the circuit
interpretation.  `halfAdder_addition` and `fullAdder_addition` prove Boolean
arithmetic correctness for all inputs.  `fullAdderTerm` is a source program
with two let bindings, and `compiled_fullAdder` proves that compiling it gives
the same analog, Boolean, and timing interpretations as the factored circuit.

For a falling `b` with `a=c=true`, the abstract carry remains true.  The
modeled circuit nevertheless has a low carry at time `7/10`, bracketed by
high values at times zero and one.  These are checked theorems about the same
analog semantics, not a separate hand-written waveform.  The retained carry
coefficient is consistent with that hazard:
`carry_path_nonempty_iff` proves that its product with `[lo,hi]` contains a
time exactly when the input width is at least `1/4`.

## Alternatives considered

- **Select one Boolean denotation for each signal.** Rejected because
  instability and empty witness intervals make that selection unsound or
  arbitrary.  Relations and witness squares preserve the specification.
- **Use only latest arrival time.** It loses hold-time bounds and the
  negative widths caused by reconvergent paths.
- **Normalize every inverted interval to an empty constructor.** Rejected
  because endpoint multiplication would no longer respect this quotient.
  The code contains a concrete counterexample.
- **Attach timings to values in one unconstrained function.** It would allow
  timing calculations to depend on runtime data.  The product of independent
  functions and a linear-map field expresses the intended restriction.
- **Copy a timing matrix as an example assumption.** Rejected.  Matrices are
  extracted from certified circuit interpretations and the displayed entries
  are proved equal to the extracted values.
- **Call raw ASTs a category modulo reflexivity.** Rejected.  The semantic
  laws use extensional equality of their complete digital interpretations.

## Consequences and limits

Timing combines the shared first-order compiler, relational specifications,
literal witness squares, finite matrix representations, and independent
signal/value interpretations.  Composition preserves all those guarantees.
The adder example also demonstrates why equality in only the Boolean
interpretation is too weak for timing-preserving circuit optimization.

The artifact does not provide a netlist optimizer, common-subexpression
elimination, Verilog export, a place-and-route model, metastability analysis,
physical measurements, clock insertion, stateful feedback, or a proof of
minimal timing bounds.  Cartesian sharing is expressed in the source and
combinator syntax; no graph allocation or runtime sharing cost is claimed.
The stable-signal theorem is conditional on input stability witnesses and
gives a guarantee at times inside the computed intervals.  Empty output
intervals correctly provide no valid observation time.

## Proof entry points

| Concern | Checked declaration |
|---|---|
| Interval algebra and interpretation | `Interval.contains_add`, `contains_shift`, `finite_add`, `finite_mul` |
| Why inverted intervals must remain distinct | `Interval.empty_product_counterexample` |
| Primitive correctness | `Digital.unary`, `Digital.binary` |
| Cartesian/category laws | `Digital.compose_assoc`, `first_pair`, `second_pair`, `pair_eta`, `terminal_unique` |
| Literal square pasting | `Digital.square_compose` |
| Exact matrix representation | `Digital.matrix_correct`, `matrix_compose`, `matrix_stable` |
| Shared matrix-backend integration | `Digital.timingMatrixSquare` |
| Frontend/fold composition | `Circuit.interpret_compile` |
| Every source program | `Circuit.compile_stable`, `compile_matrix_stable` |
| Source full-adder compilation | `Adders.compiled_fullAdder` |
| All-input Boolean addition | `Adders.halfAdder_addition`, `fullAdder_addition` |
| Calculated adder matrices | `Adders.halfAdder_matrix`, `fullAdder_matrix` |
| Reconvergent hazard | `Adders.hazard_expected_carry`, `hazard_at_seven_tenths`, `hazard_before_and_after` |
| Required stability width | `Adders.carry_path_nonempty_iff` |

All formal claims listed here have proofs in the corresponding Lean modules.
Physical and engineering limits are scope boundaries, not assumptions inserted
as axioms into the formalization.

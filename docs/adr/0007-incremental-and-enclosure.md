# ADR 0007 — Distinguish finite updates from derivatives and enclosures

**Status:** Accepted.

## Context

The 2017 paper presents incremental computation and interval analysis using
categorical interfaces. Their contracts differ from differentiation and from
exact evaluation. Treating the wrappers alike would hide precisely the bugs
the translation should detect.

## Decision

For incremental computation, store `run`, an input-dependent `change`, and the
update law. Products and composition preserve that law. Present it as a
square whose vertical map applies a finite change. Compile the shared
`Arithmetic.Prim` source through the original first-order frontend. Add a
dependent cached-state invariant and preserve it on each update.

For multiplication, include the finite-change term `dx * dy`. Arithmetic
instances work over every commutative ring. A checked counterexample shows
why the infinitesimal tangent cannot replace the finite-change rule.

For interval analysis, use rational bounds and the relation `lo ≤ x ≤ hi`.
Addition, negation and four-corner multiplication prove enclosure. Lift those
primitive proofs to every source term with the relational compiler. Prove a
dependency-loss counterexample: pointwise `x + -x = 0`, but evaluating those
operations on `[-1,1]` gives `[-2,2]`, not the singleton zero.

## Alternatives

* Use analytic AD derivatives for incremental changes: omits higher-order
  finite-change terms and fails even for integer squaring.
* Assert equal output intervals for extensionally equal source functions:
  false for the implemented interval algebra.
* Use floating-point endpoints without a rounding model: would make a
  rational-arithmetic theorem insufficient for the executable backend.

## Consequences

Incremental correctness is separate from incremental speed. The cache updater
reuses its stored output, but the project claims no general asymptotic speedup.
Rational interval operations are exact; IEEE floating-point outward rounding
is outside their theorem. Higher-order interval application uses function
relations, never an arbitrary decoder from a function on intervals to a
function on points.

## Checked evidence

`Incremental.Compiler.compile_update`, `square_comp`, `advance_correct`,
`all_arithmetic_updates`, `tangent_is_not_a_finite_change`,
`IntervalAnalysis.mul_contains`, `compile_contains`,
`interval_cancellation_is_wider`.

## Source

Elliott, [Compiling to Categories](https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf), §§7.6–7.7.

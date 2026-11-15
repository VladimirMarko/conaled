# Compositional numerical error certificates

For [#372](https://github.com/VladimirMarko/conaled/issues/372),
[the shared metric lemmas](../../SquareKit/Numerical/Error.lean) connect the
[affine interval client](../../Examples/NumericalError.lean) and the existing
[rational disk-motion step](../../Applications/Orbifold/CheckedMotion.lean).
This implements the bounded proposal in
[the ordered-observation report](ordered-quantitative-observations.md).

## Contract and reuse

`Bound` contains a nonnegative sensitivity and local error. It transforms an
input bound `e` into `L*e+d`; `comp` runs the left stage first. Identity,
associativity and monotonicity are checked. The laws supply the standard
`Monoid Bound` instance, with chronological multiplication. Maps and selected outputs remain
arguments of theorems, outside the bound. Equal bounds never identify maps.

`estimate` combines `LipschitzOnWith` for the exact map with a uniform error
specification for the selected approximate map. `compose` requires both maps
to send the first domain into the second. `compose_three` retains these closure
obligations for both intermediate boundaries and proves the two associations
have the same bound. The error radius is real: a negative input radius is
unusable for actual inputs since distance is nonnegative.

`propagate` is the underlying triangle-inequality lemma with a selected target.
It also handles a stable Euler map whose local truncation is measured against
an exact trajectory endpoint. No uniform flow Lipschitz hypothesis is invented.
The existing `advance_correct` now uses it with `euler_stability` and
`local_error`. The native `run_correct`, sample list, endpoint relation and
rational budget calculation remain available. `motion_two_steps` exercises the
existing accepted moving half-steps and identifies their native accumulated
budget with the shared transformer composed twice.

The affine client proves `6*e+3*df+dg` for arbitrary chosen implementations
satisfying the uniform bounds. `selected_affine_bound` supplies actual
perturbations and nonzero input uncertainty. Native rational interval
multiplication and addition prove the exact range `[-5,7]` and perturbed range
`[-11/2,15/2]`; no existing containment theorem is duplicated. `contains_cast`
transports rational interval membership into real closed-interval membership.
Rational affine arithmetic embeds exactly in the reals. Disk motion already
provides its stronger `step_decode` bridge from rational state updates to real
Euler coordinates. Neither bridge asserts floating-point roundoff correctness.

## Negative cases and distinctions

Checked cases refute additive error accumulation (`1/2 > 1/10+1/5`), usual-metric
nonexpansiveness of the doubling stage, and interchange of the two affine
stages. Ordered enclosure is one-sided; a wide enclosure does not determine
the error of a selected point. Distinct selected outputs can have the same
error. Resource addition remains the separate contract of
`Applications/Resources/Measured.lean`; numerical error multiplies prior error
by the next sensitivity before adding the new local term.

## Sources and scope

The implementation base is `be1dfca1f57a950950a4e77d81f9fed5140161ee`.
Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The inspected primary API is `Mathlib/Topology/MetricSpace/Lipschitz.lean`,
including `lipschitzOnWith_iff_dist_le_mul` and
`LipschitzOnWith.dist_le_mul`. The implementation uses those definitions
rather than introducing another metric or Lipschitz hierarchy. The source
comparison and its paper-only results remain in the preceding report.
These new claims are Lean declarations, not a formalization of the report's
complete-lattice or quantitative-monad source results.

The two clients justify sharing the small propagation lemma and affine bound
algebra. They do not justify a universal quantitative effect interface.
For #235, the next obligation is an independent client requiring transport of
certificates across representations, with a specified preservation contract.
The already-open #374 can supply this evidence; this record creates no duplicate
follow-up.
For #193, this work supplies a concrete coefficient action to compare with
resource composition without treating error as additive cost. No work is
claimed on #107, #108's held-out theorem, or #260. No author-time or runtime
performance measurements were made.

Mathlib's `AffineMap` was also inspected at the pinned revision, in
`Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean`. It requires a scalar ring;
the nonnegative coefficients here do not form a ring. Using real affine maps
would additionally package nonnegativity and recover coefficients. The small
record keeps the caller's supplied coefficients visible and uses a standard
monoid for its laws. Its chronological evaluation reverses function-composition
order, as `mul_apply` states, so no left-action instance is asserted.

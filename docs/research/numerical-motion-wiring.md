# Numerical motion through position/frame wiring

[#430](https://github.com/VladimirMarko/conaled/issues/430) connects the existing
motion consumer to the finite wiring experiment. The inspected baseline is
`3bbf8083f94629fdedc1a438112f78d6d97a3196`. The chosen consumer is a constant
body-frame move with velocity `(1,0)`, comparing two coarse Euler steps of
size `1/1024` with four half steps. It starts from the driver's existing
negative-axis initializer. Both sides use the production rational arithmetic
and checked executor.

The new quantitative bound compares **two discrete evolutions** at equal times.
Each execution separately retains the existing `Approx` guarantee against the
same exact continuous endpoint. Refinement error is not substituted for that
continuous error budget. No rounded arithmetic, physical-device correctness,
stochastic law or FRP progress is claimed.

## Actual interconnection

[WiredMotion](../../Applications/Orbifold/WiredMotion.lean) constructs two
`System` components with complex states `z` (position) and `r` (frame):

```text
position component: z' = supplied frame
frame component:    r' = -factor(supplied position) * r²
factor(z) = 2 conjugate(z) / (1 - |z|²).
```

Each complex input uses two real scalar ports. Each component publishes two
copies of each coordinate through distinct ports: one for the other component's
input and one for external observation. The routing is a proved bijection of
ports, satisfying the existing no-passing wiring contract. It does not silently
fan out a single supplier. Both fields read the old state before an Euler update.

`field_eq` proves that the wired pair is precisely `motionField 1 0`.
`step_eq` connects its Euler update to `RationalMotion.step (.move (1,0))`,
using the production `step_decode` theorem. `readout_eq` exposes all four real
coordinates, and `readout_gain` bounds each output discrepancy by the product
max norm. `rewire` reuses `System.wire_comp`; this is an exact substitution law,
independent of approximation.

This decomposition was chosen after inspecting `DiscreteApproximation`,
`Approx`, `RationalMotion`, `CheckedMotion`, `NumericalExecution`,
`NumericalSymmetry`, `Wiring` and the previous wiring examples. It does not
extend the exact command semantics to state-dependent controls. Such controls
would need their own trajectory and uniqueness arguments; treating a control
sampled from numerical feedback as an existing constant command would change
the consumer's specification.

## Component bounds and refinement defect

The domain remains the production predicate
`Domain(z,r) := |z| ≤ 1/2 ∧ |r| ≤ 1`. In this domain, existing
`factor_bound` and `factor_difference` give bounds `2` and `8` for the
position-dependent factor. New component proofs establish

```text
|Δ position-field| = |Δ r|
|Δ frame-field| ≤ 8 |Δ z| + 4 |Δ r|.
```

The second row comes from the product difference for `factor(z) r²`, using
`|r²-s²| ≤ 2|r-s|`. The resulting field gain is `12` in the product max norm.
Separate component magnitudes `1` and `2` give the field bound `2`.
The composite estimates are derived from these rows and the actual suppliers;
they are not assumptions about an unexplained whole system.

Let `E_h` be the wired Euler update. The exact algebraic identity is

```text
E_(h/2)(E_(h/2)(s)) - E_h(s)
  = (h/2) [F(E_(h/2)(s)) - F(s)].
```

For `h ≥ 0`, with `s` and its half-step state in the domain, the first
half step moves by at most `h`. `position_defect` bounds the position residual
by `h²/2`; `frame_defect` bounds the frame residual by `6h²`. Their maximum
gives `refinement_defect`. `euler_gain` is `1+12h`.
These are local discretization differences between two Euler meshes, not
local truncation bounds against a continuous flow.

[WiredMotionComparison](../../Applications/Orbifold/WiredMotionComparison.lean)
proves, at every `n ≤ N`,

```text
dist(refinedOrbit(n), coarseOrbit(n))
  ≤ budget(1+12h, 6h², initialError, n).
```

The existing `budget_sum` expands this recurrence as
`(1+12h)^n initialError + 6h² Σ_(j<n) (1+12h)^j`.
The theorem requires a separately supplied finite invariant covering both
sampled orbits and every intermediate half step. It makes no global domain
or infinite-horizon stability claim.

## Admitted initializer and independent finite invariant

[WiredNumericalMotion](../../Examples/WiredNumericalMotion.lean) reuses
`Examples.NumericalMotion.initial` and `initial_approx`. The packet has position
`(-1/4096,0)`, the corresponding metric-unit frame and zero initial error.
The initializer's relationship to the exact pose is proved independently of
this comparison; zero entered error is not treated as evidence by itself.

`coarse_admitted` and `fine_admitted` check the actual rational `Admissible`
predicate on finite iterated packets, including their accumulated budgets.
`admissible_domain` then supplies `coarse_domain` and `fine_domain`.
These proofs cover the two coarse steps, all four half steps, and their
intermediate states without using the approximation recurrence.
`safe_fixture` translates these packet invariants through `step_eq` into the
hypotheses of the real-valued comparison. It is a finite invariant for the
stated initializer and horizon, not a claim that `Domain` is globally invariant.

`sampled_comparison` compares refined packet `2n` with coarse packet `n`.
`returned_states` identifies the actual successful executor results with the
iterated packets, and `returned_comparison` applies the derived bound to those
returned states. `equal_clock` proves the common duration `2/1024`.
The nonzero-defect control proves that the first coarse and two-half-step
states differ, and `State.decode_injective` transfers that distinction to
their mathematical coordinate observations.

## Retained consumer contracts

| Contract | Checked connection |
| --- | --- |
| Exact continuous endpoint | `coarse_continuous` and `fine_continuous` reuse `run_interval_correct`; both refer to the same existing move trajectory at `2/1024`. |
| Error and intermediate samples | Packet budgets are unchanged. `samples_and_domains` retains `List.Forall₂ Approx` and the numerical domains through `run_correct`. The refinement bound is additional evidence. |
| Possible failure | The executor remains `Option`-valued. `outside_domain` reuses the actual rejected packet with position `3/4`; no fallback state or success is invented. |
| Symmetry | `symmetry` uses the native `run_equivariant`, including failures, without modifying body controls or duration. |
| Selected witness | `selected_label` preserves the action-category C4 arrow label via `execution_label`. It is not replaced by equality of final coordinates. |
| External readout | The wiring exposes all coordinates, and `readout_gain` preserves their error observation. |

There is no arbitrary-motive identity, probability or temporal fairness contract
on this deterministic constant-command consumer. Their absence is a scope
boundary, not an assertion that numerical closeness could discharge them.
`invalid_feedthrough` retains the existing impossibility of instantaneous
feedback `i = i+1`. The new certified routing uses state-only readouts and
therefore never asks for such an algebraic solver.

## Direct native construction and optional adapter

`comparison_native` and `comparison` have the same hypotheses and conclusion.
They share the component estimates, local defect, coordinate interpretation
and invariant. The native proof performs the triangle estimate and induction;
the adapter supplies the established step hypotheses to
`DiscreteApproximation.finite_bound`. Thus the reused proof removes the finite
recurrence induction, rather than wrapping a bound already proved for the
whole wired system.

The book's separation of wiring from interpretation helps locate the proof
obligations. Existing `System.wire_comp` removes a repeated input-substitution
proof. Neither it nor the optional metric recurrence derives nonlinear factor
estimates, domain admission or the native executor's continuous endpoint
relation. Those remain explicit here. The experiment supports an optional
adapter alongside the direct motion API; it does not demonstrate that a
mandatory double-category interface would remove the remaining work.
No independent author trial, runtime benchmark or general productivity claim
was conducted.

The primary-source check revisited Myers's
[pinned Chapter 4 source](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C4-.tex),
especially the Euler affine-map equation, the approximation remark and
change-of-theory functoriality. Exact Euler naturality there restricts state
maps to affine maps; the approximation remark does not provide this consumer's
metric recurrence or invariant. The present proofs supply their own bounds.
The earlier [source assessment](categorical-systems-approximate-transport.md)
records the PDF/source locators and the broader hypotheses. No whole-book
model theorem is applied to the checked partial executor.

## Statement review, validation and limits

EDD started with the independently expected move equations and the comparison
of one Euler step with two half steps. The missing connection was the actual
position/frame interconnection, component estimates and admission evidence.
The checked cases exercise these results, not an independently postulated
composite error bound. Statement review checked the old-state update convention,
finite quantifiers, intermediate half-step membership, rational-to-real casts,
common sample times and the distinction between discrete and continuous errors.
Development repairs concerned elaboration and notation; the rejecting theorems,
not failed proof attempts, establish the stated negative results.

Focused validation passed with `lake build Examples.WiredNumericalMotion`.
A scoped exhaustive axiom audit of that import closure passed with only
`propext`, `Classical.choice` and `Quot.sound`. Source-policy, acyclic-import,
public-entrypoint coverage and local-link checks passed. The public
entrypoint includes the example for integrated validation. The enclosing implementation
workflow records exact candidate validation and independent Standards/Spec
review; focused checks are not a full acceptance receipt.

The arithmetic is exact rational arithmetic. Bounds on numerical error do not
bound numerator/denominator growth, bit operations, memory or elapsed time.
The [driver checkpoint](numerical-driver-checkpoint.md) and
[driver policy](budget-disk-driver.md) retain their independent resource limits;
this experiment does not rerun or extend those measurements.

#34 owns further numerical consumers, including separately scoped
state-dependent controls or longer admitted horizons. #235 owns reassessment
of optional quantitative adapters. #196 and #27 retain physical interaction
and FRP ownership. The bounded result adds no universal systems API and changes
no existing driver's admission, retry, witness or resource contract.

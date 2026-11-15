# Finite approximate transport through feedback wiring

Implementation of [#416](https://github.com/VladimirMarko/conaled/issues/416),
following the [accepted assessment](categorical-systems-approximate-transport.md).
Inspection and implementation base: `ec9f1b83281ad7711d4da65692706ceb883c0582`.

The existing three-component feedback circuit now has a finite discrete
coordinate-transport contract derived from its component sensitivities and
actual wiring. The source uses Euler in x-coordinates; the target uses Euler
after changing A's state coordinate to `q=x+x³`. These updates agree under the
existing affine reassociation and disagree under the nonlinear coordinate map.
The discrepancy reaches the external z output after three simultaneous steps.

This is an experimental mathematical construction over real numbers. The cubic
inverse is noncomputable. It is neither an executable rational root solver nor
a floating-point integrator. No continuous-flow existence, uniqueness or
truncation theorem is claimed. The discrete comparison is complete under its
stated assumptions without a global ODE construction.

## The checked construction

[WiringApproximation](../../Examples/WiringApproximation.lean) reuses `A`, `B`,
`C`, `BC`, `right`, `close`, `coordinates` and the public exact hierarchy law in
[OpenSystemWiring](../../Examples/OpenSystemWiring.lean). The source equations
at external input zero are

```text
x' = -x + z,    y' = -2y + x,    z' = -3z + y.
```

Here the primes specify the vector field used by Euler, not a newly proved ODE
trajectory. `source h` reads all components' old states before any update.
`euler_wire` and `euler_parallel` give the local equations;
`discretize_components` applies them to the actual hierarchy.
`discretize_rewire` uses `System.wire_comp`. `euler_hierarchy` reuses the checked
linear isometry and retains readout equality alongside the full next state.

[CubicCoordinate](../../Applications/OpenSystems/CubicCoordinate.lean) constructs
`encode x=x+x³` and its actual inverse `decode`. `strictMono`, `surjective`,
`decode_encode` and `encode_decode` discharge the inverse obligations; they are
not assumptions left to circuit callers. `inverse_bound` proves the inverse is
1-Lipschitz. `derivative` supplies the analytic derivative `1+3x²`, and
`transformedA_derivative` connects that derivative to A's original field.
The transformed component exposes decoded x to B. C still feeds z back to A
through the same certified wires, while its second output remains exposed.

`transport_defect` computes the full state defect exactly. With `v=-x+z`, it is
`(3xh²v²+h³v³,0,0)`. `local_defect_bound` derives

```text
delta(R,h) = 12 R³ h² + 8 R³ h³
```

on the source box of radius `R`, for `R≥0` and `h≥0`.
`defect_nonzero` gives `(11/64,0,0)` at `(1,0,0)`, `h=1/4`.
This is a one-step coordinate defect. It is not the local truncation error of
Euler relative to a continuous solution.

## Component gains and domains

`scalar_gain` proves the linear component estimate before choosing suppliers.
`Cubic.field_gain` supplies the transformed component estimate in decoded
coordinates. `source_wired_gains` and `target_wired_gains` connect these
estimates to the wired systems and their A/B/C state components. The
nonnegative source Euler gain matrix and target field gain matrix are

```text
[ |1-h|   0       |h|    ]       [ 1+15R²  0   1+3R² ]
[ |h|     |1-2h|  0      ]       [ 1       2   0     ]
[ 0       |h|     |1-3h| ]       [ 0       1   3     ].
```

The off-diagonal entries reflect the actual suppliers. `field_lipschitz`
aggregates the target matrix's row sums into `L=max(4,2+18R²)` in the nested
product max norm. `target_lipschitz` then gives Euler gain `a=1+hL`. The bound
is derived from those rows; it is not a premise about the unexplained composite.

The source box is `|x|,|y|,|z|≤R`; the target box is
`|q|≤encode R`, `|y|,|z|≤R`. `interpret_box` connects the two. Both have
separate invariant proofs for `R≥0`, `0≤h≤1/3`. For the target's A component,
`Cubic.euler_box` uses the polynomial identity

```text
encode R - encode x - (1/3)(1+3x²)(R-x)
  = (R-x)(R²+Rx+2/3).
```

The right side is nonnegative on the decoded interval; reflection gives the
lower endpoint bound. Thus `target_invariant` does not assume that source
invariance transfers through nonlinear Euler. This discharges the sufficient
invariant alternative in #416. No domain guard or guard-failure theorem is
needed for this admitted region. Outside it, these results make no admission
claim. `fixture_domains` provides a nonzero admitted application, including
all intermediate states, rather than just a zero fixed point.

## Finite comparison and repeated composition

[DiscreteApproximation](../../SquareKit/DiscreteApproximation.lean) is an optional
metric recurrence lemma, not a systems interface. `step_bound` names the
interpreted source successor and the target update of the interpreted old
state as the intermediate comparison. `finite_bound` requires a local defect
and target gain at every step of the chosen horizon, plus the initial relation.
Its target is any pseudometric space; domain and wiring evidence stay with the
application.

For initial source and target states in their boxes, with
`dist(interpret s,t)≤e`, `comparison` supplies every `n≤N` with

```text
dist(interpret(sourceOrbit n), targetOrbit n)
  ≤ aⁿ e + delta(R,h) * sum(j<n, aʲ).
```

The implementation uses `budget` recursively; `budget_sum` proves this formula.
`sampled_output` bounds the actual readouts at each sample using the same
certificate. `comparison_restart` restarts from the actual pair of intermediate
states, preserving their domains and accumulated error.
`orbit_add` and `budget_add` identify the whole execution and its repeated
budget composition. These are finite-index statements; they give no uniform
error bound as the horizon grows.

`fixture_comparison` specializes to `R=1`, `h=1/4`, `s=(1,0,0)`,
`t=(2,0,0)`, initial error zero, and every sample through `N=3`.
Here `a=6` and `delta=7/8`; the resulting bound is conservative.
`fixture_output_differs` proves the source and target z samples at step three
differ, using `decode 1<3/4`. Matching the first external sample would have
missed the transported discrepancy.

## Native and reusable proof comparison

The matched claims are `comparison`/`comparison_native` and
`comparison_restart`/`comparison_restart_native`. Both routes use identical
systems, initial relations, box hypotheses, time-step restrictions and budgets.
Both share the inverse, component gains, local defect and invariant mathematics.
The native route proves the induction and triangle estimate directly. The
reusable route supplies the defect and gain obligations to `finite_bound`;
it removes that induction and its intermediate-distance arithmetic from the
client. Restart in either route must still establish the actual intermediate
states' domain membership and initial comparison.

The reusable route therefore shares a finite approximation proof, not the
construction of component gains or feedback admission. Conversion effort is
explicit: expose the circuit's nested-product norm through component
projections, aggregate row gains, and change norm estimates to metric distances.
The native route needs the same conversions. These checked proofs establish
reuse on this circuit and repeated execution. They are not an independent
author trial or a measured productivity advantage, and do not show that a
wrapper reduces the entire mathematical effort. Existing `PreservationBounds`
continues to cover ordered observations without absorbing this metric recurrence.

## Failure controls and retained contracts

[WiringApproximationControls](../../Examples/WiringApproximationControls.lean)
checks these separate boundaries:

- `false_exact_transport` in the main experiment rejects exact cubic Euler
  transport through the nonzero defect.
- `isolated_contract` gives factors `3/4`, `1/2`, `1/4` for the isolated
  components with zero inputs. With feedback coefficient 24 through the same
  wiring, `expanding_direction` and `unstable_orbit` give an exposed output
  `(5/4)^n`; `output_unbounded` proves it exceeds every proposed bound.
  This is a discrete instability result, without a continuous-flow claim.
- `admission_controls` retains the existing rejected fanout and impossible
  input-dependent algebraic feedback. The quantitative construction does not
  expand the admissible wiring class.
- `hidden_trajectory` and `hidden_steady_looking` give an incrementing component
  connected to a sink through certified no-passing wiring. The composite's
  external chart is constant; `counter_not_steady_looking` proves that its
  component trajectory is not steady-looking. The sink consumes a supplier;
  the wiring does not discard or copy it. This concrete behavior-class
  obstruction is not a claim to have implemented Myers's probe functor.

The work adds no FRP, numerical-motion or probability adapter. Their fairness,
`Approx`, failure/domain, full-law and witness contracts remain unchanged.
[#235](https://github.com/VladimirMarko/conaled/issues/235) owns reassessment
if another client needs quantitative interconnection. The current evidence
supports retaining a small optional recurrence and domain-specific gains;
it does not select a universal preservation architecture. Continuous solution
comparison, stochastic couplings, arbitrary algebraic feedback, roundoff and
infinite-horizon stability remain separately scoped work.

## Statement review and acceptance evidence

Statement review checked the directions of both inverse equations, the
simultaneous update convention, actual wire suppliers, signs of matrix entries,
initial-state and every-step domain hypotheses, and full state versus output
comparisons. The nonzero finite case discharges the hypotheses through public
invariant/comparison theorems. The defect and unstable/recovery cases prevent
exactness, stability or recoverability from being inferred from forward
composition alone. No new axiom, admission or placeholder is used.

Focused Lean builds check the new modules and their retained applications.
The parent implementation workflow records exact-candidate integrated build,
exhaustive proof-audit and independent Standards/Spec review evidence. A focused
build alone is not acceptance of the integrated candidate.

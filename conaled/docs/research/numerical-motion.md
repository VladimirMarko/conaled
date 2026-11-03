# Executable disk motion with coordinate error bounds

The experimental backend for [#48](https://github.com/VladimirMarko/conaled/issues/48)
evaluates separate move, turn, and hold controls with exact rational Euler
arithmetic. Its contract compares the computed position and frame with
[#47's timed commands](../../Applications/Orbifold/TimedCommands.lean).
Successful execution carries an accumulated error budget, endpoint samples,
and elapsed time. Failure means the conservative domain check did not certify
the requested execution.

## Inputs and observations

[`RationalMotion`](../../Applications/Orbifold/RationalMotion.lean) represents
each complex coordinate by two rationals. `State` stores position `z` and the
frame value `h` at body vector `1`. `Packet` adds a rational error budget.
`Input` admits rational complex move velocities, rational turn velocities,
and holds. `Tick` adds a nonnegative rational duration. A tick is one Euler
step; repeat a tick to subdivide a constant command interval.

The decoder embeds each rational coordinate in the corresponding real
component of a complex number. Approximate states need not be orthonormal
poses; the evaluator does not normalize them. `Approx q p` means

```text
max (norm (decode q.position - p.a))
    (norm (decode q.frame - p.frame 1)) <= q.error.
```

This is a coordinate error bound, not an intrinsic-distance bound.
`step_decode` proves exact agreement between the rational computation and
Euler stepping of the existing `motionField`. Arithmetic error is zero.
No conversion to floating point is included in the numerical result.

## Domain and quantitative analysis

[`NumericalBounds`](../../Applications/Orbifold/NumericalBounds.lean) fixes
the domain `norm z <= 1/2`, `norm h <= 1`, with `norm v <= 1` and
`abs omega <= 1`. The proved bounds are:

| Quantity | Bound | Public result |
|---|---|---|
| Connection denominator `1 - normSq z` | At least `3/4` | `gap_lower` |
| Vector field norm | At most `3` | `field_bound` |
| Vector field sensitivity | `13 * norm (q-r)` | `field_difference` |
| Exact frame coordinate norm | At most `1/2` | `frame_bound` |
| Exact position displacement over time `t >= 0` | At most `t/2` | `position_displacement` |
| One-step truncation over duration `d >= 0` | At most `39*d^2` | `local_error` |

`coordinates_derivative` connects the analysis directly to
`Control.trajectory`. The local error proof bounds the derivative of the
Euler residual using the field and sensitivity estimates. Its coefficient
is conservative. These constants are proved inequalities, not compactness
witnesses or analytic hypotheses supplied by callers.

[`CheckedMotion`](../../Applications/Orbifold/CheckedMotion.lean) checks the
control bounds, a nonnegative incoming error `e`, and

```text
abs z.re + abs z.im + e + d/2 <= 1/2
normSq h <= 1.
```

The first test bounds the exact starting radius using the supplied initial
error, then bounds its entire trajectory during the tick by displacement.
It also bounds the current numerical position. The evaluator checks the
computed endpoint against `normSq z <= 1/4` and `normSq h <= 1`. Thus success
certifies both numerical endpoints and the intervening exact trajectory;
it does not assume that every Euler iterate stays inside the disk. All tests
use rational arithmetic. The position test uses an upper bound on the complex
norm and is invariant under quarter turns, though it can reject safe inputs.

`advance_correct` combines stability and truncation to carry forward

```text
nextError = (1 + 13*d)*e + 39*d^2.
```

Callers prove their initial `Approx` relation and a concrete successful
evaluation. `checkedStep_correct` and `run_correct` then discharge the
analytic consistency, stability, and domain obligations. The same rule
covers zero duration, turns, and holds; holds receive a conservative budget
even though `step_hold` proves their coordinate update is exact.

## Finite clocks and representative changes

[`NumericalExecution`](../../Applications/Orbifold/NumericalExecution.lean)
passes the whole packet between ticks. `errorAfter` computes the rational
budget for any finite list. `run_error` identifies it with the returned
budget, and `run_clock` identifies the returned elapsed time with the sum of
input durations. `clock_decode` connects that sum to the exact command clock.
`run_correct` relates every returned endpoint sample to the corresponding
exact endpoint as well as proving the final approximation. `observations`
pairs the input control and local duration with consecutive numerical
packets; it starts each tick at the previous numerical endpoint.

`run_append` proves composition across finite command boundaries, preserving
samples and adding clocks. `execute_replicate` and `run_interval_correct`
connect a subdivided constant command to its original trajectory at time
`n*d`. No boundary resets the numerical state or its error to the exact pose.

[`NumericalSymmetry`](../../Applications/Orbifold/NumericalSymmetry.lean)
implements a quarter turn as rational sign changes and coordinate swaps in
both position and frame. `Packet.rotate` executes any finite number of these
turns. The comparison with the existing C4 action uses its proved enumeration
by powers of `i`; that semantic action adapter is noncomputable, while
`Packet.rotate`, the checks, and the evaluator remain executable.

`checkedStep_equivariant` and `run_equivariant` prove exact equivariance with
unchanged controls and rejection behavior. `approx_equivariant` preserves
the same budget. `executionFunctor` uses the existing action-category
interface, with `execution_label` and `execution_arrow_evidence` retaining
the symmetry label and its endpoints, including rejected results.

## Construction checkpoint

The API comparison used Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its
`Analysis/Calculus/MeanValue.lean` supplies
`norm_image_sub_le_of_norm_deriv_le_segment'`, used for displacement and local
error. `Analysis/ODE/DiscreteGronwall.lean` supplies product and exponential
accumulation bounds. The implementation instead retains the rational
recurrence directly, so finite executions need no exponential evaluation.
The existing `motionField_smooth` and uniqueness result supply qualitative
analysis but no explicit stability constant; `field_difference` supplies it.

Certified evaluation of the explicit formulas was the alternative. Mathlib's
`Analysis/Complex/Exponential.lean` has `Complex.exp_bound` and
`Real.exp_bound`; the trigonometric series are also available. That route
would still need certified evaluation of the normalized velocity and tanh
in the move formula, plus propagation through the Möbius position and frame
denominators. It would introduce formula-evaluation error without ODE
time-discretization error. The selected Euler route avoids those
transcendental approximations and reuses the already-proved differential
equations. The existing rational interval library covers polynomial
arithmetic over rational values; it does not provide either analytic route's
integration or transcendental remainder estimates.

## Checked executions and limits

[`Examples/NumericalMotion.lean`](../../Examples/NumericalMotion.lean) starts
at `z = -1/4096` with its exact metric-unit frame. It proves successful
move, turn, hold, and zero-duration evaluations; a regular-point representative
change; and rejection outside the admitted radius. The move's certified
positive real endpoint and its real-axis trajectory prove an actual apex
crossing by the intermediate value theorem.

The move–turn–move execution has elapsed time `3/1024` and combined coordinate
error at most `124247487/1099511627776`. Replacing a move of duration `1/1024`
by two steps of duration `1/2048` reduces the certified bound from
`39/1048576` to `160251/8589934592`. The examples consume the public correctness
results, prove the rational checks in the kernel, and execute the evaluator
with `#eval`.

This slice excludes simultaneous translation and turning, time-dependent
controls, general atlas descent, intrinsic error estimates, and floating-point
rounding. Exact rational numerators and denominators can grow during repeated
steps; these short checked executions make no performance claim for a renderer
or an interactive simulator.

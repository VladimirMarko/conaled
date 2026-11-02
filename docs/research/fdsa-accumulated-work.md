# Accumulated random work

This shared draft supplies geometric bounds for nonnegative observations on
one measure. It is motivated by the randomized-work obligations in the pinned
July 27, 2026 FDSA book, especially the selection discussion on printed p.35.
The exact source inventories, frozen scope, API preflight and independent
calculations are retained in the local recovery checkpoint under FDSA-XW01.

The implementation is currently **uncompiled**. Its proof scripts, public
integration and statement review do not establish elaboration, exhaustive
axiom compliance, chapter acceptance or final independent approval. The
existing older Chapter 1 gate remains unchanged; no additional compiler run
was started for this draft. Read the checkpoint's status and review records
for the actual validation state.

## Existing semantics and the added argument

`Applications.Probability.Table` already supplies finite rational stochastic
tables and interpretation into Mathlib kernels. `ProbabilityProgress.Execution`
already evaluates ordinary machines in one joint random environment, retaining
operational return counts, divergence and shared randomness. Their local laws
and existing clients continue to apply.

The new `Applications.Probability.AccumulatedWork` module instead takes
ordinary functions `X : Nat → Ω → ℝ≥0∞` and an existing `Measure Ω`. It uses
Mathlib's lower integral, countable sums, geometric-series identity and Markov
inequality directly. There is no new sampler, execution state, expectation
operator or representation-preservation family to learn. Measured programs
are connected in the examples through the existing `Resources.run`, `bind`
and `reweight` operations.

For explanation, write `E_t = ∫⁻ ω, X t ω ∂μ`. This is a nonnegative integral;
it is an expectation when μ is a probability measure. The core itself needs
no normalization, finite-measure, sigma-finiteness, finite sample-space,
payload equality or inhabitedness assumption.

## Public contracts

| Public result | Required information and conclusion |
|---|---|
| `lintegral_le_geometric` | From `E_0≤N` and `E_(t+1)≤q*E_t` for every t, obtain `E_t≤q^t*N`. This ordered-integral induction needs no measurability or finiteness premise. |
| `lintegral_tsum_shift_le` | Almost-everywhere measurability of every observation permits sum/integral interchange. The actual remaining sum from w has integral at most `q^w*N/(1-q)`. |
| `lintegral_tsum_le` | The zero-shift specialization bounds the total integral by `N/(1-q)`. |
| `lintegral_tsum_lt_top` | If `q<1` and `N≠∞`, that total integral is finite. Zero N and zero q remain valid. |
| `measure_tsum_ge_le` | For one chosen w, an almost-everywhere prefix bound by `w*N`, together with `q<1` and positive finite N, bounds the mass of total work at least `w*N+N/(1-q)` by `q^w`. |
| `measure_tsum_ge_le_of_stage_le` | A common almost-everywhere bound `X_t≤N` supplies the preceding prefix premise. The weaker single-prefix theorem remains available. |

Nonnegativity is supplied by `ℝ≥0∞`. The extended-valued mean inequalities
also allow q at least one, where the geometric upper bound need not be finite.
Strict contraction is used where a finite conclusion or cancellable tail
threshold requires it. No proof divides by q, so q=0 is supported directly.

The tail proof first splits the actual total sum into its prefix and shifted
remaining sum. It proves that `w*N` is finite before cancelling the prefix
cap, and that `N/(1-q)` is positive and finite before applying division-form
Markov. The event inclusion holds almost everywhere, matching the premises.
Independence of the observations is not used.

The lower integral preserves infinite observations. A totalized real integral
or `ENNReal.toReal` would need additional finiteness reasoning before it could
represent a resource expectation. Even a finite integral of accumulated work
does not imply finitely many execution steps when per-step work can vanish or
decrease. A source execution's termination remains its own contract.

## A measured program with dependent stages

`Examples.AccumulatedWork.program` runs four ordinary state transitions under
one uniform environment `ω : Fin 8`. An active transition prepends its index
to the state list and charges one unit. Inactive transitions retain the state
with zero charge. The active conditions are true, `ω.val<4`, `ω.val<2`, and
`ω.val<1`, in that order. The supplied observation pads all later stages by
zero; `accumulated_eq_cost` connects its countable sum to the actual measured
run, and `program_value` separately identifies the full ordered output.

| Environment | Returned list | Measured work |
|---|---|---:|
| 0 | `[3,2,1,0]` | 4 |
| 1 | `[2,1,0]` | 3 |
| 2 or 3 | `[1,0]` | 2 |
| 4, 5, 6 or 7 | `[0]` | 1 |

Direct finite-law arithmetic yields means `1,1/2,1/4,1/8`. The integrated
one-step inequality therefore holds with q=1/2 and N=1. The exact total mean
is `15/8`; `expected_cost_le` obtains its upper bound two through the generic
theorem, and `expected_cost_finite` uses the finite-integral specialization.
After the first stage, the exact remaining mean is `7/8`;
`expected_remaining_le` exercises the general positive-shift bound of one.

Work at least three occurs at the first two environments, so its exact mass
is `1/4`. `tail_le` obtains the upper bound `1/2` through the generic tail
theorem. The tail event is nonempty. The two nonconstant events `ω.val<4` and
`ω.val<2` have intersection mass `1/4`, while the product of their marginal
masses is `1/8`. This explicit mismatch retains the shared environment.

`affineProgram` composes existing measured reweighting by two with a final
charge of three, preserving the returned list. Its actual cost is `2*W+3`,
with exact mean `27/4`. Lower-integral linearity transports the generic bound
to seven. Its threshold-nine event is the original threshold-three event,
so both its exact mass and generic tail bound transfer through that equality.
The example's observation excludes condition tests and environment sampling;
it is not a physical runtime claim.

## Boundary clients

`Examples.AccumulatedWorkBoundary` retains the consequential hypotheses:

- An actual one-stage measured computation of work three uses q=0. The
  total bound is three; the zero-shift tail uses `0^0=1`, and positive shifts
  have zero right-hand side.
- Zero work satisfies the mean/total conclusions with N=0. At zero threshold,
  the non-strict event is certain on a probability space. With q=1/2 and w=1,
  one is not at most one-half; the positive-N hypothesis is substantive.
- On uniform `Fin 3`, work three at one outcome and zero at the others has
  initial mean one. All later work is zero, so q=0 satisfies integrated drift.
  Nevertheless work at least two has mass `1/3`, refuting the tail conclusion
  without the prefix cap. An integral recurrence does not give that cap.
- Constant positive observations illustrate q=1: the one-step inequality
  holds while the total work is infinite. The finite-integral theorem retains
  strict contraction.

These are ordinary clients of the public claims and standard measure laws.
Their source-level proof scripts remain subject to the same compiler/audit
and independent review gates as the core.

## Source-specific obligations still to discharge

For randomized selection, the later construction must establish uniform
occurrence pivots conditional on the actual history, correct duplicate-aware
rank dispatch, and the next-size inequality. It must prove that its padded
length observations sum to actual scan volume and justify any affine bridge
to a different tariff. At q=3/4 and positive initial size n, the generic
threshold becomes `(w+4)*n`. No such algorithmic conclusion follows merely
from declaring a numerical recurrence.

Quicksort executes both recursive branches; contraction along a selected
path does not account for the second branch. Its input-permutation and
randomized-pivot laws, distinct-key hypotheses, harmonic calculation and cost
correspondences remain separate chapter obligations. Treaps use restrictions
of one common priority ranking; expected bulk work still needs the actual
conditional priority/cluster and weighted-charging arguments. Uniform ranking
restriction and subset-minimum combinatorics remain a distinct shared task.

The local probability source/API preflights preserve those boundaries and
the exact pinned interfaces. This unit supplies an analytic argument for
observations whose law and operational meaning have already been proved.

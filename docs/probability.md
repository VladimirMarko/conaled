# Probability kernels and finite Metropolis–Hastings

The library represents ideal stochastic computations with Mathlib's
`ProbabilityTheory.Kernel` and `Stoch`. Exact finite rational tables provide a
computational representation of those laws. There is no random-bit sampler in
this implementation. Evaluating a table entry computes a probability, not a
random outcome.

## Random functions

The experimental [random-function model](research/higher-order-random-functions-implementation.md)
constructs QBS values, products, exponentials and measurable observations.
Standard Borel source measures can sample these functions. A checked continuous
example distinguishes sharing one affine function from independent resampling,
and compares squaring with a correlated polynomial coefficient realization.
This supplies deterministic pushforward and independent source products, not a
general higher-order probability monad. The kernel and finite-table interfaces
below retain their existing contracts.

## Accept/reject semantics

`Applications.Probability.acceptReject` weights a proposal kernel by a
measurable acceptance function and puts the rejected mass at the current
state. Its normalization theorem requires a Markov proposal and acceptance in
`[0,1]`. The reusable `complete` operation also works directly from an accepted
subkernel whose total mass is at most one. Neither construction requires finite
state spaces, standard Borel spaces, conditional distributions, or a density
relative to a reference measure.

`acceptReject_reversible` assumes symmetry of the accepted flow between every
pair of measurable sets. It proves symmetry of the completed transition by
adding the diagonal rejection flow. The assumption concerns the accepted
subkernel, not the desired final transition. Stationarity then uses Mathlib's
`Kernel.IsReversible.invariant`. The target measure need not be normalized for
that general theorem.

`FiniteMH` supplies a concrete sufficient condition: positive rational target
weights and a nonnegative rational proposal table with each row summing to one.
Its acceptance is zero when the forward proposal probability is zero;
otherwise it is the minimum of one and the reverse-to-forward target-flow
ratio. `accepted_flow` derives the symmetric minimum of the two proposal flows.
Zero reverse support therefore rejects a proposed move. The target normalizer
is the sum of the weights; a nonempty state space makes it strictly positive.

The finite transition's kernel interpretation equals the general accept/reject
construction. Its normalized target is a probability measure, and the accepted
flow theorem discharges the general balance obligation. This is a
specialization of the general construction, with finite arithmetic proving its
hypotheses.

## Composition and interpretation

`Table.comp g f` runs `f` first and `g` second using exact rational matrix
multiplication. `Table.kernel` interprets each row as a finite sum of weighted
Dirac measures. `Table.kernel_comp` and `Table.kernel_deterministic` prove that
this interpretation preserves composition and pure functions.

`tableMeaning` uses the existing `SquareKit.RawMap` and `MapLaws` interfaces to
map finite tables into `Stoch`. Existing law transport supplies the category
laws under equality of interpreted kernels. `table_steps_meaning` uses the map's
composition law to transport arbitrary finite iteration. `invariant_comp`
composes two transitions preserving the same target through Mathlib's
`Invariant.comp`; it does not assert reversibility of their composite.

The shared category interfaces are unchanged. Tables have operations, semantic
equality and laws separately; their interpretation uses Mathlib's existing
Markov category. Pure maps embed as deterministic kernels. Independent product,
copy and discard remain those of the Markov structure. Arbitrary stochastic
arrows cannot be interpreted by the existing cartesian compiler frontends:
`ProductLaws.pair_eta` would identify distinct joints with the same marginals.
Copying one sampled bit retains perfect correlation; two fresh bits do not.

## Checked cases and remaining scope

The asymmetric two-state example has target `(1/4,3/4)`, proposal rows `(0,1)`
and `(1/2,1/2)`, and MH transition rows `(0,1)` and `(1/3,2/3)`. Its reverse
acceptance is `2/3`; rejecting mass `1/6` augments the proposal self-loop `1/2`.
A directed three-cycle proposal has no reverse support and its MH transition is
identity. These cases expose proposal-ratio, support and rejection conventions.
The stochastic examples distinguish shared and independent randomness and
stationarity from convergence.

Stationarity alone supplies no convergence, mixing rate, estimator confidence,
termination or elapsed-time guarantee. The bounded [probabilistic progress
contracts](probabilistic-progress.md) supply separate execution and deadline
semantics for #198; fault and environmental contracts remain with #196. Random-bit realization,
floating-point error and general-state ergodicity require additional contracts.
Higher-order and internal probability models remain optional follow-up work
identified in the [model comparison](research/probability-model-comparison.md).
The [initial investigation](research/probability-and-monte-carlo.md) records the
scope of #197 and its primary references.

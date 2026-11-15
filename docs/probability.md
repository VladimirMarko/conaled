# Probability kernels and finite Metropolis–Hastings

The library represents ideal stochastic computations with Mathlib's
`ProbabilityTheory.Kernel` and `Stoch`. Exact finite rational tables provide a
computational representation of those laws. `Table.prepare` and `Table.compile`
realize explicitly enumerated finite tables with exact fair-bit rejection
sampling. Evaluating a table entry computes a probability; the separate row
machine consumes bits and returns an outcome with its advanced cursor.

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

## Exact rows and resumable chains

`RationalRow` requires a nonnegative rational row summing to one and an executable
enumeration `Fin m ≃ α`. Preparation stores a common denominator and integer
weights. `TableSampler` draws a uniform code by binary-block rejection and
selects its cumulative weight interval. Zero weights occupy no interval;
non-dyadic rows are exact. Positive-width blocks mean even a deterministic
output can require retries. Its operational output-event law equals
`Table.kernel`; termination is almost sure under the independent fair-tape law.
Finite fuel retains its subprobability law and can expire without proving
divergence. `SamplerWork` separately declares arithmetic and storage tariffs;
those charges do not assert bit complexity or host runtime.

[TableProducer.lean](../Applications/Probability/TableProducer.lean) connects
these rows to `Progress.Producer`. One state retains the current semantic state,
coin cursor and partial rejection block. A completed transition emits its new
state and starts the next row at the returned cursor. Self-transitions emit too.
Finite deliveries recover `RowChain`'s full ordered path law and endpoint kernel.
The producer's count is exactly the number of inspected bits; `RowChain` has
one additional terminal administrative step, including for an empty path.

Random-cursor suffix independence from the row sampler justifies the chain
laws. Every finite output length is delivered almost surely by this same
producer. The existing productivity API supplies one conull set on which all
these finite prefixes coexist and agree. The all-true tape for a deterministic
one-state row is a checked exceptional divergent execution.

[TableProducerStationarity.lean](../Applications/Probability/TableProducerStationarity.lean)
proves that target-initialized MH has the same joint law for an ordered finite
block after any finite number of earlier emissions. The initialization is an
independent target mixture of the displayed tape probabilities. This preserves
correlations within each block; it does not assert independent successive
states, mixing, or empirical accuracy. Checked asymmetric-MH cases include
self-transitions, a resumed partial block, a retry, and the stationary pair
`(false,true)` with probability `1/4` at every observation shift.

The producer samples the completed MH transition table, whose self-loop mass
combines accepted self-proposals and rejected moves. It does not expose an
accept/reject flag. `TableProducer.changes` suppresses unchanged states and has
no unconditional productivity guarantee: on a singleton space it never emits,
although the original producer is almost surely productive. Accepted-only
filtering is a separate observation policy requiring its own progress premise.

## Measured finite workloads

[SamplerWorkload.lean](../Applications/Probability/SamplerWorkload.lean) runs
cached sampler states through the existing `Resources.run` executor. A bit step
retains the current prepared row, semantic state, cursor, partial accumulator,
and reverse output list. Appending commands resumes that state and adds the
actual charges; additive reweighting commutes with this execution. Erasure
preserves the producer's full path and returned cursor, including dependent
successive rows. A pause halfway through a subsequently rejected block does
not restart the block or repeat preparation.

The declared tariffs separate bit access, arithmetic, row preparation, stored
row lookup, selection, emitted-output handling, and final list materialization.
The producer eagerly loads and initializes the next row after every emission.
An n-output prefix therefore loads n+1 rows, including its initial row. An
empty observation still pays initialization; an empty command list after
initialization costs zero. The finite-chain adapter adds an administrative
return fee and preserves `RowChain.Trace` with its one extra logical transition.
This adapter retains the producer's prefetched row: its preparation charges
are not attributed to the raw `RowChain` implementation.

`compileLoader` materializes an array of the same rows as `Table.compile` and
charges preparation plus storage at setup, then lookup on each load. The
amortization theorem compares setup plus n+1 lookups with n+1 preparations.
With the checked asymmetric MH table and unit tariffs, observing one transition
costs 80 with preparation on each load and 84 including compiled setup; two
transitions cost 117 and 100 respectively. Equal output laws thus coexist with
different execution costs. These prices are abstract operation tariffs,
including a declared price for table-entry evaluation and inverse-enumeration
lookup. They do not establish operand bit complexity or wall-clock bounds.

[SamplerExpectedWork.lean](../Applications/Probability/SamplerExpectedWork.lean)
derives finite-prefix deadline and expectation bounds using actual stopped
suffix freshness. If W is one plus the largest prepared-row block width, the
probability that n outputs require more than n*W*r bits is at most n*2⁻ʳ.
Summing deadline probabilities gives expected inspected bits at most 2*n²*W.
This deliberately coarse bound needs no independence of successive row costs.
Finite maxima of the implemented per-bit and loader charges give an explicit
affine bound for total charged work, including setup and output handling.

Both observations use nonnegative extended integration. On a completed prefix,
bit work is the actual delivery count and charged work is setup plus the actual
stopped resource execution. On non-delivery they are infinite, even if every
tariff is zero. Measurability and unconditional finite expectations are proved
for the finite-table sampler; almost-sure productivity alone is insufficient.
Finite-budget runs may emit only a shorter prefix, so their partial observations
are not the eventual full-prefix distribution conditioned on success. Checked
cases are in [SamplerWorkload.lean](../Examples/SamplerWorkload.lean).

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
semantics; the finite rational realization above discharges their delivery
obligations for the fair tape. Fault and environmental contracts remain with
#196. Physical entropy adapters, floating-point error and general-state
ergodicity require additional contracts.
Higher-order and internal probability models remain optional follow-up work
identified in the [model comparison](research/probability-model-comparison.md).
The [initial investigation](research/probability-and-monte-carlo.md) records the
scope of #197 and its primary references.

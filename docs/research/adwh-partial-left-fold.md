# Strict left folds of partial observations

The finite interpreter in `SquareKit.PartialSpine.LeftFold` distinguishes a
completed end from a prefix whose end is unknown. It updates the accumulator
through known labels, returns the seed at nil, and returns the supplied bottom
at an unknown end. `foldl_eq_view` connects that recursion to the existing
independent prefix/end representation: completed inputs use standard
`List.foldl`; open inputs return bottom.

The semantic operation in `SquareKit.PartialSpine.Observations` uses the
existing `IdealCompletion.extend` into a standard `CompletePartialOrder`.
It introduces no domain carrier, alternative order or limit construction.
The fixed-label spine order makes the finite interpreter monotone for every
accumulator step. Neither input continuity nor the constructor law assumes
that the step is monotone or continuous in its accumulator.

## Completed-end demand

`eq_principal_of_total_mem` shows that an ideal with a completed finite
observation is exactly that principal ideal. Its proof uses the existing
finite maximality facts `isTotal_iff_exists` and `ofList_le_iff`, together with
the standard ideal's directedness and lower closure. It does not use the
different notion of a maximal proper ideal.

`foldl_eq_bottom_of_no_total` then covers every ideal without a completed
observation. `foldl_nonbottom_requires_finite` states the necessary condition
for a nonbottom result: the whole input is a completed finite list. An open
prefix of known finite length does not meet that condition. The converse is
false; even a completed input may produce bottom. `foldl_stream` specializes
the result to every ordinary infinite stream, with arbitrary step and seed.

## Connection to existing producers

`Progress.SpineObservations.foldl_observations` applies the general theorem to
the actual producer interface. That interface emits a label or takes a silent
transition and has no completed-end event. Its already proved
`not_total_of_mem` discharges the input condition. Consequently every one of
its observation ideals gives bottom to this strict left fold.

`Examples.PartialSpineLeftFold` consumes that bridge alongside the existing
first-output and truncation interfaces. Guarded and paused counting expose
the same values; their first three values from 4 are `[4,5,6]`, with the
existing separate three/six-transition witnesses. Emit-once also exposes its
first label. Strict left folding still returns bottom on each of those
observations. Silent producers instantiate the same general bridge.

The finite cases check a constant-True step on completed versus open
`[4,5,6]`, negation on Prop despite its failure of monotonicity, and an
order-sensitive finite fold giving `[2,1,9]`. Another completed case returns
bottom and therefore rules out a converse nonbottom equivalence. Nil and
unknown bottom remain distinct even with the same seed.

These are denotational and observation claims. They do not infer operational
divergence from failed fuel, claim a left-fold running time, or change the
producer's event interface.

## Source correspondence

This development adapts the sixteen strict-left-fold rows of
`ADWH.Chapter01.LazyListEvaluation` from the supplied successor-335 material.
The [exact ledger](adwh-partial-left-fold-provenance.tsv) retains each source
statement, location, hash, qualification and destination. The total-spine
maximality row reuses existing facts; the finite stream-prefix helper is
covered by the stronger arbitrary-open-prefix law. Source accounting is
separate from the integrated build, exhaustive proof audit and independent
review recorded by the local task tracker. Scans and function-accumulating
concat remain separate slices. The queens-16 numerical proof is excluded.

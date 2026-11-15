# Accumulation and tupling from Chapter 1

## Source and preserved meaning

The source is `adwh-checkpoint-335-compact-recovery`, member
`project/adwh-lean/ADWH/Chapter01/Accumulation.lean`, SHA-256
`986fb1477c58aae55d010a7e5c3a7376e73156a569f8003636a624494d7c3ac3`.
Its bytes agree with the predecessor inventory. The supplied source identifies
the ordinary, cached, and difference-function collapse variants at original
LINE571, LINE589, LINE613, and the steepness variants at LINE1178 and LINE1189.
These coordinates are retained source references; the original book PDF is
absent from the supplied recovery archive.

The [declaration ledger](adwh-accumulation-provenance.tsv) records exact source
declarations and their conaled destinations. Ordinary prefix and suffix
specification proofs are retained where useful. Existing standard `List`,
ordered-summary and Batteries difference-list interfaces replace the source's
duplicated infrastructure. No archive imports or generator are needed to build
the integrated modules.

## Shared construction and concrete clients

`SquareKit.GuardedFold.run` is a finite fold which tests its state before
consuming each remaining input. Exhaustion returns the state regardless of the
test. `refine` relates two executions through input decoding and an arbitrary
state relation. It requires agreement of stopping decisions on related states,
and a transition law only for valid inputs when execution continues. Its
separate `invariant` theorem retains an ordinary predicate through the same
visited transitions. These contracts assume neither monoid structure nor a
global termination rank: the finite input list decreases.

`Sequences.Accumulation` keeps an independent specification for collapse.
The result is the initial accumulator followed by a whole-block prefix; every
proper boundary before a consumed block has nonpositive total, and the chosen
result is positive or the input is exhausted. The specification is unique.
`collapse_shortest_prefix` exposes the prefix index and all earlier inequalities
without appealing to cached execution.

`cachedRun` uses `Sequences.OrderedSummary.appendCache`, `Valid`, and
`append_valid`. Its proof is one application of `GuardedFold.refine`. The two
concrete realizations supply the existing ordinary-list and Batteries `DList`
append laws. `cachedRun_refines` retains both validity and the full sequence,
so equal sums cannot substitute for correct ordered output.

Integer addition is supplied through the standard `Multiplicative Int` wrapper.
`summary_sum` connects the existing free-monoid summary to the independent
integer sum. The source's separate map and zip of sums is preserved as a zip
in `labelSums`, with pair order changed from `(sum, block)` to `(block, sum)`
to use the established cache interface. `labelSums_eq_map` proves that this
zip creates valid caches. This representation change is explicit in the ledger.

The source's arbitrary function invariant is represented by Batteries' existing
`DList.invariant`. In addition to equality after materializing the empty tail,
`differenceResult_apply` proves the result at **every** tail. The generic
`cachedRun_refines` accepts arbitrary valid initial representations and labels;
the public collapse clients specialize it to an empty accumulator.

`differenceSquare` exposes the actual optimized result through the existing
relational representation. `collapseSummary` composes that square with the
existing `OrderedSummary.summarySquare`. Its implementation reads the cached
integer. `collapseSummary_correct` relates that observation to the independent
collapse result's sum; it does not recompute the list merely to prove an example.

`Sequences.Steepness` specifies steepness by every suffix decomposition:
each element must strictly exceed the sum of the elements after it. The direct
decision recursively recomputes that suffix sum. `fastSteep` tuples the sum and
the decision in a standard right fold. `fastSteep_invariant` is an application
of `SquareKit.ListFusion.foldr_reachable`; it connects the tupled executor to
both ordinary observations together. This uses the existing fusion theorem
instead of introducing a second generic tupling interface.

## Checked cases and initial obligations

The initial missing connection was transporting a cached representation through
an early-stopping fold. Existing ordered-summary laws covered append and complete
batches, but did not justify agreeing on the stopping point. The new refinement
rule closes that gap for both list and difference-list clients. For tupling,
the existing right-fold fusion theorem already sufficed; no artificial failing
mathematical case was introduced.

All retained cases are in `Examples.Accumulation`:

| Case | Independent expectation | Public connection |
|---|---|---|
| `cached_first_positive`, `difference_first_positive` | Empty blocks and totals `0, 0, -2, -2, -1, 2` select `[-2,1,3]` and leave `[99]` unconsumed. | Both representation refinements to `collapse`. |
| `chosen_prefix_satisfies_spec` | The same ordered result satisfies the independent whole-block prefix specification. | `collapseCached_correct`. |
| `composed_sum` | The chosen result sums to `2`. | The actual composed cache observer and `collapseSummary_correct`. |
| `every_tail`, `ordered_tail` | The chosen prefix precedes an arbitrary tail; `[7,8]` stays after `[-2,1,3]`. | `differenceResult_apply`, including noncommutative list order. |
| `negative_exhaustion` | If every boundary remains nonpositive, all blocks are retained in order. | Difference-list refinement. |
| `zero_continues` | Zero does not satisfy the strict positive stopping test. | Cached refinement. |
| `empty_cached`, `empty_difference`, `positive_seed_stops` | Empty input returns the initial state, and an already positive seed consumes no block. | Refinements and the generic-fold specialization. |
| `incorrect_cache_rejected` | A cached sum of zero cannot represent `[99]`. | Existing `Valid` and `summary_sum`. |
| `tupled_steep`, `steep_mathematics` | `[8,4,2,1]` is steep and sums to `15`. | Tuple invariant followed by the independent suffix specification. |
| `steep_tie_fails`, `steep_zero_fails` | Equality of an element and its suffix sum fails a strict comparison. | The tupled-to-direct decision theorem. |
| `steep_negative_fails`, `steep_empty` | A negative final element fails; the empty list is vacuously steep. | The same decision refinement. |

## Statement review and limits

The prefix quantifier ranges over block indices, not element indices. Empty
blocks are permitted. Signed integer totals may decrease; no positivity or
monotonicity of input values is assumed. The stopping condition is `0 < sum`,
and exhaustion is a separate allowed outcome. The uniqueness proof therefore
does not invent a positive prefix when none exists.

Cache validity relates the cached value to the represented list. Raw pairs
with false cached sums are excluded explicitly, and the negative example
demonstrates that this premise is substantive. The guarded-fold relation and
input predicates are arbitrary propositions; their step hypotheses are local
and their initial and input-validity hypotheses are discharged in the concrete
clients. The conclusion observes both represented data and the cache equation.

Difference-list correctness quantifies over every tail and preserves append
order. The steepness condition quantifies over every decomposition, with an
empty suffix at the final element, so that final element must be positive.
The tuple invariant proves the sum and Boolean simultaneously without assuming
the desired whole-list equality.

Elaborated-type inspection exposed an ambiguity from the reducible additive
type tag in the composed observer. `collapseSummary_correct` explicitly fixes
`Multiplicative.toAdd` at `Int`, so ordinary callers obtain an integer equality
without inferring another type-tag layer. The expected observed value `2` was
retained through this correction.

These are exact finite mathematical-integer semantics. No Haskell strictness,
laziness, sharing, machine overflow, allocation, operation bound, or wall-clock
claim follows from the value equalities. The retained source's separate
`CollapseAppendCosts`, `CollapseDemand`, and `SteepCosts` developments still
require their own adaptation and consumer contracts.

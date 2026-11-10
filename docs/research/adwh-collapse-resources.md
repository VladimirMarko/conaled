# Chapter 1: collapse demand and materialization work

This development continues the finite collapse adaptation in
`adwh-accumulation.md`. The existing `Sequences.Accumulation` implementation and
independent first-positive whole-block prefix specification remain the owners
of value semantics. The new resource modules make the source's demand and
materialization observations explicit. Neither finite value equality nor a
difference-list representation alone establishes these cost results.

## Source identity

The selected files are from the user-supplied checkpoint 335, whose original
archive SHA-256 is
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.

| Source member under `project/adwh-lean` | SHA-256 | Explicit named declarations |
|---|---|---:|
| `ADWH/Chapter01/CollapseDemand.lean` | `0a6dfb85101814ed2cc39981d6b29bc8563c3202d5b3aeca5c21041d94a9f620` | 46 |
| `ADWH/Chapter01/CollapseAppendCosts.lean` | `7e698ef5f5accccba74f1cdb40ce9cbd9f6684dba71739195f530de3eb2fc034` | 60 |

Both are byte-identical to their entries in the predecessor inventory. The old
ZIP is not needed. The source records printed pages 14–15 and the Exercise 1.19
best-case distinction; these coordinates are inherited provenance. The original
book PDF is absent from the supplied payload. This document does not claim a
fresh reading of unavailable pages.

`adwh-collapse-resources-declarations.tsv` accounts for every named declaration
in these two files. It records retained, renamed, and replaced interfaces rather
than claiming that all source names should become public conaled APIs. The six
demand examples and seven materialization examples are retained as named checks
in `Examples/CollapseResources.lean`, alongside additional composition and
boundary checks.

## Ownership and reuse

`Applications/Resources/CollapseDemand.lean` owns the source-specific demand
trace. It reuses `Resources.Steepness.sumRun` for the actual measured sum and
`Sequences.Accumulation.cachedRun`, cache labels, and `CollapseSpec` for value
refinement. Label erasure adapts the source's `(sum, block)` ordering to the
existing ordered-summary `(block, Multiplicative Int)` cache interface.

`Applications/Resources/CollapseMaterialization.lean` owns the finite producer
and output-materialization observations. Its append operation reuses the
existing recursive `Resources.TreeFlattening.appendWithCost`. A standard list
stores blocks in reverse update order, replacing the source's empty/snoc `Expr`
datatype. Updates use list cons. `historyValue = reverse.flatten` is a
specification observation; the measured executors do not first reverse and
flatten their histories and then omit that work from the bill.

`Resources.Measured`, `reweight`, `bind`, and `erasureSquare` remain the common
resource interfaces. No separate writer composition or resource hierarchy is
introduced. The measured sum observation in the example module uses actual
`Squares.compose`, retains the producer's work, and agrees with the already
composed `Sequences.Accumulation.collapseSummary` on its mathematical value.

The value-only guarded fold inspects its finite input before the guard and
returns directly on empty input. That is adequate for its established output
contract, but it does not encode the source demand order. The resource
recursions therefore check the accumulated total before observing the remaining
spine and retain the terminal comparison on exhaustion. Their values are proved
to refine the existing guarded implementation; its control flow is not silently
used as a source cost model.

## Demand-only contract

`plainAux` sums its accumulated list before each guard. `cachedAux` reads the
running scalar total, forcing a selected block's sum thunk once when consuming
that block. Both record the actual consumed blocks. A `Run` also records the
input lists passed to summation and four counters:

| Counter | Counted observation |
|---|---|
| `sumWork` | One unit per observed sum-input constructor and one addition per cons; a sum of length `n` costs `2*n + 1`. |
| `scalarAdds` | The cached loop's scalar accumulator additions. |
| `tests` | Total-positivity comparisons, including the terminal comparison. |
| `spineCases` | Remaining-input case observations after a failed positivity test. |

These fields are model observations. Allocating the trace lists in Lean is not
part of the modeled source bill. This module intentionally does not charge
label construction, accumulator append materialization, integer bit complexity,
or evaluator runtime. The complete materialization model below adds the first
two categories explicitly.

`plainAux_selected` and `cached_selected` connect the returned `used` trace to
the existing `NonpositiveBefore` condition and an actual remaining suffix. The
condition says every consumed whole block was preceded by a nonpositive total,
and the final result is positive or the input is exhausted. This establishes
the actual selected prefix even when several empty blocks have the same
flattened output. It is stronger evidence than value equality alone.

For the cached run, if `k` blocks containing `N` elements were consumed, the
exact sum work is `2*N + k`, the number of scalar additions is `k`, and the
number of tests is `k + 1`. The input prefix theorem yields the corresponding
whole-input upper bounds. A positive starting total avoids even the next
spine case. With a positive first block, all returned events are independent
of the discarded suffix; the plain and cached variants perform the same
number of integer additions inside their demanded sums in that best case.

For every `n`, the compact input `List.replicate n [0]` reaches every test:

- Plain sum work is exactly `(n + 1) * (n + 1)`.
- Cached sum work is exactly `3*n`.

These are universally quantified, inductively proved witnesses. No large
numerical proof graph or generated exhaustive data is needed.

## Demanded production and full materialization

`labelStep` implements one demanded step of the source map/zip producer. A cons
step constructs a delayed sum and a label at cost seven; exhaustion costs two.
`buildAux` requests this step only after the total test fails. The builder records
sum work, label production, null/head/tail selectors, comparisons, and updates
separately. Its output history remains unmaterialized.

The source append model charges two units per left cons—constructor observation
and copied cons—plus one for the final nil. Existing `appendWithCost` counts
copied cells, so each individual append is reweighted by `c ↦ 2*c + 1`. This
affine transformation is deliberately applied **per append call**. It is not an
additive homomorphism: moving the final `+1` outside a sequence of appends would
change the model and lose exhaustion charges.

`leftMaterialize` evaluates the successive left-associated append results.
`applyFunction` evaluates the corresponding function representation at an
arbitrary tail. Both produce the actual output as well as work. The function
observer's value is `historyValue history ++ tail`; its work is independent of
the tail and equals `2 * outputLength + blockCount`.

`buildAux_apply` connects every-tail observation to the existing raw cached
executor for arbitrary initial history and scalar state. For the public initial
state, `build_apply_difference` identifies its result at **every tail** with the
actual `Sequences.Accumulation.differenceResult` DList. Agreement only after
application to `[]` would be insufficient. These bridges preserve values; they
do not assert that Lean's `Batteries.DList` evaluator has the source-model cost.

Let `N` be the number of elements in the consumed blocks and `k` their number.
The builder overhead is at most `2*N + 14*k + 4`. Complete materialization has
the following proved bounds:

| Observer | Bound in the selected prefix |
|---|---|
| Function representation | At most `4*N + 15*k + 4`; at least `2*N + k + 1`. |
| Left append | At most `2*N + 14*k + 4 + k*(2*N + 1)`. |

Both have whole-input forms obtained from the actual prefix relationship. On
`replicate n [0]`, left materialization alone costs exactly `n*n`, while the
complete function run costs at most `19*n + 4`.

The faster growth bound does not establish pointwise dominance. A positive
first block of length `n` has exact complete costs `2*n + 16` for left append
and `4*n + 16` for the function representation. The checked singleton case is
therefore 18 versus 20. Three empty blocks cost 49 under complete function
materialization even though the resulting output is empty. The retained cases
prevent silently discarding label, terminal-test, or empty-append costs.

## Actual composed consumer

`Examples.CollapseResources.observedDifference` composes the measured function
materializer with the shared measured sum. Its value is the sum of the selected
collapse prefix, and its exact work is the producer's work plus
`2 * outputLength + 1`. Its whole-input bound is `6*N + 15*m + 5` for `m` input
blocks containing `N` elements.

The signed input `[[-1], [-2], [10], [90]]` consumes the first three blocks. The
composed result is `(7, 65)` in the stated model; the discarded `[90]` is absent
from the demanded-sum trace. Empty input returns `(0, 5)`. The arbitrary-input
value/cost theorems establish the composition independently of these closed
checks, and a separate theorem connects the value to conaled's cached summary
observation.

## Statement review and continuing scope

All values are mathematical integers and all inputs are finite lists. Negative
values, zero totals, empty blocks, exhaustion, early positive stopping, and
arbitrary nonempty tails remain in scope. No positivity premise is smuggled into
the whole-input upper bounds. Cached correctness is claimed for the canonical
labels and initialized total; arbitrary invalid cache data are not treated as a
correct collapse implementation. Traces identify the selected block prefix, not
only its flattened value.

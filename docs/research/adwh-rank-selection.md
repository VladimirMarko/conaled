# Occurrence-rank selection (#165)

`Applications.Selection.Rank` defines `RankedAt xs k a` independently of an
algorithm: a permutation of the input splits into `pre ++ a :: post`, with
`pre.length = k`, every prefix value at most `a`, and every suffix value at least
`a`. Duplicate values retain their occurrences. `ranked_iff_index` connects this
contract to the existing `Applications.Sorting.sortOn id`, backed by standard
`List.mergeSort`. `RankedAt.unique` identifies the selected value, not an input
occurrence. The contract itself needs only `LE`; sorting and value uniqueness
use a linear order. `RankedAt.map` needs preorders and a monotone map.

`Applications.Selection.ThreeWay` uses standard `List.partition` twice. Its
filter theorem identifies the strict-lower, equal and strict-upper blocks;
its permutation theorem retains all occurrences. The dispatcher keeps the
source's positional indexing within the equal block. `PivotValid` is a law on
an ordinary `List α → Option α` function, constrained only on nonempty inputs.
The executor checks empty input before calling the policy. Both head and last
occurrence policies satisfy this law.

`partition_strict_sizes` proves both recursive blocks are smaller when the
pivot belongs to the input. `runWith_value` proves that input-length fuel is
sufficient and agrees exactly with sorted indexing. Insufficient fuel can
return `none` for a valid rank; it is not mathematical absence. `selectWith`
supplies adequate fuel and exposes the source's one-based indexing convention.
Its `none` result means rank zero or rank larger than the input length.
`selectWith_some_iff` gives the independent occurrence-rank contract in both
directions. Policy independence follows from this contract and failure
semantics. It says nothing about equal execution traces or comparison costs.
`sortSelect` gives the standard sort/index baseline, with the same rank and
failure contracts. There is no new sorting implementation.

`Applications.Selection.Consumers` contains two clients of those public
results. The lower median uses one-based rank `(xs.length + 1) / 2`, returning
none on empty input. Its odd/even index results allow duplicates. Exact counts
of strictly smaller and strictly larger values require `Nodup`; for an even
input of length `2*r`, the counts are `r-1` and `r`. `selectWith_map` transports
selected values under any monotone map and any valid source/target policies.
Injectivity is unnecessary, since several values may become equal while still
occupying their original rank positions.

## Checked uses and statement review

`Examples.RankSelection` consumes public baseline, rank, policy, adequacy and
consumer results. Cases cover empty and singleton inputs; rank zero and rank
too large; first and last ranks; all equal values; Boolean order; and head/last
agreement. The input `[1,2,2,3]` at rank 3 returns 2 but has just one strictly
smaller entry, disproving the strict-count equation without distinctness.
Odd and even median examples specialize their count theorems. Division by two
is proved monotone and noninjective and is used through both rank transport and
selector transport. A valid policy deliberately returns `some 99` on empty
input; public failure and the executor's explicit empty branch still apply.
A zero-fuel failure is paired with the successful public selection.

The first obligation was the missing connection from independent positional
rank to standard sorting and pivot execution. Once rank/index equivalence was
proved, cases were connected through it and then through the public selector
and consumers. Concrete sorted observations use the existing theorem equating
merge sort and insertion sort; they do not require a copied sorter.
Statement review checked each definition and theorem family: zero versus
one-based indices, permutation multiplicities, weak inequalities around equal
values, two-sided rank/index equivalence, nonempty-only pivot validity, explicit
empty execution, strict recursive size and fuel premises, failure versus fuel
exhaustion, median division/truncation at zero, distinctness in strict counts,
and the absence of injectivity or execution-equivalence assumptions in value
transport. The retained examples exercise these boundaries with inhabited
orders and valid policies. Calls are direct Lean functions and theorems, with
no language, syntax, registry or specialized transport interpreter.

## Preserved source and scope

The [declaration ledger](adwh-rank-selection-provenance.tsv) records all named
source declarations in the five inspected modules, with exact immutable member
hashes, destination declarations and retained/deferred disposition. All hashes
were recomputed from the repository's preserved ZIP and checked against both
the manifest and the extracted reference. The ledger does not claim completion
of any larger chapter or imported module closure.

The selected contracts and proof ideas come from `TreePartitions`,
`QuickSelection`, `SelectionThreeWay`, `SelectionRank` and `SelectionBaseline`.
The reconstruction replaces the source partition implementation with standard
partition and the source quicksort/mergesort closure with existing sorting.
Independent value uniqueness, last-pivot validity, monotone rank/value transport
and generic lower-median consumers are local additions. The concrete
`LinearOrder` presentation supplies the source's lawful total-order operations;
it does not assert a claim for preorders where distinct values may be equivalent.

Median-of-medians and group balance, tree partitions, source quicksort demand
and instrumentation, baseline sorting work, recursion/cost traces, adversaries,
two-list/tree/array selectors, and complexity or runtime claims remain deferred.
The historical files remain intact in
[checkpoint-233](../history/algorithm-design-haskell/README.md).

Validation: `direnv exec . lake build Examples.RankSelection` checks all three
library modules and their clients. The examples are imported by the public
entrypoint and enter the normal build and proof audit. Fresh whole-repository
checks and independent Standards/Spec review belong to the integration session.

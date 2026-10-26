# Ordered partitions and paragraph layout reconstruction

Issue [#168](https://github.com/VladimirMarko/conaled/issues/168) is in progress.
This checkpoint reconstructs its complete ordered-partition foundation. The
paragraph client, global layout objectives, helper refinement and relational
consumers remain required work; this is not a completion or acceptance record.

## Ordered-partition checkpoint

`Applications/OrderedPartitions/Left.lean` defines independent `IsPartition`
semantics: flattening gives the original list and every block is nonempty.
Occurrences and order are retained. These ordered contiguous blocks are distinct
from the connectivity library's finite-carrier partitions.

The actual left-extending generator and its source helpers retain their order
and total extensions. Completeness, absence of duplicate partitions, and entry
counts hold for arbitrary element types, including repeated input values.
Empty input has one partition, the empty list of blocks. A nonempty input of
length n has `2^(n-1)` partitions. These are output-entry counts, not execution
costs.

`Right.lean` retains the actual right-extending foldl and proves its correspondence
with left enumeration under reversal. Its permutation theorem does not identify
the two generators' output orders. The source reverse-induction helper forwards
to Mathlib `List.reverseRecOn`. Nonempty-block and flattening laws justify the
reversal correspondence independently of enumeration.

Left pruning requires suffix closure of the block predicate; right pruning
requires prefix closure. Both exact filter equalities use the shared
`SquareKit.ListFusion.foldr_reachable`/`foldl_reachable` laws. Their one-step
commuting equations hold on arbitrary candidate lists, so the invariant is
`True`. The source total `headOk`/`lastOk` behavior remains explicit.

`Enumeration.lean` retains grouped foldr and recursive split enumeration.
The recursive definition's attached membership proof justifies decreasing suffix
length; `partsRecursive_cons` removes that proof attachment from the public
source equation. Recursive, grouped and right-extending generators have exactly
equal output lists. The grouped-versus-interleaved permutation helper reuses
`List.flatMap_append_perm`.

Mathlib's `List.splitLengths` was inspected: it splits using externally supplied
lengths, rather than enumerating every ordered partition in these source orders.
It does not directly replace these generators. Standard list flattening,
reversal, membership and permutation interfaces are used for their laws.

## Cases and statement review

`Examples/OrderedPartitions.lean` connects the public results to:

- Empty input's unique empty partition.
- Repeated `[1,1,1]`, with four distinct ordered partitions.
- Exact left and right orders on `[1,2,3]`, their permutation and inequality.
- Independent feasibility and rejection of empty blocks.
- Exact recursive and grouped output orders through their equality theorems.
- A length-two block cap, proving suffix/prefix closure before applying pruning.
- Even-length block predicates, which expose failure of unrestricted early
  pruning in both directions: the complete pair is admissible, but its singleton
  intermediate state is discarded.

Statement review checked arbitrary element universes, nonempty-block premises,
flattening order and occurrence preservation, exact equality versus permutation,
and the direction of closure needed by each fold. Repeated input values do not
make the output list contain duplicate partitions. The count's empty boundary
is separate from its exponential nonempty formula. Termination requires the
split prefix to be nonempty; the source split-membership theorem supplies it.

## Provenance and remaining work

Both source members below were compared byte-for-byte with the preserved ZIP
and hashed for this checkpoint:

| Archive member under `project/adwh-lean/ADWH/Chapter12/` | SHA-256 |
| --- | --- |
| `Partitions.lean` | `1301bd5577317a671f3892ff391e35ee4017b2f35424d74f94756a18c430c427` |
| `ParagraphGreedy.lean` | `b0aad857b5c1469c400d5e4fe1a717192e07b426cb3269c7213cfb59e7f46258` |

The [declaration ledger](adwh-paragraph-layout-provenance.tsv) records all 209
named source declarations: 109 adapted partition declarations, four recovered
through shared results, and 96 pending paragraph declarations. Anonymous
examples and generated declarations are not counted separately. The immutable
reference is [checkpoint233](../history/algorithm-design-haskell/README.md).

The next increment must retain actual character-list width, independent fitting
partitions, candidate versus greedy bind/snoc order, source-call domains,
lexicographic global optimality, minimum line count and last width, and the exact
helper refinement with its `AllWordsFit` premise. It must add both consumers
using standard lexicographic scores and the shared optimization/observation
squares, and preserve the specified counterexamples. No portion of that scope
is dropped by this checkpoint. Later paragraph waste objectives, caches and
resource models remain outside #168 as recorded in its specification.

Targeted validation is `direnv exec . lake build Examples.OrderedPartitions`.
Full fresh build, exhaustive audit and independent reviews are still required
for the completed issue.

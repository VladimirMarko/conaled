# Ordered partitions and paragraph layout reconstruction

Issue [#168](https://github.com/VladimirMarko/conaled/issues/168) reconstructs
ordered contiguous partitions and the greedy paragraph-layout client. Global
correctness compares the returned paragraph with every independently fitting
partition of the original character-list text. The helper implementation has
exact layout equality under the source word-fit premise.

## Ordered partitions

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

## Paragraph realization and shared objective

`Applications/Paragraphs/Candidates.lean` retains actual words as `List Char`
and the source nonempty width recurrence, extended by width([])=0. Independent
`FitsLine` counts word characters and one separator between consecutive words.
`width_formula` connects that specification to the operation. Prefix/suffix
width monotonicity supplies both closure contracts used by partition pruning.
`FitPartition` requires flattening to the complete text, nonempty lines, and
independent fitting bounds. The fitting candidate generator uses source
snoc-before-bind order, with exact equality to a filtered partition enumeration.

`Greedy.lean` keeps the different source bind-before-snoc filtered-head operation
and its left fold. `AddDomain` and `FoldDomain` follow actual intermediate states
and justify nonempty source partial calls. `greedy_fitPartition` needs only
`AllWordsFit`: each token fits individually. The stronger `SourceInput` also
requires nonempty text and nonempty words without spaces; that condition is
used for the printed source domain, not imposed on mathematical optimality.
The mathematical extension therefore also handles empty text and empty tokens.

`MinimumLex` is an independent global predicate. Its `CostLE` orders paragraphs
by line count first, then last-line width. `lexCost` uses Mathlib `Nat ×ₗ Nat`,
and `costLE_iff_lex` connects the exact source predicate to that standard order.
Reflexivity and transitivity reuse its laws; no parallel custom ordered score
structure is introduced. Global comparison retains the contextual premise of
`add_cost_mono`: both old paragraphs partition the same text and the new word
fits. The proof-only candidate enumeration supplies predecessors of arbitrary
feasible competitors. The conclusion establishes minimum line count and minimum
last-line width among equal-count competitors. It does not claim that line
count alone satisfies the local greedy condition.

`Helper.lean` retains the actual recursive helper and initialized `greedy2`.
`help_foldl` is an arbitrary-accumulator identity, while `help_fitPartition`
separately requires a nonempty fitting initial line. `greedy2_eq_greedy`
requires `AllWordsFit` and gives exact paragraph equality. `HelpDomain` and
`Greedy2Domain` record source-definedness along the actual helper trajectory.
Oversized tokens demonstrate why unconditional helper equality is false.

`Observation.lean` defines the problem as a width/text pair carrying its
`AllWordsFit` proof. `minimumLex_iff_minimizer` connects independent global
optimality to shared optimization semantics. `witnessSquare` reuses
`Optimization.selectionSquare`. `lineCountSquare` is actual relational
composition with `Optimization.observationSquare cost1`; the problem identity
is retained and the specification is the image of permitted optimal layouts.
The public observed count is attained by a globally optimal layout, bounds
every independently feasible competitor, and equals any minimum-line witness's
count. Distinct tied layouts are permitted. Shared square infrastructure is
used directly, without duplicating the segment or subsequence observation.

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

The paragraph cases in `Examples/ParagraphLayout.lean` use exact character-list
values from the source, plus cases selected to separate the domains and orders:

| Cases | Public connection |
| --- | --- |
| `empty`, `singleton`, `empty_word_extension` | Global optimum under the weaker mathematical domain; empty text/token exclusion from `SourceInput` remains separate. |
| `exact_width`, `source_domains` | Both realizations agree at the inclusive width boundary; the general equality and source-domain theorems are instantiated. |
| `lex_count_priority` | One full line wins despite a wider last line, exercising the standard lexicographic bridge and excluding componentwise interpretation. |
| `candidate_order` | Both candidates fit but exhaustive and greedy candidate orders are reversed. |
| `repeated_layout`, `repeated_count` | Repeated token occurrences through the witness and composed line-count consumers. |
| `book_layout_consumer`, `alternative_optimum`, `tied_layouts` | Printed widths `[6,1,5,3,4,7]` at maximum ten, two distinct globally optimal layouts, and observed count four. |
| `exercise12_14_condition_failure`, `exercise_append_outputs` | Feasible equal-count predecessors violate the count-only local condition; their exact successor layouts are retained. |
| `printed297_both_bind_equality_counterexample`, `both_bind_inequality` | The printed equality fails with all relevant premises, while the valid nonstrict source monotonicity theorem applies. |
| `oversized_divergence` | Violating word-fit produces different totalized greedy/helper results. |

Statement review of paragraph claims checked character tokens rather than token
lengths as the represented input; the latter are used only to construct the
worked examples. Global feasibility preserves token occurrences and order.
Width uses natural subtraction solely for the number of separators; its
nonempty and empty equations agree with the independent formula. The fitting
bound is nonstrict. The objective uses standard lexicographic order, and the
same-text premise remains on local monotonicity. No theorem assumes the final
global optimum as a correctness hypothesis. Source partial-call obligations,
initialized helper validity and arbitrary-accumulator refinement have separate
premises. The observation domain contains exactly the required word-fit
evidence, with no extra source restrictions or invented invalid-input guarantee.

## Provenance and remaining scope

Both source members below were compared byte-for-byte with the preserved ZIP
and hashed for this reconstruction:

| Archive member under `project/adwh-lean/ADWH/Chapter12/` | SHA-256 |
| --- | --- |
| `Partitions.lean` | `1301bd5577317a671f3892ff391e35ee4017b2f35424d74f94756a18c430c427` |
| `ParagraphGreedy.lean` | `b0aad857b5c1469c400d5e4fe1a717192e07b426cb3269c7213cfb59e7f46258` |

The [declaration ledger](adwh-paragraph-layout-provenance.tsv) records all 209
named source declarations: 202 adapted and seven recovered through shared
results. None of the two-module source scope remains deferred. Instances
preserve the executable decidability of independent fitting, word-fit and source
domain predicates. Anonymous source examples are represented by named public
applications; generated declarations are covered by the normal exhaustive
audit. They are not counted as separate ledger entries. The immutable
reference is [checkpoint233](../history/algorithm-design-haskell/README.md).
New lexicographic/minimizer bridges and relational consumers are local
constructions, not source declarations.

Later signed paragraph waste objectives (`ParagraphObjectives`,
`ParagraphCost2`), caches, RTL/thinning frontiers, bank transfers and resource
models remain outside #168. In particular, this reconstruction does not claim
that greedy optimizes costs3–5, or the separately derived cost2 identity.
Retained partition counts do not imply runtime or physical allocation bounds.

Targeted validation passed with `direnv exec . lake build
Examples.ParagraphLayout Examples.OrderedPartitions`. Source hashes, all 209
unique provenance rows and active destinations, and whitespace were checked.
The complete fresh build, exhaustive axiom audit and independent reviews are
supervising integration checks.

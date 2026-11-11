# ADWH reconstruction coverage and successor reconciliation

[#149](https://github.com/VladimirMarko/conaled/issues/149) owns the full textbook
reconstruction. The [source map](adwh-reconstruction-map.json) keeps every one of
the 1,240 main-library source modules visible. It is a routing and provenance
record, not a percentage of mathematical completion. GitHub Issues own task
specifications, acceptance and current status.

## Evidence and grouping

The generator checks the preserved ZIP digest and each actual source member
against [the original inventory](adwh-preview-233-inventory.json). Each record
retains its imports, immutable source identity, routing family and original
correspondence member/hash. All 1,239 nonaggregate modules have a correspondence
record. `ADWH` is the aggregate entrypoint. The map also identifies all 32
chapter scope/coverage ledgers by archive member and hash.

**266 correspondence records contain an embedded `source_sha256` that differs
from the preserved source bytes; 973 agree.** The map records both the historical
field and `source_hash_agreement`. The actual source member hash is authoritative
for reconstruction provenance. These mismatches do not alter the source hashes
or establish false theorems, but the correspondence cannot certify current-source
coverage without reconciliation. Inspect the current declaration and recorded
contract before adopting it. Source compilation and audit belong to
[#150](https://github.com/VladimirMarko/conaled/issues/150).

The [family definitions](adwh-reconstruction-families.json) group mathematical
observations and consumers. Their selectors are review routing rules, with the
first match taking precedence. They are not proposed Lean directories or
assertions that everything in a group shares one interface. The preserved
imports expose dependencies across groups. Each source correspondence supplies
more specific contracts, limitations and theorem references; a broad group does
not erase those distinctions.

| Routing families | Reconstruction direction and remaining scope |
|---|---|
| Finite list folds/scans/compression; partial lists | #152 covers reachable fusion and an inclusive scan bridge. #157 covers adjacent-run compression. Partiality, lazy demand, suffix scans and remaining list derivations still need separate contracts. |
| Asymptotic/recurrence/amortized reasoning; sequence representations | #154 starts instrumented composition. Growth proofs, array/tree indexing and allocation models remain to be selected against actual consumers. |
| Ordered search; sorting; rank/selection | Keep sortedness, permutation, stability, rank and query lower bounds distinct. Tree split/join clients may justify shared laws; naming overlap does not. |
| Coin choice; weighted tree construction | Compare enumeration, greedy and tabulated realizations against independent objective semantics. Canonical denominations and tree exchange hypotheses are local premises. |
| Connectivity; graph paths/forests/tours | #158 covers partition observations and list/array histories; #169/#172 cover Kruskal tree/forest minima; #180 covers finite Dijkstra. #183 covers ordinary Prim, #184 finite-sentinel Dijkstra and #186 matrix/array Prim. #187 adds Dijkstra state execution costs; other finite sentinels, graph costs and jogger tours remain separate obligations. |
| Thinning; knapsack; layered paths | #151 covers a bounded dominance/optimization slice. Fractional boundaries, integer tables, other frontier variants and full cost recovery remain. Layered paths are not endpoint shortest paths. |
| Subsequences/edit distance; contiguous segments; ordered partitions | Reuse enumeration/optimization transport only after preserving embeddings, edit weights, empty segments, admissibility and tie direction. Bank and paragraph clients retain distinct objectives. |
| Numeric/shuttle recurrences; interval DP; alphabetic trees | #153 covers generalized-cost bracketing. Numeric tables, shuttle objectives, other interval optimizations and Garsia–Wachs reductions/AVL execution remain. |
| Finite numeral/floating arithmetic; arithmetic expression search | Keep finite arithmetic and error contracts explicit. Expression enumeration does not inherit a rounding theorem from output equality. |
| Constraint counting/queens; transition search/planning; concrete puzzle/geometric realizations | #155 covers bounded static heuristic search. #137 separately owns checker/CSP intake. Concrete encodings, certificate chunks and geometric safety remain attached to their own semantics. |
| Infrastructure | Preserve aggregate coverage and counterexample evidence while integrating selected modules through conaled's existing public entrypoint and audit. |

The initial bounded follow-ups are
[#157, adjacent-run compression](https://github.com/VladimirMarko/conaled/issues/157)
and [#158, connectivity refinement](https://github.com/VladimirMarko/conaled/issues/158).
Their specs name inspected source interfaces, independent semantics and checked
clients. Other rows remain owned by #149 as untouched reference, not silently
deferred. Further issue slices must name a public contract and actual clients
before assigning a shared abstraction.

[#160, keyed merge and stable sorting](https://github.com/VladimirMarko/conaled/issues/160)
now pins the corresponding source contracts and standard sort realizations,
preserving the distinction between
sorted permutation and equal-key order. #157 has a pinned reconstruction candidate
and declaration ledger; its counted executor and generic guarded-drop results remain
reference. #159 pins a static rational/infinity adapter on top of #155, with the
Nat theorem reuse distinguished from new local transport proofs. #158 now pins its
list/array histories, finite connectivity and query/cycle-rejection consumers.
[#161](https://github.com/VladimirMarko/conaled/issues/161) pins bounded segment
optima and the source thinning scan; #164 supplies the subsequence slice, while cost models remain reference.
[#162](https://github.com/VladimirMarko/conaled/issues/162) pins complete immutable
knapsack initialization, rows and observation, extending #154 with exact selection
and whole-workload scalar recovery.
[#163](https://github.com/VladimirMarko/conaled/issues/163) pins coin enumeration
and lexical versus minimum-count choice, including first/last/descending ties.
#165 pins occurrence-rank selection, median and monotone-value transport.
#164 pins increasing-subsequence enumeration and ordered thinning, including
shared witness observations. #166 pins Huffman global optimality and exact queue
construction. #167 pins fixed-price
edit alignment with cached row refinement. #168 pins ordered partitions with greedy
paragraph layout. #169 pins disjoint-set Kruskal and global spanning-tree
optimality, with the numbered source adapter and exact residual behavior.
#170 pins finite symmetric lists and prefixes; #171 pins binary random-access
lists. #172 pins nested Kruskal and global minimum spanning forests.
#173 pins potential accounting and #179 pins ordered binary search.
#180 pins finite Dijkstra distances, ordered paths, target stopping and actual
closed-search queue agreement. #181 pins measured lookup and bulk update costs;
#182 pins carry/borrow accounting and its mixed-cycle counterexample.
#183 pins ordinary growing-tree Prim with visited-cut exchange and actual
Kruskal cost agreement. #184 pins finite-sentinel Dijkstra and its range proof.
#186 pins matrix overwrite semantics and array Prim with attained-cost comparisons.
#187 pins measured Dijkstra execution and exact failure charging. #190 completes
tree-flattening traversal costs, raw cache-erasure simulation and standard growth claims.

## Dispositions and declaration coverage

[Scope records](adwh-reconstruction-scopes.json) link #151–#155, #157–#173, #179–#184, #186–#187 and #190
and pin the #151–#155, #157–#173, #179–#184, #186–#187 and #190 candidate destinations. Resolve candidate paths
at those exact commits until integration; they need not exist at the map's base
commit. Candidate evidence is partial reconstruction pending acceptance, never
a whole-module parity assertion. The pinned candidate commits are retained in the integration ancestry, so their
paths remain resolvable after cloning. GitHub acceptance records identify the
integrated result; any changed declaration needs a new record or explicit
supersession of the candidate evidence. #111, #137, #109 and #113
remain separate commitments.

Use these dispositions with an explicit source scope:

- **Untouched reference:** no reconstruction selected in this map.
- **Scoped task:** a linked issue owns a named slice; imports needed to prove it
  are not automatically migrated in full.
- **Partial reconstruction:** named candidate declarations exist. Other source
  declarations remain reference and acceptance stays with the issue.
- **Accepted retained/adapted result:** acceptance evidence identifies the exact
  declarations, destination commit, reviewed assumptions and checked uses.
- **Replaced with proved equivalence:** additionally name the equivalence theorem
  and its domain/observation. Merely using a similarly named Mathlib lemma is
  insufficient.
- **Explicit deferral:** link a recorded reason and follow-up owner. No initial
  family is assigned this disposition merely because it was not a pilot.

A replacement record identifies `(snapshot, archive_member, source_declaration,
member_sha256)` plus the destination file/declaration, immutable commit, issue,
disposition and exact scope. The scope file contains concrete #151–#155 examples and the #157 declaration ledger;
the linked candidate declaration maps supply the full pilot detail. This map
does not copy their entire acceptance history. Future records must preserve
source exceptions, failure behavior, ties and theorem assumptions.

In particular, retain the Chapter 6 groups-three qualification in
`project/docs/chapter06.md` and `GroupRecurrenceLimits.lean`: the recurrence
countermodel refutes an inference, not the actual selector's superlinear
worst-case claim. Do not turn its accepted research disposition into either a
new theorem or an alleged defect. The stock
`cqueens 16 = 14772512` proof and unfinished Installed/GroupChecked endpoints
remain open; historical execution records do not close them.

## Reproduction

From the development shell:

```sh
python3 scripts/build-adwh-reconstruction-map.py --check
python3 scripts/test-adwh-snapshot-diff.py
python3 scripts/adwh-snapshot-diff.py \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  --output /tmp/adwh-self-comparison.json
```

The generator without `--check` regenerates the map after a reviewed change to
the routing/scopes. It fails on missing correspondence, unassigned source
modules, unknown scoped modules or source hash drift. Embedded correspondence
hash disagreement is preserved as evidence, not silently repaired.

The archive self-comparison has 10,463 unchanged members and no additions,
removals or changes. Six CLI fixture tests cover changed/added/removed content,
build-control deltas, unchanged inputs, ambiguous relocation/copies, duplicate
members, nonrelative members and input-overwrite rejection. These tooling checks
introduce no Lean claims and do not replace the formal build/audit gates.

## A later snapshot

Preserve the successor as a new immutable snapshot using the
[historical intake procedure](../history/algorithm-design-haskell/README.md).
Never overwrite checkpoint 233. Then run:

```sh
python3 scripts/adwh-snapshot-diff.py \
  docs/history/algorithm-design-haskell/checkpoint-233.zip \
  /path/to/preserved-successor.zip --output /tmp/adwh-successor-diff.json
```

The report gives member hashes and added/removed/changed/unchanged paths.
`relocation_candidates` groups equal bytes among removed and added paths; copies
make the match ambiguous, so it does not invent a one-to-one rename.
`dependency_review` includes full textual changes to recognized toolchain,
Lake and Nix controls and lists all affected Lean files. This is byte-level
reconciliation, not a Lean import parser or a dependency resolver.

Review control diffs for changed dependency pins. Inspect affected Lean sources
for import changes, rebuild the source dependency inventory, then compare its
import edges with this map. Use both old and new edges to identify reverse
consumers: removal of an old dependency can matter even when no new edge exists.
Recheck the affected transitive closure with the successor's pinned toolchain
and the exhaustive audit. Changed controls or uncertain dependency resolution
require a fresh full check. Equal member bytes do not certify equal elaboration
under changed imports, dependencies or compiler versions.

For each migrated declaration, first match the old member/hash, then review its
successor declaration and assumptions. A changed path with identical bytes can
reuse the source identity link after relocation review; a changed declaration
needs semantic comparison and checked examples. Preserve old provenance and add
the new snapshot identity, equivalence/correction evidence and acceptance issue.
No real successor was available when that tooling was delivered. The current
[checkpoint-335 intake](adwh-checkpoint-335-intake.md) compares the supplied
compact recovery payload against the checked-in predecessor inventory, keeping
this historical map intact. The fixtures and self-check still exercise the ZIP
comparison mechanics; they do not by themselves validate the nested successor
format or its Lean proofs.

## Recovered Chapter 1 and Chapter 2 integration

The [recovered integration](adwh-recovered-integration.md) adds list/partial-list,
numeral/floating, resource/growth, exact-arithmetic and recurrence results, plus
generic search counting from checkpoint 335. Its per-development declaration
ledgers extend the historical routing map above; that generated checkpoint-233
map remains a record of its original scoped tasks. These additions do not close
Chapter 2 or the textbook umbrella. The successor inventory stores only changed
and added source records, reusing unchanged predecessor identities.

## Recovered continuation research

The [external continuation handoff](adwh-recovered-handoff.md) records the
retired private-ticket dispositions, remaining Chapter 2 designs, later-chapter
research questions and capability-audit requirements. Its
[research synthesis](adwh-recovered-research.md) preserves counterexamples and
observation contracts. These notes supplement the existing declaration map;
they do not mark deferred rows accepted or certify whole-chapter parity.

## Useful recovered mathematics audit (#458, 2026-11-11)

Baseline: `3c064b11a5812e38c317601473e6897f65ce2a32`, including the accepted
recovered integration `1e7bee1e`. The owner sets three criteria: retain useful
built mathematics, cover *Algorithm Design with Haskell* with factual
corrections, and make the results useful to conaled. Checkpoint 335 supplies
comparison evidence; its declarations and private completion labels are not
requirements to copy an inferior formulation.

This audit reconciles the existing declaration ledgers and current public
contracts. It does not replace them with another declaration inventory. The
[validation record](adwh-useful-coverage-validation.json) records the source-hash
checks, primary-source identities and focused elaborated-type inspection.
The [integration record](adwh-recovered-integration.md#usefulness-and-observation-audit)
records the retained mathematical distinctions and consumers. The [R1 disposition](adwh-r1-disposition.md) accounts for the selected list-cost family using #468, #469 and existing exact head/reverse contracts. R2–R7 remain implementation work under #459; Chapter 2 and #149 are not complete.

### Book evidence and corrections

The [authors' materials](https://www.cs.ox.ac.uk/publications/books/adwh/)
provide the [official extracted code](https://www.cs.ox.ac.uk/publications/books/adwh/code.zip)
and [errata](https://www.cs.ox.ac.uk/publications/books/adwh/errata.html).
Downloaded on 2026-11-11, `part0/chap1.hs` and `part0/chap2.hs` exactly match the
preserved extracted sources. The code's `LINE` directives identify the original
literate source, not printed page numbers. The relevant anchors are recorded
below. Publisher metadata locates [Chapter 1, Functional programming](https://doi.org/10.1017/9781108869041.003)
and [Chapter 2, Timing](https://doi.org/10.1017/9781108869041.004).

The full printed chapters and PDF used by the historical source reviewer are
not present in the recovered inputs. Thus prose-only page/exercise attributions
below are inherited from `project/docs/chapter01.md`, `chapter02.md` and their
coverage records in the preserved archive, rather than a new reading of every
printed passage. The audit directly checks the official code and errata, current
formal statements and the recorded mathematical corrections. A fresh
whole-chapter textbook certification still requires the missing printed source;
#149 owns that evidence obligation. No historical `chapter_complete` flag is
promoted to a local completeness theorem.

The official errata correct p29's exponential recurrence conclusion to Theta
of `2^n`, and p39 Exercise 2.8's incremental toll to Theta of `n`, uniform in the
other parameter. The current recurrence and growth ledgers retain both
corrections. The archive also records independent mathematical corrections,
which must not be attributed to the official errata: failed stopping tests in
`build` change its source-priced amortized constant; finite digit-search means
include terminal failures; permutation growth depends on the actual generator
and observer; literal and eager array resizing have different boundary policies.
Their implementation dispositions are separate below.

### Chapter 1 selection and current disposition

Every source module in the recovered Chapter 1 selection is assigned in this
table. Links lead to the existing contract/declaration records. The disposition
concerns those stated domains and observations, not Haskell/GHC semantics or
machine timing. Anonymous examples and context qualifications remain in the
linked ledgers; wrappers and proof-script helper names need not become new APIs.

| Source modules under `ADWH.Chapter01` | Book/extracted-code connection | Current disposition and useful owner |
| --- | --- | --- |
| `Lists`, `Interfaces`, `SourceDerivations` | Chapter 1 types/folds; `LINE` 75–194, 739–795, 947–1017 | [Finite-list ledger](adwh-finite-lists.md): standard List operations and checked interface/derivation clients; partial selectors use Option with explicit domains. Keep the printed recursive destructor folds distinct from extraction wrappers. |
| `ScanFusion` | Prefix/suffix Scan Lemma and reachable fusion; 244, 871 | [Scan bridge](adwh-scan-bridge.md) plus [finite correspondence](adwh-finite-correspondence.md): ListFusion and InclusiveScan; arbitrary initial accumulator and noncommutative order. Existing `foldr_tails_eq_scanr`, `scanr_suffix_values` and the reachable parity clients supplement the later finite ledger, rather than representing missing work. |
| `Iteration` | `until`/`while`, fixed-count iteration; 382–390, 839, 1077 | [Ranked iteration](adwh-ranked-iteration.md) and finite correspondence: `UntilSpec`, ranked `runUntil`, first-hit/invariant/rank independence and explicit divergence controls. Dijkstra/Huffman use the shared owner. Core repeat and Mathlib iterate replace redundant fixed-count wrappers. |
| `Accumulation` | Collapse variants and fixtures; 561–630 | [Accumulation](adwh-accumulation.md): signed values, independent shortest-positive-prefix specification, cached sum and arbitrary-tail difference-list invariant. No positivity assumption on input elements. |
| `SteepCosts` | Steepness/tupling, 1178–1196 | [Steepness costs](adwh-steepness-costs.md): actual naive/tupled demand, short-circuit costs and worst-case witnesses; useful evidence for resource-aware fusion. |
| `CollapseDemand`, `CollapseAppendCosts` | Collapse accumulation and demand, 571–630; inherited Exercise 1.19/1.20 | [Collapse resources](adwh-collapse-resources.md): retained consumed-block demand, cached sums and append materialization; discarding unused labels does not force their sums. |
| `StructuralCosts`, `FusionCosts` | Fold variants and concatenation, 122–194, 788–795 | [List resources](adwh-list-resources.md): executing folds/reversal/append and exact structural savings; reuses measured bind and existing tree-flattening append accounting. |
| `Permutations`, `ErasePermutations` | `perms1/2/3`, insertion, picks and removal; 273–355, 849, 1091–1100 | [Permutation ledger](adwh-permutations.md): exact occurrence order, positional picks versus first-occurrence removal, duplicates and common prefix; Occurrences is also consumed by forest algorithms. This does not supply Chapter 2 measured permutation execution. |
| `PartialLists`, `LazyListDomain`, `InfiniteLists` | Unknown/infinite lists, head and foldr; 177; inherited Exercise 1.16 | [Partial-spine observations](adwh-partial-spine-observations.md) and [directed limits](adwh-directed-limits.md): bottom/nil/cons distinction, ideal completion and strict continuous fusion, with actual Progress observations. Label refinement and whole-language laziness are outside this model. |
| `InfiniteListFusion` | Append/flatten/fold fusion; 194, 308 | [Partial append](adwh-partial-append.md) and [concat](adwh-partial-concat.md): arbitrary partial inner/outer spines, infinite-prefix suffix invisibility, explicit continuity/strictness. |
| `LazyListEvaluation` | Seed-inclusive scan and strict left folds; 122, 244; difference collapse 613 | [Seeded scans](adwh-seeded-scans.md), [left folds](adwh-partial-left-fold.md), [difference concat](adwh-partial-difference-concat.md): real Mealy realization and operational observations; n-output lagged stream and n+1 finite seed-inclusive scan remain distinct. |
| `LazyListDemand` | Head, takeWhile and online labeling; 112, 177, 988 | [TakeWhile](adwh-partial-takewhile.md) and [zip](adwh-partial-zip.md): unknown predicate versus false, first-failure suffix independence, productive index stream; no length precomputation. |
| `LazyListMaps` | Map/filter and composition; 75–82, 308 | [Map](adwh-partial-map.md) and [filter](adwh-partial-filter.md): semantic and actual producer fusion, ordered predicate evaluation, all-reject infinite input remains bottom, not completed nil. |
| `Numerals` | Integer/fraction folds; 1043–1055 | [Numerals](adwh-numerals.md): integer/rational meanings and affine compositions, with parallel-scan consumer. Exact arithmetic laws are not assigned to rounded operations. |
| `NumeralsFloating`, `FloatingAlgebraLimits` | Floating interpretation of the same numeral fragment | [Observations](adwh-floating-observations.md) and [numeral certificates](adwh-floating-numerals.md): finite/NaN/infinity distinctions and nonassociativity controls; interval consumption retains the exact decimal as specification. |
| `FloatingRounding`, `FloatingShiftRound`, `FloatingPacking`, `FloatingArithmetic`, `FloatingMagnitude`, `FloatingNormalize`, `FloatingOperations` | Supporting actual-format interpretation, beyond bare Haskell numeral equations | [Rounding](adwh-floating-rounding.md), [packing](adwh-floating-packing.md), [normalization](adwh-floating-normalization.md), [operations](adwh-floating-operations.md): actual finite operation/normalization contracts supply the per-step premises, not a new floating implementation assumed sound by interface. |
| `FloatingNumeralBounds`, `FloatingNumeralsUniform` | Proper-digit certificates and uniform guarantees | [Bounds](adwh-floating-numeral-bounds.md) and [uniform result](adwh-floating-uniform.md): every finite proper-digit input obtains finite closed-range output and error certificate. Rounded one and underflowed zero remain permitted; interval square clients consume the guarantees. |

No new Chapter 1 capability defect was established in this audit. In particular,
the lexical absence of some old iteration/scan names from a later TSV is not a
missing theorem: earlier scoped records and current shared declarations supply
them. The combined records must be used, rather than treating one adaptation
ledger as the entire chapter.

### Chapter 2 and generic search selection

| Source modules | Audited disposition and subsequent reconciliations | Reuse or residual owner |
| --- | --- | --- |
| `Asymptotics` | Retained/adapted in [resource growth](adwh-resource-growth.md); signed one-sided comparison is separate from norm Big O. Anonymous sign/zero controls retained. | `Resources.Growth`, reverse/fold clients. |
| `FiniteSums`, `GeometricTail` | Retained/adapted in [finite sums](adwh-finite-sums.md), including derivative and quantitative tail statements. | Geometric-sum scan and weighted resources. |
| `LogarithmicScales`, `HarmonicEstimates`, `LogarithmicSums` | Retained/adapted in [discrete estimates](adwh-discrete-estimates.md). | ExactGrowthBounds and finite logarithmic-sum consumers. |
| `ExactGrowthSemantics`, `ExactGrowthClaims` | Corrected native replacement in [exact arithmetic](adwh-exact-arithmetic.md); explicit validity, exact logarithm/root interpretation and symbolic bounds. | Relational first-order/stack/interval compilation and ExactGrowthApplications. |
| `Recurrences`, `GeneralRecurrences`, `RecurrenceDerivations` | Retained/generalized in [recurrences](adwh-recurrences.md); independent base/tolls, eventual exceptions and uniform two-parameter threshold. | ResourceRecurrences and actual RecurrenceScans. |
| `Build`, `BuildEquality` | Retained/corrected in [guarded build](adwh-guarded-build.md); failed stopping test counted; lawful-equality run compression preserves nonadjacent occurrences. | GuardedBuild and RunCompression clients; code anchor 549. |
| `Timing`, `Amortized` | Already reconstructed by #173's [107-row ledger](adwh-potential-accounting-ledger.json), which also includes SymmetricListCosts. The two modules are not an unimplemented prerequisite. | Workload/Potential/BinaryCounter, arbitrary seeds and noncommutative ordered observations; code 579–595. |
| `BestWorst`, `UniformConcatenation` | #468 and #469 supply uniform concatenation and attained takeWhile extrema with executed fold consumers. Existing generic exact head/reverse contracts imply the remaining selected growth summaries; no new named Theta wrapper is claimed. | [Accounted R1 disposition](adwh-r1-disposition.md); #459 retains R2–R7. |
| `CompositionDemand`, `ContextLists`, `ContextConcatenation` | Finite value and partial-spine components exist; complete shared-cache/delayed-construction/append-history cost correspondence is not supplied by them. | #459 R2; code 457, 523, 1000–1022. |
| `Prune` | #470 supplies single trim; #471 adds folded prune, tail-closed recovery and native cumulative potential/budget bounds with ordered consumers. #472 supplies constant natural guard prices, including archived positive dispatch; selected source obligations are covered, pending parent/book reconciliation. SuffixTrim stays separate. | #459 R3; code 676; [single-trim dispositions](whole-list-trim.md), [folded-prune dispositions](folded-prune.md), [pricing dispositions](priced-prune.md). |
| `DynamicArray`, `DynamicArrayEager` | Fixed buffers/store updates provide reusable mechanisms, not policy-specific resizing and ordered allocation/copy traces. | #459 R4. |
| `DigitSearch` | #478 supplies measured first-hit execution, native ordered decimal population/function bridge, corrected finite-uniform mean and strict convergence bounds. | #459 R5; [source dispositions and limits](digit-search.md); inherited Exercise 2.13 attribution. |
| `CounterGeometric`, `CounterOutput` | BinaryCounter already supplies the counter/potential laws; independent floor-series derivation and executed token observation remain distinct. | #459 R6; code 586–595. |
| `PermutationConstruction`, `RemovalPermutationCosts`, `InsertionDemand`, `InsertionDemandGrowth`, `PermutationGrowth`, `PermutationObservations`, `PermutationRationalBounds` | Pure occurrence semantics retained; complete measured-pair correspondence, forcing/observation and resulting symbolic growth corrections remain. | #459 R7; code 354–358, 523, 845–851. |
| `Chapter15.SearchCounting` | All nineteen named source declarations retained/adapted in [search counting](adwh-search-counting.md), with richer decoder/checker clients. | FiniteSearch, SearchCount and Search.Counting. Exact-depth occurrences and checked residual backend; not legal BFS/DFS, distinct-state cardinality or queens-16. |

### R1 disposition and remaining contracts under #459

R1 is accounted for on the evidence linked below. R2–R7 refine existing ownership; they are not additional issues or approved whole-chapter deferrals. Each remaining family needs ordinary checked callers, statement review,
positive and rejecting cases, the applicable build/audit and independent review.
The current source-level absence claims concern the complete specified contract,
not the lack of a similarly named theorem.

| ID | Observable deliverable and acceptance cases | Useful current interface / dependency |
| --- | --- | --- |
| R1 | Accounted for: #468 supplies uniform concatenation and its fold consumer; #469 supplies attained takeWhile extrema and its prefix-fold consumer. Existing `head_work` and `reverse_work` subsume the selected head/reverse finite and growth summaries via explicit coefficient/threshold comparisons. | [Source-to-current disposition and boundaries](adwh-r1-disposition.md). No new generic Theta declaration or whole-chapter completion is claimed. |
| R2 | Execute cached cell requests with ordered history; distinguish delayed outer construction from forcing and first-head consumption from full materialization. Compare actual left append frames with right concatenation; keep unknown-end failure of fallback and infinite first block. | CollapseDemand/CollapseMaterialization and PartialSpine/Progress; source `observeCell`, `initsRun`, `initsAccRun`, `headRight`, `AppendExpr.observe`. Separate subpackages are appropriate when implementation begins. |
| R3 | Define whole-list-predicate trim/prune with independent longest-prefix specification. No monotonicity for trim; tail closure for identifying folded prune with one trim. Exact guard-priced cost/potential and `Pairwise` specialization; reject predicate accepting only `[1,2]` and adjacent-only test on `[1,2,1]`. | Reuse Workload/Potential and list operations; no replacement of existing SuffixTrim. Source `TrimSpec`, `trimRun_potential_exact` and `prune`. |
| R4 | One raw storage/event owner with literal and eager policies, copy correctness in arbitrary surrounding windows, full ordered events, every additive list price, grouping and arbitrary initial states/potentials. Distinguish zero-capacity/malformed raw states from layout-valid states. | Existing fixed buffer/store and Resources.run/reweight_run. Three- versus four-insertion examples must show that neither policy is uniformly cheaper. Source `copyInto_layout`, `add`, `adds`, `logical_agreement`. |
| R5 | First-hit Option index and exact inspection cost, ordered decimal enumeration and actual finite-uniform mean `2 - 2 / 2^n`, including failures. Empty word has cost zero in a singleton population; n=1 mean one and n=2 mean 3/2. Preserve convergence and finite strict inequality. | Finite sums/search; source `search_first_spec`, `search_work`, `words` and average theorems. This is a corrected book consumer, not an arbitrary distribution theorem. |
| R6 | Derive zero-start cost from actual even/odd branches as a floor series with cutoff, plus state-prefix/transition indexing and token-rendering/decode costs. Retain n states versus n−1 increments, arbitrary seed contracts, extending carry and bill order. | Existing BinaryCounter and Workload/Potential; do not reimplement Timing/Amortized. Source `totalCost_floorSeries`, `power_two_exact`, `transitionCosts_sum`, `prefixRun`, `renderState`. |
| R7 | Measured positional and first-removal generators, full measured-pair adequate-fuel correspondence, ordinary/accumulating insertion with explicit forcing, then one shared complete-spine observer and symbolic rational-constant growth/rejection. Preserve duplicates and each generator's order. | Occurrences/Permutations, FiniteSums/Growth. A varying-callback measured traversal is shared with R6 and must have one owner; constant-price `ListFusion.map` is not that contract. Source `perms2Run`, `perms3Run`, `permutationForce`, `no_rational_shifted_lower`. |

R1 needs no further theorem implementation for the selected source claims. R2 and R4 require explicit execution interfaces and should start with their independent observations. R6/R7 can share
one varying-callback traversal without making either depend on unrelated array
work. No private chapter-order gate is reinstated. Full Stirling expansion,
GHC timing/space and machine overflow are not silently accepted: they remain
outside these selected models, with their relevance assessed under #149 if a
concrete book or repository consumer requires them. Whole-book coverage and
source licensing remain #149; queens/kernel work remains #137.

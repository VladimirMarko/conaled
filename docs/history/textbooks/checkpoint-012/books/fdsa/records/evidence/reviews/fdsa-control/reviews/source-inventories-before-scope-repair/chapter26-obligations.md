# Chapter 26: Huffman's Algorithm — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-026`.

**State: queued; source preparation only.** No Lean change, build, ticket
or acceptance update, or remote write is performed by this inventory.
Rows identify future checked obligations and genuine existing reuse;
they do not certify chapter coverage or change chapter order.

## Sources and inspected pins

| Source | Inspected identity |
|---|---|
| Book | Jasmin Blanchette, Chapter26, printed pp.305–318, PDF pages311–324, July27,2026 version. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Direct manuscript link | <https://isa-afp.org/browser_info/current/AFP/Huffman/Huffman.html>; current browser pages are mutable. Entry <https://isa-afp.org/entries/Huffman.html>, Jasmin Christian Blanchette, published October15,2008. |
| Inspected companion | <https://isa-afp.org/release/afp-Huffman-2026-10-26.tar.gz>, 549,876 bytes, SHA-256 `229ba4f3037d9f02dff7df8836d8a5a95f91c8463c8572cb0ae1a93dea2bfd77`. |
| Main formal file | `Huffman/Huffman.thy`, 101,517 bytes, SHA-256 `7bdc838bbdf7347fb78440a5b3c8dadaf6b7c228e6e3cae6f2d1fb49582837bf`. Imports Isabelle `Main`; book definitions/results correspond directly to its named tree/forest/surgery theorems. |
| License | AFP entry advertises BSD; shared <https://isa-afp.org/LICENSE>, SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Retain source attribution/notices in adaptations. |
| Project/dependencies | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; inspected HEAD `1aabd512284fe86254278ac631eda061d311050b`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean4.35.0. Project/dependency inspection is not acceptance of local candidates. Relevant library files are Apache-2.0. |

The dated formal source postdates the book; its hash pins inspection, not
the unknown source revision used to generate the July PDF. Reading inputs
remain in `book-source/`; this original inventory/provenance is the
deliverable. The theory contains the word `sorry` once in historical
expository text about development tools, not as an active proof command.
No active admission was identified; no Isabelle build was run.

There are **no numbered exercises**. Scope includes all seven numbered
results, the three preservation formulas, the named raw functions and
forest predicates, the coding discussion's mathematical assertions, and
the three runtime claims in the notes. The question whether a Huffman
algebra might make the proof more elegant is methodological discussion,
not an asserted theorem or a request to formalize that entire external
paper.

## Existing conaled optimality proof and exact bridges

There is substantial reusable proof content. The current Huffman
development proves **global** weighted-path optimality against every
feasible full binary tree; it is not merely a heap implementation or a
local greedy-step claim.

| Existing component | Actual reusable result and boundary |
|---|---|
| `Applications/Huffman/Basic.lean` | Independent `weight`, `cost`, `depthsFrom`, `pathCost`, `pathCost_eq`; `Feasible xs t := (fringeSpec t).Perm xs`; `Optimal`; `ForestFeasible`, `ForestOptimal`, `cost_flatten`. These are occurrence-based and allow zero weights/repeated labels. |
| `Applications/Huffman/Exchange.lean` | `swap_cost_balance`, `swap_cost_le`, `DeepSiblings`, `deepSiblings_exists`, `deepSiblings_depth`, `deepest_exchange_distinct`, `contract_deep`, `greedy_exchange`, `forest_greedy_exchange`, `forest_greedy_refinement`, `forestOptimal_perm`, `forestOptimal_leaves`. Genuine deepest-sibling exchange and global forest optimality, including tied/repeated occurrences via tags. |
| `Applications/Huffman/Priority.lean` | `step` removes two minima and inserts the merged tree/cache; `step_size`, `step_spec`, `loop_spec`, `huffman_optimal`, `huffman_correct`, `huffman_none_iff`. A new exact sorted-list queue adapter can reuse this proof engine. Its generic iteration trace is not already the book's exact cached-tree recursion. |
| `Applications/Search/ExactPriority.lean` | `ExactQueue`/`ExactLaws` preserve all occurrences and minimum deletion. Use this interface; a keyed frontier that replaces equal keys has the wrong multiset semantics. |
| Mathlib `Data/List/Sort.lean` | `List.orderedInsert` with `r u t := cachedWeight u ≤ cachedWeight t` is literally the source insertion recurrence. `orderedInsert_length`, `perm_orderedInsert`, `List.Pairwise.orderedInsert`, `map_orderedInsert`, `List.Pairwise.insertionSort_eq` support size, order and representation bridges. |
| Mathlib `InformationTheory/Coding/PrefixFree.lean` | `IsPrefixFree`, `IsPrefixFree.isUniquelyDecodable` with exclusion of the empty word, and `isUniquelyDecodable_of_nontrivial`. Leaf-path representation and symbol injectivity must still be connected. |
| Mathlib `Coding/UniquelyDecodable.lean` | `IsUniquelyDecodable`, `epsilon_notMem`, `flatten_injective`; useful exact formalization of unambiguous concatenated codewords. |
| Mathlib `Coding/Kraft.lean`, `KraftMcMillan.lean` | Prefix-free and uniquely-decodable Kraft inequalities, including `IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`. Inequality alone is not the constructive finite prefix-code converse or a complete bridge from arbitrary uniquely decodable codes to the tree optimum. |
| Existing resource and queue modules | Measured erasure, occurrence queue histories and earlier priority-queue cost theorems can support execution analysis. `Huffman.cost` is the optimization objective, not algorithm running time; `LeftistQueue.rank_log` alone does not prove Huffman runtime. |

| Inspected file | SHA-256 |
|---|---|
| conaled `Applications/Huffman/Basic.lean` | `5e4d3c91809f9296470c23b30fce77348280468807d802030399c0d4cade250b` |
| conaled `Applications/Huffman/Exchange.lean` | `93b1d25d4cc4968be004298b1dcc330fdaae19b307fecad1a3ba74ab90a6f5d5` |
| conaled `Applications/Huffman/Priority.lean` | `c06cfbe28f488d5aed5ddc2cc2f8002244eb22818c875b3f752dfccc393048e1` |
| conaled `Applications/Search/ExactPriority.lean` | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| Mathlib `Coding/PrefixFree.lean` | `28186b2ec20bd34ab051bbbd51fb2fdf8a2e1116b9a8b3a1911804b500c8d478` |
| Mathlib `Coding/UniquelyDecodable.lean` | `c9d3758b1b79f2e201a246768dcf619fa3803804fa842cf068ccf9f48da897c0` |

### Cached carrier versus semantic tree

Source trees are `Leaf weight symbol` and `Node cachedWeight left right`.
Every internal node retains a cache. Existing `Bracketing.Tree α` has
unannotated forks, and Huffman queue entries cache only their current root.
An effective semantic erasure keeps leaf pairs:

```
Leaf w a       ↦ Bracketing.Tree.leaf (w,a)
Node cache l r ↦ Bracketing.Tree.fork (erase l) (erase r)
```

With leaf weight `Prod.fst`, computed source weight and cost match the
existing definitions on **all raw source trees**, irrespective of internal
cache accuracy. Source consistency is `Nodup` of the **symbol projection**
of the weighted fringe, not merely `Nodup` of `(weight,symbol)` pairs.
Under consistency, equal alphabets and frequency functions give a
permutation of weighted leaves, connecting source comparability to
conaled feasibility. Alphabet equality remains necessary for zero-weight
symbols.

Cache erasure is not injective. Recomputing all caches cannot establish
raw equality, including `huffman [t]=t` for a tree with inaccurate caches.
The source adapter needs to preserve that observation or restrict and
prove an explicitly canonical-cache correspondence. In particular,
`swapLeaves` deliberately leaves internal caches unchanged while moving
leaf weights. Its mathematical lemmas use independently computed weights
and costs and must **not** be restricted by an invented global
accurate-cache premise.

The formal `sortedByWeight` predicate orders **computed** weights. The
actual `insortTree` compares **cached** weights. These agree for initial
leaves and for correctly maintained algorithm states; they can disagree
on raw trees. The source's insertion-order lemma assumes all trees are
leaves. Generalized algorithm-state preservation needs a separate cache
accuracy invariant.

### Tie behavior and existing queue results

Source insertion puts a newly merged tree **before** existing equal-weight
entries. `List.orderedInsert (cachedWeight · ≤ cachedWeight ·)` matches
this exactly. Existing queues need separate observations:

- For input `[a:1,b:1,c:2]`, source returns `fork (fork a b) c`.
  Existing `exactList` appends the new entry and sorts for deletion, giving
  `fork c (fork a b)`. Both are optimal; their selected trees differ.
- Existing `exactLeftist` also need not preserve the source tie order.
  On five unit-weight leaves `[a,b,c,d,e]`, after two merges source
  prioritizes `[e,CD,AB]`, while leftist deletion gives `[e,AB,CD]`.
  Final shapes are `fork AB (fork e CD)` and
  `fork CD (fork e AB)`, respectively.
- `Huffman.SourcePriority.huffman_eq` relates the project's existing
  ADWH checkpoint233 leftist source. It does not identify that algorithm
  with this chapter's sorted-list source.

A lawful source-exact sorted-list queue can share the generic greedy
optimality proof, while a separate recurrence theorem preserves the
book's exact chosen tree, internal caches and tie choices. Cost equality
or existence of some optimum cannot replace this correspondence.

## Exhaustive coverage checklist

All source weights and frequencies are natural numbers, so zero weights
are allowed and every exchange/cost argument uses nonnegativity.
`A`, `freq`, `W`, `C`, `H`, and `cw` below denote alphabet, frequency,
computed weight, weighted path cost, height and cached root weight.
Forest versions actually used by the book are `A_F`, `consistent_F`,
`freq_F`, `H_F`, and `splitLeaf_F`.

### Binary codes and the tree interpretation

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-001 | Define a finite source alphabet, a symbol-to-bit-list code, nonempty codewords where the source coding convention requires them, and the admissibility needed for unambiguous decoding. | pp.305–306. An arbitrary map to nonempty lists need not be injective or uniquely decodable. Distinguish prefix-free, nonsingular and uniquely-decodable notions. |
| C26-002 | Encoding concatenates the codewords of a source string; its bit length is the sum over symbols of occurrence frequency times codeword length. | p.305 weighted encoding objective. Use finite sums/multisets and retain zero-frequency symbols in the code alphabet when required. |
| C26-003 | Define a leaf-path encoder: left edge emits0, right emits1, and a leaf at the root has the empty path. | p.306. On consistent trees, a symbol in the alphabet has one path; absent symbols should have explicit failure or a guarded query. |
| C26-004 | Leaf paths for distinct leaves are distinct and no one is a proper prefix of another; consistency connects leaves to unique source symbols. | p.306 prefix property. A prefix-free set alone does not establish injectivity of an arbitrary symbol map if duplicate codewords were discarded. |
| C26-005 | Nonempty leaf codewords plus prefix-freeness yield unique decoding of concatenated codeword sequences; provide encoder/decoder or an injectivity theorem. | p.306 ambiguity claim; Mathlib `IsPrefixFree.isUniquelyDecodable`, `flatten_injective` can discharge much after the carrier bridge. |
| C26-006 | Relate finite prefix-free codes to finite binary tries, and eliminate unary internal nodes without increasing weighted length. | p.306 justification for full binary trees. Elimination is strict only when the removed edge carries positive total weight; Nat weights can be zero. At least two symbols avoid the singleton/nonempty-codeword conflict. |
| C26-007 | Tree depth equals the corresponding leaf codeword length, and computed tree cost equals the encoding-length objective for consistent trees. | pp.306,310–311; combines C26-002/003 with the sum theorem below. |
| C26-008 | Transport optimum full-tree weighted path length to optimum among the stated finite prefix-code class. | pp.305–306,317. Requires C26-006's representation/compression argument, not only optimality among already full trees. |
| C26-009 | Retain the stronger unambiguous-code optimality claim with a precise uniquely-decodable-code interpretation and a proved bridge, e.g. finite Kraft–McMillan plus a prefix-code realization with no greater weighted length. | p.305 says no code unambiguously encoding symbols can beat the example; p.317 concludes optimum binary coding. This is not supplied by the companion's tree theorem. It does not request the whole theory of coding or every cited paper. |
| C26-010 | Check example `abacabad`, frequencies `(4,2,1,1)`, code `a↦0,b↦10,c↦110,d↦111`, exact encoded bits `01001100100111`, length14. | p.305; finite reconstruction regression and weighted-sum equality. |
| C26-011 | Prove that the example code's weighted cost14 is minimal in the stated admissible class, including the unambiguous-code interpretation of C26-009. | p.305 explicit optimality assertion; Huffman tree optimum plus a coding bridge can be reused. A mere evaluation of14 is insufficient. |
| C26-012 | The displayed fixed-length code gives16 bits; any injective fixed-length binary code for four symbols needs at least two bits per symbol. | pp.305–306 comparison. Pigeonhole/cardinality `4≤2^k` supplies the lower bound. |
| C26-013 | Preserve singleton tree behavior and explicitly correct the conflict with nonempty codewords: a root leaf has source cost0 and empty path, while a valid nonempty singleton code needs length at least1. | pp.305,310,317. State the ≥2-symbol tree-to-nonempty-code theorem, and/or a separately accounted singleton coding adapter; do not alter the source's leaf cost. |
| C26-014 | Empty alphabet/input has no nonempty tree result; expose the existing optional failure behavior or a nonempty-domain API. | pp.309,317 source precondition. Empty coding conventions can be stated separately; do not invent a payload inhabitant. |

### Source carrier and exact greedy implementation

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-015 | Preserve raw full binary trees `Leaf Nat α` and `Node Nat left right`, and list forests. | pp.308–309; source datatype lines264–266. Internal cached labels are observable even when inaccurate; use a narrowly justified source adapter if no existing annotated carrier matches. |
| C26-016 | `cw` returns the leaf weight or internal cached value in constant structural depth. | p.308; `cachedWeight`, lines780–782. It is distinct from recursively computed weight. |
| C26-017 | `uniteTrees l r = Node (cw l+cw r) l r`, preserving left/right order and reusing both subtrees. | p.308; lines808–809. Cache correctness is a later invariant, not built into the raw datatype. |
| C26-018 | `insortTree u []=[u]`; on a head `t`, insert before it if `cw u≤cw t`, otherwise retain that head and recurse. | p.309; lines836–839. New equal priorities precede old ones. Mathlib `orderedInsert` has the exact recurrence. |
| C26-019 | Insertion adds one occurrence and one list element; its output is nonempty and a permutation of `u::ts`. | p.309 and termination support; `length_insortTree`, `insortTree_ne_Nil`; library permutation law. Do not quotient equal-weight or equal-symbol occurrences away. |
| C26-020 | Exact Huffman base case on singleton `[t]` returns that same raw tree. | p.309; `huffman`, line886. Inaccurate internal caches must not be silently recomputed in this raw equation. |
| C26-021 | Exact recursive case takes the first two trees, unites them, inserts into the remaining sorted list, and recurs. | p.309; line887. The main operation is a tree-valued recurrence, not just an optimal-cost sequence. |
| C26-022 | Each productive step reduces forest length by exactly1; nonempty input stays nonempty, giving termination and exactly `n−1` merges. | p.309 procedure; use C26-019. Empty source case is underspecified and receives C26-014's adapter. |
| C26-023 | Reconstruct the displayed five-symbol execution for weights `z:2,d:3,f:5,s:7,e:11`. | pp.307–308. Merge weights are5,10,17,28; the exact final shape has `e` at depth1, `s` at2, `f` at3, `z,d` at4; weighted cost60. |
| C26-024 | Realize the source sorted-list priority queue with exact occurrence and minimum-deletion laws, then prove its transition/loop equality to the source recursion. | Existing `ExactQueue` and generic Huffman optimality engine. The adapter must preserve insertion ties and full cached-tree observations. |
| C26-025 | Define cache accuracy recursively and prove leaf initialization and `uniteTrees`/insertion/whole-run preservation. | pp.306,308 implementation interpretation. This supplies `cw t=W t` on actual states without restricting all raw surgery lemmas. |
| C26-026 | Distinguish source `sortedByWeight` on computed weights from insertion order on caches; prove their equality under cache accuracy and sortedness preservation for actual runs. | Source lines1729–1750. Its original insertion lemma assumes inserted/list trees all have height0. Raw consistency alone is insufficient. |
| C26-027 | State the initial invocation premises: nonempty forest, all elements leaves, unique/disjoint symbols, and nondecreasing computed leaf weights. | pp.306–309, Theorem26.7 p.317. Initial sorting is an explicit upstream task if arbitrary input is accepted. |

### Independent semantics and forest abstractions

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-028 | Alphabet of a leaf is its singleton symbol; alphabet of a node is the union. It is finite and nonempty for every tree. | pp.309–310; `alphabet`, `finite_alphabet`, `exists_in_alphabet`. Does not depend on weights or caches. |
| C26-029 | Forest alphabet is the union over its elements, with empty forest alphabet empty. | p.311; `alphabet_F`, lines314–316. |
| C26-030 | Tree consistency requires recursively consistent children with disjoint alphabets; equivalent to symbol-fringe `Nodup`. | pp.309–310; `consistent`, lines343–346. Repeated labels with different weights still violate it. |
| C26-031 | Forest consistency means each tree is consistent and all its symbols are disjoint from the rest of the forest; equivalent to `Nodup` of concatenated symbol fringes. | p.311; `consistent_F`, lines348–351. |
| C26-032 | Source `depth t a` is0 at a leaf and for absence; at a node it follows the left child if `a` occurs there, else right if present, adding1. | p.310; `depth`, lines434–439. On inconsistent trees it chooses a leftmost occurrence, unlike an occurrence-sum notion. |
| C26-033 | Tree height is0 at leaves and `max child heights+1`; forest height is the maximum with empty value0. | pp.310–311; `height`, `height_F`, lines458–464. Height0 forest iff all its trees are leaves. |
| C26-034 | Every symbol depth is at most height; a consistent tree has an alphabet symbol at maximum depth. | p.315–316 deepest-sibling proof support; `depth_le_height`, `exists_at_height`. Consistency is needed for the source's leftmost-symbol depth to witness every deepest occurrence. |
| C26-035 | Frequency sums all matching leaf weights; forest frequency sums tree frequencies. A symbol outside the alphabet has frequency0. | p.310; `freq`, `freq_F`, lines543–549, absence lemmas. The converse fails for zero-weight leaves. |
| C26-036 | Computed weight sums leaf weights, ignoring all internal caches. Under consistency it equals the sum of symbol frequencies over the alphabet. | p.311; `weight`, `weight_eq_Sum_freq`, lines600–602,619–622. A stronger raw-tree sum law may be separate; retain the source premise when reconstructing it. |
| C26-037 | Computed cost is0 at a leaf and `W l+C l+W r+C r` at a node, independently of caches. | p.311; `cost`, lines642–644. This is weighted path length, not algorithm execution work. |
| C26-038 | Under consistency, `C t = Σ(a∈A t), freq t a * depth t a`; a height0 tree has cost0. | p.311; `cost_eq_Sum_freq_mult_depth`, lines712–747, and `height_0_imp_cost_0`. Existing `pathCost_eq` gives substantial reuse after the symbol-occurrence bridge. |
| C26-039 | Source comparability is equal alphabets and equal entire frequency functions; define `optimum t` by cost domination of every consistent comparable competitor. | pp.310–311; `optimum`, lines764–767. The predicate itself does not assert `consistent t`; the output theorem proves consistency separately. |
| C26-040 | Erase internal caches while retaining `(leafWeight,symbol)` pairs, and prove raw computed weight/cost correspondence with existing conaled. | Reuse bridge described above. Do not erase leaf weights or identify two raw trees merely because their erasures agree. |
| C26-041 | For consistent source trees, comparable alphabets/frequencies iff weighted fringes are permutations, with the appropriate original-input fringe. | Connect C26-039 to conaled `Feasible`/`Optimal`. Zero-weight labels make alphabet equality essential. |
| C26-042 | Prove the source optimum theorem from the occurrence-based existing optimum through C26-030/041; retain consistency rather than treating the two definitions as unconditional aliases. | Existing `huffman_optimal`, `greedy_exchange`. Duplicate-symbol counterexample below shows the boundary is substantive. |
| C26-043 | `uniteTrees` unions alphabets, adds frequencies, and preserves consistency when child alphabets are disjoint. | pp.308–311 proof support; `alphabet_uniteTrees`, `consistent_uniteTrees`, `freq_uniteTrees`, lines816–827. |
| C26-044 | Insertion unions forest alphabet, adds frequencies, preserves the equivalent head-plus-tail consistency predicate, and takes maximum forest height. | Formal support for p.314 and induction; `alphabet_F_insortTree`, `consistent_F_insortTree`, `freq_F_insortTree`, `height_F_insortTree`, lines860–874. |
| C26-045 | Nonempty Huffman output alphabet equals the input forest alphabet. | First displayed preservation formula p.314; `alphabet_huffman`, lines903–905. No sortedness, cache accuracy or leaf-only premise. |
| C26-046 | Consistent nonempty input forest gives a consistent Huffman output. | Second preservation formula p.314; `consistent_huffman`, lines907–909. No sortedness/cache assumption. |
| C26-047 | Nonempty Huffman output frequency function equals input forest frequency. | Third preservation formula p.314; `freq_huffman`, lines911–913. Preserve all symbols, including zero weights. |

### Exact swap, sibling, merge and split functions

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-048 | `swapLeaves` replaces a leaf labeled `a` by `(w_b,b)`, else a leaf labeled `b` by `(w_a,a)`, else leaves it unchanged; recurse through nodes without altering their cached labels. | p.312; source lines1106–1110. The ordered tests matter when `a=b`. Do not recalculate caches during this operation. |
| C26-049 | `swapSyms t a b` calls `swapLeaves` using original frequencies of `a,b`. | p.312; `swapSyms`, lines1414–1415. On a consistent tree with both symbols, this moves weighted labeled leaves to the exchanged positions. |
| C26-050 | Recover swap identity/absence, alphabet, consistency, height, unaffected-depth and frequency laws with their exact occurrence/membership premises. | pp.312–316 proof support; `swapLeaves_id*`, `alphabet_swapLeaves`, `consistent_swapLeaves`, `height_swapLeaves`, `freq_swapLeaves`; `swapSyms_id`, `alphabet_swapSyms`, `freq_swapSyms`. Cache accuracy is not a premise. |
| C26-051 | Exact source swap-cost balance: `C(swapped)+f(a)d(a)+f(b)d(b) = C(t)+f(a)d(b)+f(b)d(a)` for consistent `t` containing `a,b`. | Supporting identity for Lemma26.1; `cost_swapSyms`, lines1439–1448. Includes the equal-symbol case separately; existing `swap_cost_balance` can transport through C26-040/041. |
| C26-052 | **Lemma26.1:** if additionally `freq a≤freq b` and `depth a≤depth b`, exchanging the two does not increase cost. | p.312; `cost_swapSyms_le`, lines1456–1470. Direction pushes the less frequent symbol deeper and the more frequent one shallower. |
| C26-053 | Preserve the three `swapFourSyms` branches: `a=d` swaps `b,c`; else `b=c` swaps `a,d`; else perform swaps `a,c` then `b,d`. | p.312; lines1510–1514. This handles aliasing; a naive fixed pair of swaps is not equivalent. |
| C26-054 | Four-way swaps preserve consistency and, with all specified symbols present, alphabet/frequency; when `c,d` are distinct siblings and `a≠b`, the result makes `a,b` siblings. | pp.312,315–316; `alphabet/consistent/freq_swapFourSyms`, `sibling_swapFourSyms_when_4th_is_sibling`, lines1521–1564. The target sibling pair is not necessarily assigned the same left/right orientation in alias cases. |
| C26-055 | Define omitted `sibling`: at a leaf return the query; at two leaf children return the other label when a child matches; otherwise search left alphabet first, then right, else return the query. | p.313; exact source lines931–938. Retain absent/non-leaf-sibling and inconsistent-tree behavior. |
| C26-056 | On consistent trees, `sibling t a≠a` iff the occurrence of `a` has a sibling leaf; the sibling is present, sibling is reciprocal/involutive, and its depth is equal. | p.313 property and deepest-pair proof; `sibling_sibling_id`, `sibling_reciprocal`, `depth_sibling`, membership lemmas. |
| C26-057 | In a positive-height consistent tree, a symbol at maximum depth has a distinct sibling leaf at that same depth. | pp.315–316; `depth_height_imp_sibling_ne`, `exists_at_height`. Existing `DeepSiblings` and `deepSiblings_depth` are useful but need the source symbol-depth bridge. |
| C26-058 | Exact `mergeSibling`: leave a leaf unchanged; replace a two-leaf node containing the queried label by a single leaf labeled by that query with summed leaf weights; otherwise recurse through children preserving other node caches. | p.313; source lines1581–1587. This is a label-directed raw transformation, not merely contracting an already located deepest pair. |
| C26-059 | Merge is identity when the symbol is absent; preserves consistency and total computed weight; for a genuine sibling, removes its label and adds its frequency to the queried label. | p.313 meaning; `notin_alphabet_imp_mergeSibling_id`, `alphabet_mergeSibling`, `consistent_mergeSibling`, `freq_mergeSibling`, `weight_mergeSibling`, lines1603–1644. Exact formulas require consistency and the stated membership/sibling premises. |
| C26-060 | **Lemma26.2:** `consistent t ∧ sibling t a≠a` implies `C(mergeSibling t a)+freq t a+freq t(sibling t a)=C t`. | p.313; `cost_mergeSibling`, lines1651–1654. Existing `contract_deep` proves a related located contraction; prove exact source-operation correspondence where used. |
| C26-061 | Exact `splitLeaf`: replace every leaf labeled `a` by `Node oldLeafWeight (Leaf w_a a) (Leaf w_b b)` and recurse through nodes preserving their cache values. | p.314; source lines1672–1676. Root cache is the **old** leaf weight, not unconditionally `w_a+w_b`. |
| C26-062 | `splitLeaf_F` maps the exact tree function over the forest, preserving order and forest length. | p.316 forest operation; source lines1678–1681. Reuse list map where exact. |
| C26-063 | Splitting is identity if `a` is absent; alphabet gains `b` iff `a` is present; consistency is preserved when original tree is consistent and `b` is absent. | p.314 intended transformation; source lines1688–1703. Without freshness, duplicated `b` may appear. |
| C26-064 | With consistency and fresh `b`, splitting changes frequencies to `w_a` at `a`, `w_b` at `b`, and leaves others unchanged when `a` was present. | p.314; `freq_splitLeaf`, lines1705–1710. Distinguish absence from zero frequency. |
| C26-065 | With consistency, `a∈A t` and `freq t a=w_a+w_b`, splitting preserves computed total weight. | p.314 context; `weight_splitLeaf`, lines1712–1715. Freshness of `b` is not required for this weight identity. |
| C26-066 | **Lemma26.3:** under the same premises, `C(splitLeaf t w_a a w_b b)=C t+w_a+w_b`. | p.314; `cost_splitLeaf`, lines1717–1720. In particular, do not add an unnecessary `b∉A t` premise to this theorem. |
| C26-067 | `cw(splitLeaf t ...)=cw t` unconditionally, including inaccurate raw caches and arbitrary new weights. | Needed for Lemma26.6; `cachedWeight_splitLeaf`, lines2052–2054. This is a cache observation, separate from C26-065's computed-weight equality. |
| C26-068 | Clarify “undoes merging”: under sibling/frequency/freshness conditions, split recovers the relevant alphabet/frequency/cost relationship; exact original raw-tree equality requires orientation/cache conditions. | pp.313–314. Source merge can collapse a right-labeled queried child and split always places `a` on the left, so a blanket raw inverse equation is false. Retain a small orientation counterexample if claiming an inverse adapter. |
| C26-069 | Preserve `minima t a b`: both labels occur, differ, and each frequency is no larger than every **other** symbol's frequency. | p.314; source lines1760–1764. The definition is symmetric and contains no `freq a≤freq b` conjunct. |
| C26-070 | Bridge symmetric source minima to conaled's ordered `TwoLeast` by an orientation case split, keeping tied cases and all other-symbol bounds. | Existing `TwoLeast` explicitly orders the selected pair. Do not strengthen the source definition unnoticed; see the counterexample below. |

### Greedy exchange, commutation and the global theorem

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-071 | **Lemma26.4:** consistent `t`, source minima `a,b`, distinct present `c,d` at maximum depth imply `C(swapFourSyms t a b c d)≤C t`. | p.315; `cost_swapFourSyms_le`, lines1805–1836. No sibling assumption on `c,d` is needed for this inequality alone. |
| C26-072 | Account for all alias cases `a=c`, `a=d`, `b=c`, `b=d` and their effect on the two source swaps. | p.315 proof; source theorem proof. Existing exchange witness may choose another equivalent tree, so exact source-function result still needs a bridge. |
| C26-073 | For any consistent comparable competitor to a split tree with two present distinct symbols, obtain a deepest sibling pair in that competitor. | Lemma26.5 proof pp.315–316; source uses `exists_at_height`, sibling facts, and equality of alphabets to prove positive height. |
| C26-074 | Four-way swapping the selected minimum symbols into that sibling pair preserves competitor alphabet/frequencies/consistency and does not increase cost. | pp.315–316; source proof combines C26-054/057/071. |
| C26-075 | Merging the swapped minimum siblings gives a consistent competitor comparable with the unsplit original tree. | p.316; equality of alphabets and full frequency functions is essential, not merely total weight. |
| C26-076 | **Lemma26.5:** if `t` is consistent/optimum, `a∈A t`, `b∉A t`, `freq t a=w_a+w_b`, and every old symbol has frequency at least both `w_a,w_b`, then the split tree is optimum. | p.315; `optimum_splitLeaf`, lines1936–1999. Nat weights may be zero; no ordering between `w_a,w_b` is required. |
| C26-077 | Preserve the exact cost inequality chain: split cost equals `C t+w_a+w_b`, optimality compares with the merged competitor, merge identity restores swapped cost, and exchange bounds it by the original competitor. | p.316. Correct the printed swapped argument order in its first `splitLeaf` expression. Existing `forest_greedy_refinement` can share the mathematics, but source statements still need reconstruction witnesses. |
| C26-078 | Prove split commutes with cached comparisons, `uniteTrees`, and ordered insertion under the relevant map/forest hypotheses. | Lemma26.6 support; source `splitLeaf_F_insortTree_when_*`, lines2056–2076. `map_orderedInsert` plus C26-067 is a direct general route. |
| C26-079 | **Lemma26.6:** consistent nonempty forest containing `a` with `freq_F a=w_a+w_b` satisfies `splitLeaf (huffman ts) ... = huffman (splitLeaf_F ts ...)`. | p.316; `splitLeaf_huffman_commute`, lines2082–2110. This is exact cached-tree equality including ties, not cost or optimality equality. Source omits explicit nonempty premise because membership implies it. |
| C26-080 | Raw split/unite/ordered-insert homomorphisms may yield a stronger all-nonempty-forest commutation theorem, from which the printed result follows; any strengthening must preserve all raw caches. | Reuse opportunity, not already checked evidence. C26-067 shows why no global cache accuracy is needed; do not silently narrow the printed result to accurate-cache states. |
| C26-081 | In the optimality induction, flatten the first merged leaf pair into one summed-weight leaf, keeping a shorter consistent leaf-only sorted forest. | pp.316–317. Initial leaf sortedness and insertion of the summed leaf must be proved; source `sortedByWeight_insortTree` covers the leaf-only case. |
| C26-082 | Use induction to obtain optimum for the flattened smaller forest; prove its selected `a` frequency is the original pair sum and each other remaining frequency is at least both original minima. | p.317 and source `optimum_huffman` proof. These are the premises of Lemma26.5, not consequences of total-weight preservation alone. |
| C26-083 | **Theorem26.7:** nonempty, consistent, height0, sorted-by-computed-weight input forest yields `optimum (huffman ts)`. | p.317; `optimum_huffman`, lines2130 onward. All four premises retained. Existing global queue proof can discharge the same source theorem once exact queue/feasibility/cache bridges are proved. |
| C26-084 | Combine optimum with alphabet, consistency, frequency and accurate-cache output properties for the actual sorted-leaf invocation. | p.317 concluding correctness claim. An optimum predicate alone does not state that the desired symbols/frequencies survived. |
| C26-085 | Extend an arbitrary-order public input adapter by a checked sorting permutation while preserving source input convention and chosen equal-weight tie order. | p.306 requires sorting before invocation; Chapter2 supplies sorting. If exact raw output is not preserved by a different initial tie order, identify that adapter as an equivalent optimum variant. |
| C26-086 | Connect the resulting consistent tree to prefix-code and uniquely-decodable optimum statements with the alphabet-size/nonempty-codeword conditions above. | pp.305–306,317. Existing conaled documentation leaves coding out of its present Huffman scope, so this remains substantive new work. |

### Execution complexity and the two faster variants

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C26-087 | Define an exact measured source recurrence for insertion comparisons/visited list cells and whole Huffman execution; prove value erasure. | p.318 quadratic claim. Distinguish weighted path cost, comparison work, allocations and copied list prefix cells. The book gives no explicit tariff constants. |
| C26-088 | Inserting into a remaining list of length `k−2` uses at most `k−2` cached-weight comparisons; nonempty forest shrinks through sizes `n,n−1,...,1`. | C26-018/022; derive total comparison upper bound `(n−1)(n−2)/2`, with Nat boundary cases0/1 and additional `O(n)` merge overhead. |
| C26-089 | Prove a quadratic lower family for the literal sorted-list implementation, e.g. `n=2r` distinct symbols all of weight1. The first `r` merges already use `r²−1` insertion comparisons. | p.318 “quadratic” assertion interpreted as worst-case `Θ(n²)`. Source tie rule matters: each new weight2 scans remaining weight1 leaves and, except for the first merge, compares with an old weight2. |
| C26-090 | State the runtime domain: unit-cost cached access, comparisons/addition on weights and indices, constructor/list operations; weights of unbounded bit length need a separate arithmetic model. | p.318. Every run need not be quadratic, e.g. all-zero priorities insert at the head. Initial sorting is separate unless explicitly included. |
| C26-091 | Preserve the claimed `O(n log n)` alternative by a specified efficient ordered priority data structure or a comparison-only insertion model, with a checked greedy refinement and measured costs. | p.318 binary-search sentence. Binary search on an ordinary contiguous array only finds the position; shifting entries remains linear. A balanced search-tree/heap implementation can establish the intended overall bound with the actual PartIII laws. |
| C26-092 | Retain a counterexample/cost model showing that binary-search position discovery alone does not establish logarithmic update time for a sorted array/list. | p.318 source-description correction. On a sorted array, insertion before an existing equal-weight block moves that block under the usual contiguous-storage model; across Huffman steps this can still be quadratic. Linked lists do not offer constant-time middle access for binary search. |
| C26-093 | Implement the stated two-queue variant: one queue of already sorted unprocessed leaves, one of produced combined trees; choose each next minimum from their heads and enqueue the new combined tree. | p.318 externally cited mathematical algorithm claim. This is retained as an executable variant, not waived because only a sentence describes it. |
| C26-094 | Prove generated combined weights are nondecreasing, using nonnegative weights and two-minimum extraction, so the second queue remains ordered. | Necessary mathematical property behind the p.318 linear claim. State tie choices; ordinary FIFO generated trees need not reproduce source `≤` insertion's new-before-old ties. |
| C26-095 | Prove the two-queue variant's exact occurrence/cached-weight/greedy invariants and global optimality through the shared Huffman interface. | p.318. If its chosen tree differs on ties, label it a correct optimum variant rather than asserting raw equality to C26-021. |
| C26-096 | Prove `O(n)` total two-queue processing from `O(n)` initialization, `n−1` merges, a constant number of queue operations per merge, and appropriate worst-case or amortized queue costs on one sequential history. | p.318. The initial leaves must already be sorted; obtaining arbitrary input order is not hidden in this bound. Reuse Chapter20 queues and Chapter19 history accounting where suitable. |
| C26-097 | If the `O(n log n)` variant starts from unsorted input, account for its initialization/sorting or bulk-build cost and prove exact input-occurrence preservation. | p.318 versus pp.306–309 input convention. A named asymptotic count must say whether sorting is included. |
| C26-098 | Preserve the source's “merged subtrees are never revisited” claim as a property of actual Huffman construction: only root caches are inspected after a subtree is formed. | p.316 motivation for commutation. Mathematical proof functions like `weight`, `depth`, swaps and splitting are not executed by the Huffman runner. |
| C26-099 | Checked examples cover empty/singleton APIs, zero weights, duplicate-label rejection or explicit occurrence semantics, equal-priority tie shapes, stale-cache raw transformations and the displayed cost60 execution. | Whole chapter reconstruction and existing API compatibility. Do not silently change current conaled support for repeated occurrences. |
| C26-100 | Keep proof-style comparisons and the Huffman-algebra question as identified discussion, not extra mathematical coverage claims; retain all actually stated runtime/coding claims above. | Chapter Notes p.318. No whole-paper expansion and no unproved axiom replacing source mathematics. |

## Source discrepancies, counterexamples and required dispositions

1. **Nonempty codewords versus singleton trees.** The coding definition
   on p.305 excludes the empty bit sequence, but p.310 assigns a root
   leaf depth0 and the optimality proof on p.317 explicitly uses its
   cost0. For a singleton symbol of weight `w>0`, every nonempty code
   has cost at least `w`; assigning the empty word is not uniquely
   decodable because one and two copies both encode as `[]`. Preserve
   the tree theorem and state the ≥2-symbol coding bridge. A separate
   singleton encoder using `[0]` is valid, but has an explicitly different
   coding-cost convention. Do not alter the raw tree algorithm to hide
   this mismatch.

2. **Tree representation of codes.** A leaf-labeled tree represents a
   prefix-free code, not every arbitrary nonempty bit-list map. Even
   uniquely decodable codes can fail prefix-freeness; for example,
   `{0,01}` is uniquely decodable but one word prefixes the other.
   If formalizing the broader optimum claim, use a proved comparison
   bridge such as finite Kraft–McMillan and prefix-code realization,
   rather than claiming literal tree representation of every code.
   Full-tree optimality alone does not prove that bridge.

3. **The ordering omitted from `minima`, p.314.** Take distinct `a,b`
   and `t=Node 3 (Leaf 2 a) (Leaf 1 b)`. The displayed predicate holds
   for `(a,b)` because there are no other symbols, but `freq t a≤freq t b`
   is false. The actual definition and all seven numbered mathematical
   results work with a symmetric pair of minima. Correct the prose,
   retain the counterexample, and orient the pair only when adapting to
   existing `TwoLeast`.

4. **Cache order is not computed-weight order.** Let
   `u=Node 100 (Leaf 1 a) (Leaf 1 b)` and
   `v=Node 0 (Leaf 1 c) (Leaf 2 d)`, with distinct symbols.
   Computed weights are2 and3. Inserting `u` into `[v]` compares100
   with0 and yields `[v,u]`, which is not sorted by computed weight.
   The source `sortedByWeight_insortTree` correctly limits its theorem
   to leaves. Use a separate cache invariant for generalized actual
   algorithm states; consistency alone cannot repair this discrepancy.

5. **Swaps retain stale internal caches.** Moving unequal-weight leaves
   between subtrees can change those subtrees' actual weights while
   keeping their stored labels. This is intentional in `swapLeaves`.
   The source cost/weight definitions ignore caches, so surgery and
   exchange theorems remain valid. A bridge through a type requiring
   cache accuracy everywhere would exclude legitimate source proof
   states and lose Lemmas26.1/26.4's original scope.

6. **“Undoes” does not mean a raw two-sided inverse, pp.313–314.** Let
   `t=Node 3 (Leaf 1 b) (Leaf 2 a)`, with `a≠b`. Merging at `a`
   produces `Leaf 3 a`; splitting with `w_a=2,w_b=1` produces
   `Node 3 (Leaf 2 a) (Leaf 1 b)`, reversing the original child order.
   An inaccurate original parent cache could also be lost at merge.
   The needed source mathematics concerns alphabet/frequency and exact
   cost changes, not an unrestricted raw inverse. State any exact
   inverse theorem with orientation/cache premises.

7. **Argument order in the proof chain, p.316.** The first displayed
   cost equality writes `splitLeaf t a w_a b w_b`, while the declared
   type and Lemma26.3 use `splitLeaf t w_a a w_b b`. Restore the typed
   order; the formal companion's theorem/proof use the latter.

8. **Binary search and insertion cost, p.318.** Binary search reduces
   comparisons used to locate an insertion point. It does not by itself
   reduce movement in a contiguous sorted array, nor make indexed access
   constant-time in a linked list. To retain the intended `O(n log n)`
   implementation claim, identify a data structure with a proved
   logarithmic full update, or explicitly state a comparison-only model.
   A balanced priority queue is a valid algorithmic refinement, with
   its own tie correspondence and queue-operation costs.

9. **Sorted input and worst-case qualifiers, p.318.** The two-queue
   `O(n)` claim assumes the leaf queue is already sorted. The source
   list algorithm's quadratic bound is a worst-case claim, not the cost
   of every input. All-zero weights insert at the front; unit weights
   on distinct symbols give the quadratic witness retained below.

10. **Occurrence optimum is not source optimum without consistency.**
    A tree with two leaves `(1,a),(1,a)` is a valid occurrence-optimal
    tree of cost2 for that two-occurrence list in existing conaled.
    Source comparability also permits the consistent singleton
    `Leaf 2 a`, of cost0, with the same alphabet/frequency. Thus this
    duplicate-label tree is not source-optimum. Keep existing repeated-
    occurrence APIs and prove the source theorem on its distinct-symbol
    domain; do not change conaled's semantics to force an alias.

The finite source execution, stale-cache insertion example and initial
quadratic-witness counts were independently evaluated in a small Python
transcription during inventory. The queue tie examples are also
read-only source checks. They are not Lean proofs or acceptance evidence;
meaningful counterexamples should become checked statements alongside
the corrected source-facing interfaces.

## Cost witnesses and priority-queue variants

For a forest of size `k≥2`, the source inserts into a list of size `k−2`.
Counting one comparison at each nonempty inspected list cell gives the
simple total upper bound

```
sum_{k=2..n} (k−2) = (n−1)(n−2)/2.
```

There are also `n−1` constant-structural-size root constructions and
weight additions under the unit-cost model. Failed insertion tests copy
the inspected prefix; insertion can reuse the untouched suffix. State
which of these are counted before claiming an exact constant.

For `n=2r≥2` initially distinct unit-weight leaves, consider the first
`r` merges. At merge `k` there are `2r−2k` unprocessed unit-weight
leaves. The new weight2 tree passes all of them; for `k≥2` it additionally
compares with the first old weight2 tree and inserts before it. Thus these
merges alone cost

```
sum_{k=1..r} (2r−2k + if k≥2 then 1 else 0) = r²−1.
```

Together with the upper bound, this supplies a precise route to the
book's worst-case quadratic claim. Both formulas remain future Lean
obligations connected to the actual measured recurrence.

For the two-queue variant, nonnegative priorities imply that newly
combined root weights are generated in nondecreasing order. Once that
fact and the exact-occurrence interface are proved, the existing greedy
forest-optimality proof can be shared. Ordinary FIFO handling of equal
generated priorities can select another optimum shape from the source's
new-before-old insertion; state that variant relationship explicitly.
The linear total queue-work bound needs only one sequential update
history, plus already sorted leaves. It must not include an unaccounted
sort or allow arbitrary persistent queue histories to reuse amortized
potential without accounting.

## Completion boundary

Acceptance requires source-function correspondence and all seven named
results, not just reuse of an existing Huffman theorem. The raw cached
carrier, symbol-consistency/feasibility bridge, exact tie behavior,
label-directed surgery, forest commutation, coding interpretation,
probative source corrections and three runtime variants all need
explicit witnesses. Existing conaled's stronger occurrence-optimality
framework should be reused where its hypotheses match and retained for
its present clients. This source inventory changes none of the project
validation or independent-review gates.

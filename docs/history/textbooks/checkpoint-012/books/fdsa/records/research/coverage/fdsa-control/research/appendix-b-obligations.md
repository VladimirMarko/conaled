# Appendix B: Time Functions — recurrence and reuse inventory

Prepared 2026-11-02. **Cross-cutting source inventory only.** This note covers
every displayed declaration, recurrence and simple property in printed
pp. 347–354. It does not activate later chapters, accept an appendix, modify
Lean source, or report a build. The sixty IDs below are coverage handles;
several are witnessed by existing declarations and need no new public alias.

## Evidence, source support and pins

The book is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026:
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
PDF SHA-256:
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
All eight appendix pages were text-extracted and visually inspected. Appendix B
has no exercises or separate asymptotic theorem. Its eleven displayed simple
properties are in B.1–B.2; other chapters own their further bounds.

The inspected conaled baseline is
`1aabd512284fe86254278ac631eda061d311050b`, with Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Lean 4.35.0
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. FDSA-X002 insertion-sort candidate
`697bcf242ce65d74815b5639bddb1c6e754dd10f` is separately identified below: it
has focused build evidence but still awaits its full gates and prerequisite
acceptance. Nothing here treats that candidate as integrated coverage.

Isabelle support uses shared mirror commit
`f86f290225eebcc52c1ae7dba2e098f405f51c21`:
<https://github.com/isabelle-prover/mirror-isabelle/tree/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL>.
`Time_Functions.thy` is under `Library/`; the other files in this table are
under `Data_Structures/`. The source pin postdates the book; it is a reproducible
support snapshot, not an assertion about the manuscript's build revision.

| Support file | SHA-256 | Exact support inspected |
|---|---|---|
| `Time_Functions.thy` | `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01` | `T_append`, `T_length`, `T_map_simps`, `T_map`, `T_filter_simps`, `T_filter`, `T_nth`, `T_take`, `T_drop`, `T_itrev`. |
| `Selection.thy` | `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8` | `partition3_code`, its selected `time_fun`, `T_partition3`, `T_slow_select_le`, `T_slow_median_le`, `T_chop_le`. |
| `Tree23_of_List.thy` | `dcb3ef5eff58d65a4bb95b915870dd527d0bb9dcffd13c9c41e9fb5421ba7240` | Alternating forest carrier, `not_T`, `join_adj`, `join_all`, `leaves`, `tree23_of_list`, and generated costs. |
| `Array_Braun.thy` | `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f` | `nodes` and exact `T_nodes = length xs + 1`. |
| `Leftist_Heap.thy` | `894e22da05b2dbf37ce46b8401958957e5d4a729c691d6a402b0e66dd8a22450` | Rank-cached merge, insertion, deletion and generated costs. This file does **not** include the book's list-construction subsection. |
| `Binomial_Heap.thy` | `821d4236fb294b3b73b9c119a40f36225d3f16d4030b805c045da39dcf63210a` | Actual binomial tree/forest algorithms and their generated costs; nonempty minimum premises. |
| `Queue_2Lists.thy` | `cd2b22bce8aafcc93ec19ca5d18a8ff9dd83f533cfd231fe3642cf08274149c2` | `norm`, `enq`, `deq`, observation `list`, invariant `invar`, and generated costs. |

AFP support is pinned by dated archives, not mutable browser pages. Each URL is
`https://isa-afp.org/release/afp-ENTRY-2026-10-26.tar.gz` with ENTRY from the first
column. The exact archive digests are:

| AFP entry | Archive SHA-256 |
|---|---|
| `Amortized_Complexity` | `d853a2fbf5644b5515847398dda6f9b65b203532ae608ad99d28b8f7a571442a` |
| `Priority_Queue_Braun` | `e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b` |
| `Splay_Tree` | `4c9b4a9fd24a63ba40eb5a357e2d8469d32eb437173018213bff2232f6dfd2f6` |
| `Skew_Heap` | `0aa18ccafebd4767acc96ab29d3b653faaaf437fdfa7912f49fa9e29ed3f0437` |
| `Pairing_Heap` | `fe2985e0b299455da334b51ef37c780e392f551dc47ea5f9a14bfbd53c1a3653` |

| Extracted supporting theory | SHA-256 |
|---|---|
| `Priority_Queue_Braun.thy` | `2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e` |
| `Splay_Tree.thy` | `1f922b404850d90b4fee6345577c945e297948dde7efe03e58886ed3df24beab` |
| `Splay_Tree_Analysis_Base.thy` | `3f8cc3fd475bf40bed0eff7f2442370eb326e140c90e66600fea220fc22cfe17` |
| `Splay_Tree_Analysis.thy` | `fd6ac8ae8b48e18e4dc8622e49f527ea7ce7fa8fa557f2af4231fd90e268f012` |
| `Skew_Heap.thy` | `212435f75ba99eb103c274cae4909ee4ac272add055ac3ffd1665eda7ea3a114` |
| `Skew_Heap_Analysis.thy` | `e1b224bf9d210bd3c8cd78508adab3444515b60d4162a903436d4add45f24b7b` |
| `Pairing_Heap_List2.thy` | `cea84ce48af8653082f68ac84fd763fdfabea981952d292819c84b88f8ba4b76` |
| `Pairing_Heap_List2_Analysis.thy` | `edf22de9e51028eac4a7936a12b06903c9b1b7fce101e9342da596f9b3aa70db` |

The five official `https://isa-afp.org/entries/ENTRY.html` pages were checked:
each identifies the BSD license. `book-source/AFP-LICENSE` supplies the
BSD-3-Clause terms. Isabelle's pinned COPYRIGHT also supplies BSD-3-Clause
terms. Retain required notices for any later adapted source; Lean/Mathlib
sources have their own Apache-2.0 notices. Downloaded sources, full text extracts
and page renders remain research inputs outside checkpoint deliverables; this
original inventory and its pins are the durable artifact.

## Interpretation and notation

`E` means the empty binary tree and `N l a r` its node constructor. These are
normalizations for this note, not proposed new Lean notation. Binomial
`Node rank value children`, 2-3 trees and pairing `Hp value children` are
different carriers despite sharing some printed words. `n` in a list bound is
`xs.length`. A displayed later catch-all clause applies only after the earlier
patterns have failed. All costs below have result type `Nat` except B-054–055,
which deliberately use `Int`.

| ID | Cross-cutting statement | Existing route and obligation |
|---|---|---|
| B-001 | Source helpers with cost identically zero are already eliminated. Charges follow each displayed recurrence, not a blanket one-charge-per-named-wrapper convention. | `Resources.Measured`, `bind`, `CallCount.tick`, `primitive_rule`, `let_rule`, `if_rule`, `case_rule` express the needed semantics. Prove value erasure and costs separately; `same_value_different_cost` already records why the former does not imply the latter. B.5's construction is a further selective merge-work model. |

## B.1 Lists: seven recurrences and seven exact properties

No relation, element equality, inhabitance or order assumption is needed here.
Map/filter callbacks carry nonnegative natural costs. The sum counts **list
occurrences**, so equal elements appearing twice contribute twice.

| ID | Source declaration/equation or property | Exact current reuse or missing work |
|---|---|---|
| B-002 | `Tappend : List α → List α → Nat`: empty left input costs 1; cons costs the tail append plus 1. | `Resources.ListReversal.appendRun_nil`, `appendRun_cons`, with `appendRun_exact` for the joint result. Chapter 1 candidate, not a cost claim about Lean's compiled `++`. |
| B-003 | `Tappend xs ys = n+1`. | Cost projection of `appendRun_exact`; independent of the right input and head values. |
| B-004 | `Tlength : List α → Nat`: empty costs 1; cons costs the tail plus 1. | `Resources.SymmetricCosts.lengthRun` has precisely these branches, returning length and cost together. |
| B-005 | `Tlength xs = n+1`. | `SymmetricCosts.lengthRun_exact`. |
| B-006 | `Tmap : (α → Nat) → List α → Nat`: empty costs 1; cons costs callback on head plus tail map plus 1. | A measured callback map and erasure to `List.map` remain useful shared work. Existing `Resources.Knapsack.sourceMapRun` charges **2**, not 1, per cons and is not exact reuse for this tariff. |
| B-007 | `Tmap Tf xs = (xs.map Tf).sum+n+1`. | Prove from B-006 using `List.map_nil/cons` and `List.sum_nil/cons`; retain duplicates. No callback constancy hypothesis. Isabelle support is `T_map`. |
| B-008 | `Tfilter : (α → Nat) → List α → Nat`: empty costs 1; cons costs predicate evaluation plus tail filter plus 1. | A measured Boolean predicate filter needs value erasure to `List.filter`. Both keep and discard branches pay the same recursive charge; no short-circuit traversal. |
| B-009 | `Tfilter TP xs = (xs.map TP).sum+n+1`. | Same arithmetic shape as B-007, separately connected to filter execution. Isabelle `T_filter_eq_T_map` is support for equality of these costs; it does not identify the output algorithms. |
| B-010 | `Ttake : Nat → List α → Nat`: empty input costs 1; on cons, zero count costs 1 and successor count costs recursive tail take plus 1. | The first-value projection of `SymmetricCosts.splitRun` has the correct value and count. Prove the displayed take recurrences as a checked adapter; `splitRun_value` already identifies the projection with `List.take`. |
| B-011 | `Ttake k xs = min k n+1`. | `SymmetricCosts.splitRun_work` after B-010's correspondence. Includes zero, empty and overlarge counts. |
| B-012 | `Tdrop : Nat → List α → Nat`: empty input costs 1; on cons, zero count costs 1 and successor count costs recursive tail drop plus 1. | The second-value projection of `splitRun`, with its own displayed recurrence correspondence and `splitRun_value`, supplies exact reuse. |
| B-013 | `Tdrop k xs = min k n+1`. | `splitRun_work` after B-012. Paying for a separate take and drop means adding both counts, even though their values can be computed by one fused split. |
| B-014 | `Tnth : List α → Nat → Nat`: on cons, index zero costs 1; successor index costs the tail lookup plus 1. No empty-input equation is displayed. | A measured list lookup on the valid domain, or an optional extension with its invalid behavior explicitly separated, is still needed. Standard `getElem?` and proof-domain `getElem` provide value semantics only. Random-access tree lookup is a different execution. |
| B-015 | `k<n → Tnth xs k = k+1`. | Prove on the bounds domain; `List.getElem?_eq_getElem` gives the optional/proof-domain value bridge. No source cost is claimed for out-of-range calls. |

The original source has `T_length` as an abbreviation for a typeclass timing
instance; there is no need to reproduce that Isabelle mechanism. The existing
measured length already gives the actual value/count relationship.

## B.2 Selection: four recurrences and four bounds

These are Chapter 3 helpers. Sorting costs refer to the ordinary insertion
algorithm and its exact tie direction. Zero-based `k` here must be bridged to
the existing public one-based Selection API, not used to change that API.

| ID | Source declaration/equation or property | Exact current reuse or missing work |
|---|---|---|
| B-016 | `Tchop : Nat → List α → Nat`: chunk size zero or empty input costs 1; otherwise pay `Ttake d xs + Tdrop d xs + Tchop d (drop d xs)+1`. | A source-faithful chunk execution/recurrence remains needed. The recursive clause has `d>0` and nonempty input. B-010–013 supply its separately charged traversals; prove strict decrease of the dropped suffix. |
| B-017 | `Tchop d xs ≤ 5n+1`, for every `d`, including zero. | Isabelle `T_chop_le`; combine the exact recurrence with `List.length_drop`/natural arithmetic. Do not accidentally impose a positive-size precondition on this total bound. |
| B-018 | `Tpartition3 : α → List α → Nat`: empty costs 1; each cons adds 1 to the tail count. | Corresponds to Isabelle's one-pass `partition3_code`, explicitly selected for `time_fun`. Existing conaled Selection partition observations/permutation are useful, but its decomposition into standard partitions/filters does not prove this execution count. |
| B-019 | `Tpartition3 pivot xs = n+1`. | The recurrence is order-independent once the one-pass execution exists. Source `T_partition3`; actual less/equal/greater observations retain their separate comparison laws. |
| B-020 | `Tslow_select k xs = Tinsort xs + Tnth (insort xs) k`. | Compose FDSA-X002 `Resources.InsertionSort.sortRun` with a B-014 lookup. `sortRun_value`, its length/cost bounds and the existing rank contract are candidate reuse; indexing work must be added. No extra wrapper charge is present. |
| B-021 | `k<n → Tslow_select k xs ≤ n²+3n+1`. | Use insertion-sort source bound, preserved length, and B-015. Stronger candidate sorting bounds may imply this weaker printed bound, but sorting-only estimates are not whole-selection estimates. |
| B-022 | `Tslow_median xs = Tlength xs + Tslow_select ((n-1)/2) xs`. | Compose measured length with the slow selection value and cost. Natural subtraction is truncated and division is `Nat.div`; source lower-middle indexing is explicit. |
| B-023 | `xs≠[] → Tslow_median xs ≤ n²+4n+2`. | Establish `((n-1)/2)<n` from nonemptiness, then B-005/B-021. An optional empty median must have a separately stated chosen cost; the printed implication supplies none. |

The existing FDSA-X002 size-at-most-five budget of 21 covers sorting alone.
Its use in median-of-medians still requires the length and lookup charges above.

## B.3 Construction of 2-3 trees

Use Chapter 7's actual alternating forest `T tree` or `TTs tree label forest`.
No ordering assumptions occur. These equations are shared with
`chapter07-obligations.md`; they do not justify replacing that carrier with a
list of binary trees.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-024 | `Tjoin_adj : tree23s α → Nat`: `TTs _ _ (T _)` costs 1; `TTs _ _ (TTs _ _ (T _))` costs 1; the remaining two-`TTs` prefix costs recursive tail work plus 1. | Missing measured operation on the Chapter 7 carrier. Source `join_adj` has no specified `T _` case; expose `not_T` or an optional total extension and prove recursive domain preservation. |
| B-025 | `Tjoin_all : tree23s α → Nat`: terminal `T _` costs 1; otherwise pay adjacent joining, recurse on its **actual output**, then add 1. | Missing source execution. `len_join_adj1` is the source termination support. A value-equivalent bulk constructor would not establish this recurrence. |
| B-026 | `Tleaves : List α → Nat`: empty costs 1; cons adds 1 to the tail. | Existing measured-list recursion techniques apply, but the value must be the alternating forest of empty trees and input labels. Source `T_leaves` gives `n+1`. |
| B-027 | `Ttree23_of_list xs = Tleaves xs + Tjoin_all (leaves xs)`. | Measured composition with no additional wrapper tick. Chapter 7 owns correctness and the `3n+3` upper bound. |

## B.4 Arrays via Braun trees

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-028 | `Tnodes : List (Tree α) → List α → List (Tree α) → Nat`: empty middle list costs 1; each nonempty middle-list branch recurses on its tail and adds 1, consuming each side-list head if one exists. This covers both side lists nonempty, left only, right only, and neither. | Implement/measure the Chapter 11 `nodes` value operation. Isabelle `T_nodes` proves the exact count `xs.length+1` **without** Braun, equal side-length or order assumptions. The existing random-access tree representation is different and does not supply this value/cost correspondence. |

## B.5 Leftist heaps

The existing `Search.LeftistQueue.PQ α π`, `combineQ`, `insertQ` and `deleteQ`
are substantive value-level reuse. Their operation definitions require only
`[LE π] [DecidableLE π]`; heap-order proofs add appropriate laws. A source
tree can be related to `PQ Unit α`, using its priority as the source label and
cached rank as the source node annotation. Prove that representation and its
smart-constructor/merge equations; do not create a second leftist heap merely
to copy the book's constructor spelling.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-029 | `Tmerge : LHeap α → LHeap α → Nat`: either empty argument costs 1; for nodes `t1=N l1 (a1,n1) r1`, `t2=N l2 (a2,n2) r2`, recurse on `(r1,t2)` when `a1≤a2`, otherwise `(t1,r2)`, then add 1. | `Search.LeftistQueue.combineQ` has the matching branch/tie direction after the representation bridge. A measured merge and exact erasure/count recurrence remain missing. `combineQ_entries`, `combineQ_ranked`, `combineQ_heap`, `rank_paths`, `rank_size`, `rank_log` are reusable value/invariant support, not existing execution bounds. |
| B-030 | `Tinsert x t = Tmerge (N E (x,1) E) t`. | `insertQ` uses precisely a singleton merge. Derive the cost from measured merge; no insertion-wrapper tick. |
| B-031 | `Tdel_min E=0`; a node's deletion cost is `Tmerge l r`. | `deleteQ` exposes root removal as `Option`; bridge nonempty deletion to its returned residual heap and empty deletion to the source empty result if that view is required. The empty cost is 0, not the merge base cost. |
| B-032 | `Tmerge_all []=0`, singleton cost 0; for two or more heaps pay `Tmerge_adj ts + Tmerge_all (merge_adj ts)`. | A pairwise-round constructor remains missing. Existing `makeQ` is a right fold of insertions, so neither its algorithm nor its cost is this one. |
| B-033 | `Tlheap_list xs = Tmerge_all (map singleton xs)`. | The singleton mapping is uncharged in this **selective merge-work** model. No B-006 map charge or extra wrapper tick may be inserted while claiming this exact recurrence. |
| B-034 | Referenced dependency from Chapter 15, p. 188: `Tmerge_adj []=0`, singleton cost 0, pair-head cost `Tmerge t1 t2 + Tmerge_adj tail`. | Record alongside B-032 even though the appendix references rather than displays it. Chapter 15 p. 187 explicitly chooses to count only merge work. The pinned `Leftist_Heap.thy` lacks this list-construction subsection, so the book itself is the current exact specification. |

## B.6 Priority queues based on Braun trees

These use the ordinary node-labelled binary-tree carrier and a Braun shape
invariant, not a leftist rank cache. The pinned AFP operation is the simpler
`del_left`/`sift_down` implementation in `Priority_Queue_Braun.thy`.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-035 | `Tinsert : α → Tree α → Nat`: empty costs 1; at `N _ x r`, recurse with `x` if `a<x`, otherwise with `a`, always into `r`, then add 1. | Missing measured Braun insertion. Retain strict `<` and equality branch; generic binary-tree operations do not implement this alternating-child insertion. |
| B-036 | `Tdel_min E=0`; any node with empty left child costs 0; otherwise pay `Tdel_left l`, obtain its actual `(y,l')`, and pay `Tsift_down r y l'`. | Missing measured deletion and value correspondence. The third clause is reached with `l≠E`. `del_left_size`/`del_left_braun` are source support for the sift domain. No wrapper tick. |
| B-037 | `Tdel_left (N E _ _)=1`; otherwise on `N l _ _` recurse into nonempty `l` and add 1. No empty-tree clause is displayed. | Use a nonempty-tree domain or explicit optional extension. A proof of nonempty recursive input is needed; `Inhabited α` is not a solution. The source operation itself permits arbitrary right subtrees here. |
| B-038 | `Tsift_down E a r=1`; `Tsift_down (N E _ _) a E=1`; for two nodes, cost is 1 if `a≤x1 ∧ a≤x2`, otherwise recurse into the first node's two children when `x1≤x2`, or the second's children otherwise, then add 1. | Missing measured sift. Preserve the source's shape domain: the displayed clauses do not give a meaningful general case for a left node with nonempty left child paired with empty right tree. Braun validity of the assembled node supplies the relevant domain and recursive closure. Do not manufacture a label for omitted cases or strengthen the literal base patterns unnecessarily. |

The source `T_insert`, `T_del_left_height`, `T_sift_down_height` and `T_del_min`
give later height bounds under their stated premises. Those belong to the
priority-queue chapter; this appendix inventory does not accept them by analogy
with another tree representation.

## B.7 Binomial priority queues

The carrier is a ranked node with a **list** of children; a heap is a list of
such trees. Neither Mathlib's binary tree nor conaled's leftist queue is a
definitionally matching representation. No current conaled binomial execution
was found. Use the chapter's source forest invariant for its logarithmic bounds,
but do not require it for elementary recurrence equations that make sense more
generally.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-039 | `Tlink`, `Trank`, `Troot`, `Tmin` are identically zero and removed from these equations. | Make this tariff explicit when measuring the existing/new value operations. A numeric label comparison cost is not silently added. |
| B-040 | `Tins_tree : BinTree α → List (BinTree α) → Nat`: empty forest costs 1; at head `t2`, cost is 1 when `rank t1 < rank t2`, otherwise recursive insertion of `link t1 t2` into the tail plus 1. | Missing measured source carry operation; preserve the rank test, link tie behavior and actual linked result. |
| B-041 | `Tinsert x ts = Tins_tree (Node 0 x []) ts`. | Singleton-tree insertion with no wrapper tick. |
| B-042 | `Tmerge` on forests: either empty costs 1. If first rank is smaller, recurse on first tail/full second; if second rank is smaller, recurse on full first/second tail; if equal, pay tail merge plus insertion of the linked heads into that **merged tail**. Add 1 to the selected branch. | Missing measured merge. The equal-rank branch must thread one actual recursive result into insertion; merely adding independently chosen upper bounds does not establish the exact recurrence. |
| B-043 | `Tget_min [t]=1`; at length at least two, recurse on the tail and add 1. | Nonempty forest/proof domain or optional extension required. No source empty equation. Isabelle `T_get_min_estimate` proves cost equals forest length under nonemptiness. |
| B-044 | `Tget_min_rest [t]=1`; at length at least two, recurse on the tail and add 1. | Same count, different output: minimum tree plus remaining forest. Keep its occurrence-removal/value contract separate. Source `T_get_min_rest_estimate`. |
| B-045 | `Tdel_min ts`: first pay minimum-with-rest; destruct its actual result as `(Node _ _ children, rest)`; pay `Titrev children []` and `Tmerge (itrev children []) rest`. | Nonempty input is needed for the source minimum. Reuse `SymmetricCosts.reverseRun_value/work` for the accumulator reversal after the carrier specialization; preserve reversed child order before forest merge. No extra deletion-wrapper charge. |

## B.8 Queues

The source pair `(fs,rs)` observes `fs ++ rs.reverse` and satisfies
`fs=[] → rs=[]`. Existing `Sequences.Symmetric.SymList` shares the pair carrier
and observation but has a different invariant and half-splitting rebalance.
Consequently its measured `tailRun` is not an exact source-cost replacement.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-046 | `Tnorm (fs,rs)` is `Titrev rs []` when `fs=[]`, otherwise 0. | Missing source normalization adapter; reuse measured accumulator reversal. On `([],[])` this is 1, even though the resulting queue remains empty. No equality decision on payload elements is needed to test list shape. |
| B-047 | `Tenq a (fs,rs) = Tnorm (fs,a::rs)`. | Source enqueue differs from symmetric-list rebalance. Once value erasure is proved, reuse `AbstractFIFO.Ops` and `Simulation` for clients, and measured composition for its exact charge. |
| B-048 | `Tdeq (fs,rs)=0` when `fs=[]`; otherwise `Tnorm (fs.tail,rs)`. | Source dequeue leaves an empty-front raw pair unchanged. Public queue correctness uses the source invariant; the exact raw-pair cost equation itself has no invariant premise. No dequeue-wrapper tick. |

`Sequences.AbstractFIFO.Simulation.runSquare`, `client_eq` and
`representation_independent` connect actual queue implementations through
observations. `Resources.Workload.run`, `run_invariant`, and
`Resources.run_potential`/`run_cost_le` provide the existing execution and
amortized infrastructure after these concrete measured operations are supplied.
Neither framework equates the two implementations' costs automatically.

## B.9 Splay trees

No current conaled source splay execution was found. Reuse the Chapter 4 binary
carrier and its traversal observations; implement the actual rotation/search
recurrences in the appropriate search domain and measure them separately.
The source's three-way `cmp` should map to a standard comparator/`Ordering`
with its explicit order law, not a second comparison vocabulary.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-049 | `Tsplay x E=1`. At `N AB b CD`, add 1 to this selected inner count: if `x=b`, 0; if `x<b` and `AB=E`, 0; otherwise for `AB=N A a B`, equality with `a` costs 0, a smaller `x` recurses into `A` only if nonempty, and a larger `x` similarly into `B`. The `x>b` case is symmetric through `CD=N C c D`, comparing with `c` and selecting `C` or `D`. | Missing measured source splay. Preserve every empty-child guard: it contributes 0 internally rather than invoking the recursive empty case of cost 1. AFP `time_fun splay equations splay.simps(1) splay_code` explicitly selects this execution form; `T_splay_simps` records its branches. |
| B-050 | `Tsplay_max E=1`; node with empty right child costs 1; at a right child `N _ _ CD`, add 1 to 0 if `CD=E`, otherwise to `Tsplay_max CD` plus the residual case selecting 0 from a nonempty `splay_max CD`. | The residual case has no displayed empty branch. Source `splay_max_Leaf_iff` proves that nonempty input stays nonempty, permitting a safe simplification to recursive cost plus 1 under that guard. Do not discard a partial case without this proof. |
| B-051 | `Tinsert x t=0` if `t=E`, otherwise `Tsplay x t`. | Missing measured source insertion; no additional insertion tick. AFP `T_insert_simp` supports the equation. |
| B-052 | `Tdelete x t=0` if empty; otherwise pay `Tsplay x t`, inspect the actual resulting node `N l a r`, and add 0 when `x≠a` or `l=E`; otherwise add `Tsplay_max l` and its nonempty-output case selecting 0. | Thread the actual splay result and prove its nonemptiness using `splay_Leaf_iff`/`splay_not_Leaf`; use `splay_max_Leaf_iff` for the nested case. Ordering/search correctness and the execution count are separate obligations. |

## B.10 Skew heaps

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-053 | `Tmerge : Tree α → Tree α → Nat`: either empty argument costs 1; on two nodes, recurse on `(t2,r1)` when `a1≤a2`, otherwise `(t1,r2)`, and add 1. | Missing measured skew merge. The first branch **swaps argument order** relative to leftist merge, and the value operation swaps children; the existing leftist `combineQ` is not this execution. |
| B-054 | `Tinsert : α → Tree α → Int`, equal to the natural merge count on singleton/input, embedded in `Int`. | This type is intentional, confirmed by `Skew_Heap_Analysis.T_insert_def`. Reuse generic `Resources.reweight`/`reweight_bind` with `Nat.castAddMonoidHom Int`; preserve nonnegativity. No raw insertion-wrapper tick. |
| B-055 | `Tdel_min : Tree α → Int`: empty gives 0; a node gives its children's natural merge count embedded in `Int`. | Confirmed by `T_del_min_def`. Keep this raw count separate from the AFP amortized framework's later `cost` wrapper, which adds 1 to insert/delete operations. The printed integer type is not a source error. |

The signed potential can decrease, but the raw costs in B-054–055 remain
nonnegative. `Resources.charge_iff_signed` is existing support for making signed
amortized expressions precise; it does not erase the distinction between raw
operation cost and the later extra wrapper charge.

## B.11 Pairing heaps

The source uses `Option (Hp α)`, where each nonempty heap node has a list of
nonempty child heaps. Empty has an explicit `none` representation. No matching
conaled pairing-heap execution was found; retain the chapter's actual two-pass
algorithm rather than treating any equal multiset result as equivalent work.

| ID | Source declaration and every branch | Exact current reuse or missing work |
|---|---|---|
| B-056 | `Tlink` and `Tmerge` are identically zero and eliminated. | AFP `T_link_0` and `T_merge_0` confirm the tariff. These operations still change values. |
| B-057 | `Tinsert` gives 0 on both `none` and `some heap`. | AFP `T_insert_0`; total explicit cases, no recursive insertion or added wrapper tick. |
| B-058 | `Tdel_min none=0`; for `some (Hp _ hs)`, pay `Tpass1 hs + Tpass2 (pass1 hs)`. | Missing measured two-pass deletion; pass 2 consumes the actual first-pass list. |
| B-059 | `Tpass1` on two or more child heaps costs recursive work on the tail after two heads plus 1; empty and singleton each cost 1. | Missing measured adjacent pairing pass. Its base cost differs from leftist `Tmerge_adj`, whose corresponding bases are zero. |
| B-060 | `Tpass2 []=1`; cons costs tail pass 2 plus a case on its actual result returning 0 for `none` and for `some`, then plus 1. | The residual case is exhaustive and can be proved identically zero by Option cases, unlike B-050's partial tree pattern. Retain the value-level right-to-left merging and source erasure. |

## Domain placement and acceptance evidence

The shared foundation consists of existing `Resources.Measured`,
`Resources.CallCount`, `Resources.Workload`, and potential infrastructure. Add
only measured list helpers or recurrence adapters with actual reuse, under
`Applications/Resources`; use existing public `List` functions for their value
contracts. In particular, no duplicate list library, cost monad or global
Isabelle-style timing typeclass is needed. Existing append, length and reversal
implementations should be referenced rather than copied. A source-tariff map
must coexist explicitly with Knapsack's different tariff.

Algorithms belong with their existing semantic domains: Selection helpers with
Selection; queue realizations with Sequences and `AbstractFIFO`; leftist
extensions with `Search.LeftistQueue`; balanced tree, Braun, splay, binomial,
skew and pairing operations with the appropriate later chapter/domain work.
Measured companions belong in Resources and should import their value
interfaces in the established direction. Chapter 7's 2-3 constructor costs
should be shared by reference between that chapter and B.3, not implemented
twice to satisfy two coverage lists.

For acceptance, record an exact declaration witness for each numbered row,
including recurrence equations, erasure, and every premise of the simple
properties. Useful connected examples distinguish the actual risks: duplicate
callback charges; zero/overlarge take/drop; valid versus invalid nth; chunk size
zero; source selection sorting-plus-indexing work; a leftist pairwise round
versus fold-insertion construction; empty queue normalization versus empty
dequeue; Braun deletion's shape domain; a binomial carry depending on merged
tail output; guarded splay empty subtrees; and zero-cost pairing insert versus
nonzero two-pass deletion. These should be theorem-level observations of the
public contracts, not a mirrored test suite of implementation internals.

No new mathematical source error was established in Appendix B. Its apparent
inconsistencies are explained by selected cost models, omitted invalid-input
equations, deliberate natural-to-integer coercions, and distinct data carriers.
The missing leftist-construction companion source is recorded as a support gap,
not an excuse to omit the printed obligations.

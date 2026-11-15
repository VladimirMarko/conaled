# Chapter 15: Leftist Heaps — source obligations and reuse

Prepared 2026-11-02. Local chapter handle: `FDSA-015`.

**State: queued; source preparation only.** This note covers printed
pp. 183–189, with p. 190 blank, in the pinned July 27, 2026 book. It includes
both exercises, all displayed definitions/results, the generic complexity
remarks and the exact referenced Appendix B.5 costs. No Lean source, ticket,
acceptance status or Git state was changed; no build or review loop was run.

## Source evidence and provenance

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 15 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. PDF pages 189–196. |
| Isabelle revision | <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`; a shared support snapshot later than the manuscript. |
| `Leftist_Heap.thy` | `src/HOL/Data_Structures/Leftist_Heap.thy`, SHA-256 `894e22da05b2dbf37ce46b8401958957e5d4a729c691d6a402b0e66dd8a22450`. Direct chapter link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Leftist_Heap.html>. Carrier, algorithms, correctness and generated access costs. |
| `Leftist_Heap_List.thy` | `src/HOL/Data_Structures/Leftist_Heap_List.thy`, 7,350 bytes; SHA-256 `fa1cb93ccb2e346bbdd8471d41ab537145e8f16fc1fc2ac30d357288804b9750`. Additional primary support discovered in the pinned directory inventory; supplies §15.4 algorithms, hand-written merge-only costs, power-of-two analysis and Lemma 15.1. |
| Shared ADT | `src/HOL/Data_Structures/Priority_Queue_Specs.thy`, SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`; Chapter 14 inventory owns its exact occurrence/validity interface. |
| Tree support | `src/HOL/Library/Tree.thy`, SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`; `src/HOL/Data_Structures/Tree2.thy`, SHA-256 `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e`. The latter's set/inorder observations discard node annotations. |
| Cost support | `src/HOL/Library/Time_Functions.thy`, SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`; Appendix B inventory B-029–034 records the exact source recurrences. The additional `Leftist_Heap_List.thy` now supplies primary theory support for B-032–034 as well. |
| License | BSD-3-Clause at this Isabelle pin; `ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Both leftist theories name Tobias Nipkow. Retain relevant notices for adapted source. |
| Lean reuse | Inspected conaled baseline `1aabd512284fe86254278ac631eda061d311050b`, with relevant existing leftist APIs already in checkout `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. |

Pinned raw URLs are
`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/`
followed by the revision, `/`, and the path above. Both leftist theories were
read completely. The scoped scan found no `sorry`, `oops`, `axiomatization`
or `admit` token in them; this is not an Isabelle rebuild or proof audit.
The p. 184 shape/exercise page and p. 188 summation/inequality page were
visually inspected, in addition to full text extraction. The all-length
linear extension, arbitrary-merge generalization and two exercise solutions
are not provided by the inspected leftist theories.

Reading copies are not deliverables. This original inventory and the pins
make the source work reproducible without copying the manuscript into a
checkpoint.

## Definitions, assumptions and exact existing reuse

Write `E` for the empty tree and `N l (a,c) r` for a source node with element
`a` and cached rank `c`. Let `n(t)` count labelled nodes, `ell(t)=n(t)+1`
count empty leaves, and `mh(t)` be minimum root-to-empty-leaf length.
All three distinctions below are essential:

| Book name | Existing conaled observation | Meaning |
|---|---|---|
| `mht` | `Search.LeftistQueue.rank` | Read the stored annotation, constant-time. |
| `mh` | `Search.LeftistQueue.shortPath` | Compute actual minimum path length from the shape. |
| Exercise 15.1 `rank` | `Search.LeftistQueue.rightPath` | Compute actual right-spine length. It is not the stored `rank` operation. |

The three agree on valid leftist trees, but not on arbitrary cached trees.
The structural invariant does not bound maximum height: an arbitrarily long
left chain is leftist while its nonempty nodes have short right spines.

| Existing API | Precise reuse and remaining work |
|---|---|
| `LeftistQueue.PQ α π` | Reuse the existing item/priority/cached-rank carrier. `PQ Unit α` recovers the book's element-only tree; `entries.map Prod.snd` recovers the labels. An explicit constructor/observation bridge replaces a duplicate leftist datatype. |
| `Ranked`, `Heap`, `Valid` | Already separate cache/shape validity, heap order, and their conjunction. `Ranked` compares child caches; the source `ltree` compares actual `mh`, so prove the recursive equivalence using `rank_paths`. Do not equate them by name alone. |
| `rank_paths` | `Ranked q → rank q=shortPath q ∧ rank q=rightPath q`. Gives the crucial source interpretation, but does not by itself prove the annotation-free Exercise 15.1 equivalence. |
| `fork`, `fork_rank`, `fork_ranked`, `fork_size`, `fork_entries`, `all_fork`, `fork_heap` | Exact source smart constructor, including keeping child order on equal ranks and swapping otherwise. Contents are a permutation, not necessarily the same traversal list. Source converse invariant lemmas need small additional proofs if exposed. |
| `combineQ`, `combineQ_entries`, `combineQ_size`, `combineQ_ranked`, `combineQ_heap`, `combineQ_valid` | Near-exact source merge with the same `≤` tie choice and right-spine recursive arguments. Termination is already by sum of sizes. Value/structural facts use only a decidable comparison; heap preservation adds a linear preorder on priorities. |
| `insertQ`, `insertQ_entries`, `insertQ_valid` | Singleton merge, with the same singleton placement. `fork … null null` reduces to a rank-1 singleton. Independent shape/order preservation can be recovered from the existing separate merge laws. |
| `deleteQ`, `deleteQ_spec`, `deleteQ_none_iff` | Actual root removal, returning `Option (entry × residual)`. Empty failure and successful one-occurrence deletion are explicit. `deleteQ_spec` combines `Valid` assumptions; the source's weaker separate content/rankedness/heap laws should be derived directly from the separate merge laws where appropriate. |
| `emptyQ`, `emptyQ_valid`, `nullQ`, `nullQ_iff`, `size_zero_iff`, `entries_length` | Empty boundary, validity and content/size bridges. Source `is_empty` is in the companion locale although omitted from the book's Chapter 14 figure. |
| `rank_size`, `rank_log` | `Ranked q → 2^rank q≤size q+1` and `rank q≤(size q+1).log2`. These are existing structural theorems, not yet merge execution bounds. |
| Mathlib `Real.log2_le_logb (n : Nat)` | Exact bridge `(Nat.log2 n : ℝ)≤Real.logb 2 n` in `Analysis/SpecialFunctions/Log/Base.lean`. It connects the existing integer bound to the book's real logarithms without defining another logarithm. |
| `Nat.log2_eq_log_two`, `Nat.le_log_of_pow_le`, `Real.natFloor_logb_natCast` | Alternative standard bridges when a proof already uses `Nat.log`. Prefer `Real.log2_le_logb` for the current `rank_log` route. |
| `Nat.le_pow_clog`, `pow_pred_clog_lt_self`, `clog_pow` | Useful for the all-length construction extension: choose a bounding power of two, with a factor less than two for input length greater than one. Handle 0 and 1 separately. |
| `Resources.Measured`, `pure`, `bind`, erasure lemmas | Existing value-plus-cost framework for actual merge and round execution. The chosen charge is selective; generic wrapper ticks would change the source model. |
| `LeftistQueue.makeQ`, `addListQ` | Right fold of singleton insertions. It is not §15.4's pairwise-round constructor, even though it has the same multiset and invariants. No linear construction bound transfers through output equivalence. |
| Batteries `PairingHeap.Heap.combine` | Different heap carrier and two-pass child-combination schedule. It is not the list-of-leftist-heaps round algorithm. |
| Mathlib finite sums / geometric sums | Standard `Finset` sums suffice for Lemma 15.1 by induction. `geom_sum_eq` and `geom_sum_Ico_le_of_lt_one` support a correctly qualified polynomial-sublinear generalization. No new summation framework is required. |

Structural carrier/shape facts need no order, equality or inhabitance on
payloads. Execution comparisons need `[LE π] [DecidableLE π]`; content
permutation, rank preservation and the rank-based cost bounds need no order
laws. Heap/minimum laws add `Std.IsLinearPreorder π`; the source minimum as a
unique element uses its linear-order specialization. Keep item and priority
universes independent.

Use a direct optional/proof-domain root observation for `get_min`. Merely
mapping the first result of `deleteQ` performs a child merge and loses the
source's constant-time minimum behavior. No `Inhabited α` is justified by
the source's unspecified empty minimum.

## 15.0 Shape and Exercise 15.1: pp. 183–184

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-001 | Leftist heap is an ordinary binary tree annotated with element/rank pairs. | Existing `PQ Unit α` bridge; reuse, rather than another cached-heap carrier. |
| C15-002 | `mht E=0`; `mht(N l (a,c) r)=c`. | Exact stored `LeftistQueue.rank` observation. |
| C15-003 | Augmented heap predicate ignores annotations and requires each node element to be a lower bound for both subtrees, which are themselves heaps. | `Heap`, `All`, `all_iff`; only priorities, not item values/caches, enter the comparison. |
| C15-004 | `ltree E=True`; a node requires `mh r≤mh l`, cache `c=mh r+1`, and leftist children. | Prove equivalence with `Ranked`, whose local condition uses child caches. |
| C15-005 | In every leftist subtree the right spine is a shortest root-to-leaf path; stored rank equals its length and `mh`. | `rank_paths`, after C15-004's bridge. This is not a maximum-height balance theorem. |
| C15-006 | `2^(mh t)≤ell(t)`, hence `mh t≤log₂ ell(t)`; following right spines supports logarithmic access. | Shared Chapter 4 minimum-height bound; on leftist trees also `rank_size`, `rank_log`, `Real.log2_le_logb`. |
| C15-007 | Exercise 15.1 defines annotation-free right-spine rank: empty zero, node equal to right child's rank plus one. | Existing `rightPath` after forgetting irrelevant item/cache fields; for plain `BinaryTree` share the shape observation with its exact bridge. |
| C15-008 | Exercise predicate `ltree_by f`: empty true; node requires `f r≤f l` and recursively satisfies the same predicate on both children. | New shape predicate if no existing common predicate fits; do not include cache correctness in this exercise's definition. |
| C15-009 | Exercise 15.1: `ltree_by rightPath t ↔ ltree_by mh t`. | New equivalence, proved with the auxiliary equality of right-spine and minimum height under either corresponding invariant. `Ranked` alone does not cover arbitrary annotations. |
| C15-010 | Exercise 15.1: `ltree_by numNodes t → 2^(rightPath t)≤numNodes t+1`. | Weight-biased shape proof by induction: right size no greater than left, and the right induction bound doubles. No weight-biased merge algorithm is requested by this exercise. |

## 15.1 Implementation: pp. 184–185

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-011 | `merge E t=t`, `merge t E=t`. | `combineQ` empty branches, including both empty. |
| C15-012 | On two nodes, if `a1≤a2` use `node l1 a1 (merge r1 t2)`; otherwise `node l2 a2 (merge t1 r2)`. | Exact `combineQ` branch/tie/argument order after the representation bridge. |
| C15-013 | `node l a r` reads both cached heights once; if right rank is at most left rank, keep the children and store right rank plus one; otherwise swap and store left rank plus one. | Exact `fork`; the branch uses cached rank, not recursively recomputed `shortPath`. |
| C15-014 | Merge terminates by sum of sizes, alternatively lexicographic input sizes. | Existing `combineQ` sum termination. The rank measure is only valid under an invariant and should not restrict total merge's termination. |
| C15-015 | Nonempty `get_min(N l (a,c) r)=a`. | Shared direct root adapter from Chapter 14; no traversal or arbitrary empty payload. |
| C15-016 | `insert x t=merge (N E (x,1) E) t`. | `insertQ` specializes exactly after singleton `fork` reduction. |
| C15-017 | Empty queue and deletion are inherited from Chapter 14: `empty=E`, `del_min E=E`, `del_min(N l _ r)=merge l r`. | `emptyQ` and a total source view of `deleteQ`, returning empty on `none`; no wrapper-cost claim follows yet. |

## 15.2 Correctness: pp. 185–186

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-018 | `M(E)=0`; `M(N l (a,c) r)={a}+M(l)+M(r)`, ignoring caches. | `Leftist_Heap.mset_tree`; `entries.map Prod.snd` coerced to a multiset supplies the Lean observation. |
| C15-019 | Validity is `heap ∧ ltree`, with no distinct-label premise. | Existing `Valid` modulo conjunction order and C15-004. |
| C15-020 | `heap t ∧ t≠E → get_min t=Min(S(t))`. | Source `get_min`; cache/rank validity is not required. |
| C15-021 | `M(merge t1 t2)=M(t1)+M(t2)` for all inputs. | `mset_merge`; `combineQ_entries` and `List.Perm.map`/multiset bridges. No validity hypothesis. |
| C15-022 | Leftist inputs give a leftist merged result. | `ltree_merge`; `combineQ_ranked` after the invariant bridge. Heap order is not required. |
| C15-023 | Heap-ordered inputs give heap-ordered merge. | `heap_merge`; `combineQ_heap`, without rankedness. |
| C15-024 | `M(insert x t)=M(t)+{x}` unconditionally. | `mset_insert`; `insertQ_entries`, with multiset commutativity. |
| C15-025 | Nonempty deletion removes exactly the root occurrence; the displayed source equation also holds at empty because subtracting any singleton from the empty multiset gives empty. | `mset_del_min`; in Lean express the nonempty root law and explicit empty case, or an Option-case equation, avoiding an arbitrary empty `get_min`. No heap/leftist premise is needed for content removal. |
| C15-026 | Leftist validity is preserved by insertion. | `ltree_insert`; derive from `combineQ_ranked` and the rank-1 singleton. |
| C15-027 | Heap order is preserved by insertion. | `heap_insert`; derive from `combineQ_heap`, independently of caches. |
| C15-028 | Leftist validity is preserved by deletion, including empty. | `ltree_del_min`; child validity and `combineQ_ranked`. |
| C15-029 | Heap order is preserved by deletion, including empty. | `heap_del_min`; child heap order and `combineQ_heap`. |
| C15-030 | These laws instantiate mergeable priority queues with the stated observation and invariant. | Source interpretation `lheap: Priority_Queue_Merge` discharges ten companion laws, including `is_empty` and two merge laws. Use the existing exact occurrence interface plus its explicit merge compatibility. |
| C15-031 | Cached rank reads actual minimum height on leftist trees. | `mht_eq_min_height`; first component of `rank_paths` after invariant equivalence. Needed for the smart-constructor proof, not an executable substitution. |
| C15-032 | Smart construction is leftist iff both children are; heap order holds iff both children are heaps and the new root bounds all their elements. | `ltree_node`, `heap_node` in supporting theory. Existing `fork_ranked`/`fork_heap` give forward construction laws; converse facts can be proved by the constructor's two branches. |

## 15.3 Exact access costs: p. 186 and Appendix B.5

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-033 | `TM(E,t)=TM(t,E)=1`; a two-node merge pays the selected recursive merge plus 1. | Appendix B-029 and generated `T_merge`. A measured `combineQ` with exact value erasure and branch-cost equations is missing. Charge no rank-read/smart-constructor traversal. |
| C15-034 | Insertion cost is exactly the merge cost of its singleton and old tree. | B-030; no extra insertion-wrapper tick. |
| C15-035 | Empty deletion costs 0; a node deletion costs only `TM(l,r)`. | B-031; distinguish this zero empty deletion from merge's base cost 1. |
| C15-036 | Leftist inputs imply `TM(l,r)≤mh(l)+mh(r)+1`. | `T_merge_min_height`; prove for measured execution by branch induction and rank interpretation. Heap order is unnecessary. |
| C15-037 | Equation (15.1): `TM(l,r)≤log₂ ell(l)+log₂ ell(r)+1` for leftist inputs. | `T_merge_log`; cast C15-036 and use `rank_log` with `Real.log2_le_logb`. Keep the `+1` leaf count at empty inputs. |
| C15-038 | Leftist `t` implies insertion cost at most `log₂ ell(t)+2`. | `T_insert_log`; the singleton has minimum height 1 and leaf count 2. |
| C15-039 | Leftist `t` implies deletion cost at most `2*log₂ ell(t)+1`. | `T_del_min_log`; case-split empty/node and bound each child leaf count by the parent's. |
| C15-040 | Empty construction and minimum observation are constant-time projections; the nonconstant access operations have logarithmic worst-case upper bounds in stored size. | Keep direct root/cache accesses distinct from content traversal, recomputation of minimum height and `toListQ`. No bound on maximum tree height is claimed. |

## 15.4 Pairwise list construction: pp. 186–187

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-041 | `merge_adj []=[]`, `merge_adj [t]=[t]`. | `Leftist_Heap_List.merge_adj`; retain an unmatched final heap unchanged. |
| C15-042 | `merge_adj(t1::t2::ts)=merge t1 t2 :: merge_adj ts`. | Adjacent pairs, original order, using actual `combineQ`. Existing right-fold `makeQ` is not this algorithm. |
| C15-043 | `merge_all []=E`, `merge_all [t]=t`. | Exact source base cases; no singleton remerge. |
| C15-044 | For at least two heaps, `merge_all ts=merge_all(merge_adj ts)`. | Recursion on list length, preserving the pass schedule. |
| C15-045 | `lheap_list xs=merge_all(map singleton xs)`, with singleton rank 1. | New pairwise constructor on the existing heap carrier, not a second occurrence queue. |
| C15-046 | `length(merge_adj ts)=(length ts+1)/2`. | `length_merge_adjacent`; standard natural ceiling-halving arithmetic, including 0 and 1. |
| C15-047 | For length at least 2, that length strictly decreases, proving `merge_all` termination. | C15-046 with natural division; preserve the guard. |
| C15-048 | If every input heap is heap-ordered, every result of `merge_adj` is heap-ordered. | `heap_merge_adj`; combine per-pair C15-023. |
| C15-049 | Under the same pointwise premise, `merge_all ts` is a heap. | `heap_merge_all`; empty case is valid. |
| C15-050 | If every input is leftist, every `merge_adj` result is leftist. | `ltree_merge_adj`; order laws are unnecessary. |
| C15-051 | Under that premise, `merge_all ts` is leftist. | `ltree_merge_all`. |
| C15-052 | Summing the content multisets over `merge_adj ts` gives the same multiset as summing over `ts`. | `mset_merge_adj`; source writes a multiset image and multiset sum. Use the ordinary sum of `ts.map M` with a checked equivalence. List entries are counted with multiplicity. |
| C15-053 | `M(merge_all ts)=sum(ts.map M)` for every input list. | `mset_merge_all`; no heap-order or leftist premise. |
| C15-054 | `heap(lheap_list xs)`. | `heap_lheap_list`; singleton validity plus C15-049. |
| C15-055 | `ltree(lheap_list xs)`. | `ltree_lheap_list`; singleton shape plus C15-051. |
| C15-056 | `M(lheap_list xs)=mset(xs)`. | `mset_lheap_list`; duplicates retained. The result need not equal the right-fold heap structurally. |

## 15.4 Construction costs, Lemma 15.1 and generalizations: pp. 187–189

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-057 | Construction analysis counts only merge work; list traversal, singleton mapping and wrapper calls are uncharged. | Explicit source text and hand-written cost functions. Keep distinct from the Chapter 1 general recursive-call convention and Appendix B.1 measured map. |
| C15-058 | `TA([])=TA([t])=0`; `TA(t1::t2::ts)=TM(t1,t2)+TA(ts)`. | `T_merge_adj`, p. 188, B-034. |
| C15-059 | `Tall([])=Tall([t])=0`; at length at least 2, `Tall(ts)=TA(ts)+Tall(merge_adj ts)`. | `T_merge_all`, B-032. It depends on the actual intermediate heaps. |
| C15-060 | `Tbuild(xs)=Tall(map singleton xs)`. | `T_lheap_list`, B-033; no hidden linear map/wrapper charge. |
| C15-061 | If all `ts` are leftist of the same node count `m`, `TA(ts)≤(length ts/2)*Tm(m)`, where `Tm(m)=2*log₂(m+1)+1`. | `T_merge_adj`; cast natural pair count to reals. The equal-size hypothesis is distinct from equal rank or equal shape. |
| C15-062 | Merge adds node counts; an even-length list of equal-size heaps becomes a list of twice that size after one pass. | `size_merge`, `size_merge_adj`. Odd carry prevents an unconditional equal-size conclusion. |
| C15-063 | Equation (15.2): if all inputs are leftist, each has node count `m`, and list length is `2^k`, then `Tall(ts)≤Σ(i=1..k) 2^(k−i)*Tm(2^(i−1)*m)`. | `T_merge_all`; all three premises and the one-based inclusive sum limits are material. |
| C15-064 | In the power-of-two case round `i` performs `2^(k−i)` merges of heaps of node count `2^(i−1)*m`. | The level interpretation underlying C15-063; exact equal sizes are preserved because no odd carry occurs before the singleton round. |
| C15-065 | Lemma 15.1: `Σ(i=1..k) 2^(k−i)*(2*i+1)=5*2^k−2*k−5`. | Source `summation` is a real-valued equality. Prove by induction/finite-sum splitting; avoid silently interpreting its subtraction as truncated natural subtraction. An addition-only natural version is another exact route. |
| C15-066 | For singleton initialization and length `2^k`, the source chain bounds `Tbuild` by the C15-063 sum with `m=1`, then by `Σ 2^(k−i)*(2*i+1)`. | Uses `2^(i−1)+1≤2*2^(i−1)` for `i≥1`, log monotonicity and `log₂(2^i)=i`. Preserve the summation index domain. |
| C15-067 | Published consequence: `length xs=2^k → Tbuild(xs)≤5*length xs−2*log₂(length xs)`. | `T_lheap_list`; the proof actually reaches the sharper `5*2^k−2*k−5`, then weakens it. Omitting `−5` in the final displayed bound is intentional, not a typo. |
| C15-068 | The book also claims a uniform linear bound for all input lengths, with the power restriction only a proof simplification. | Not proved in the inspected theory. A concrete extension route using maximum heap sizes and `Nat.clog`, yielding for example `Tbuild(xs)≤10*length xs`, is described below. It remains new formal work. |
| C15-069 | The logarithmic subtraction is asymptotically immaterial: the classes bounded by `n−log₂ n` and by `n` agree eventually. | Standard little-o/log growth and `Asymptotics` infrastructure can prove the two bounding directions on a sufficiently large positive domain. No pointwise identity is claimed. |
| C15-070 | The pairwise-round proof generalizes to any size-additive merge satisfying the stated logarithmic bound, independently of priority-queue/leftist semantics. | A generic operation, size observation, invariant preservation and actual merge-cost premise suffice. Reuse a small round lemma only if it serves these existing source clients; no full master-theorem framework is needed. |
| C15-071 | The prose further says sublinear merge work yields linear total work. | Requires a precise qualification: a polynomial bound `O(m^c)` for some fixed `0≤c<1` suffices; arbitrary `o(m)` does not. The independent counterexample below prevents accepting the unrestricted claim. |

## Exercise 15.2: tail-recursive construction, p. 189

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C15-072 | Define `merge_adj2` with two list arguments and tail recursion, without list append in its implementation. | Accumulator-first candidate: empty input returns accumulator; singleton pushes it; a pair computes merge and tail-calls on that result consed to the accumulator. |
| C15-073 | Define `merge_all2` using the new pass, with empty/singleton bases and a strict length decrease for larger lists. | Same ceiling-halving length argument; reversing a pass's results does not affect its length. |
| C15-074 | Define `lheap_list2` by singleton mapping and `merge_all2`. | Reuse the same singleton and heap carrier. |
| C15-075 | `M(lheap_list2 xs)=mset(xs)`. | New occurrence-preservation proof, using reversal/permutation of each pass and the existing merge content law. |
| C15-076 | `heap(lheap_list2 xs)`. | New pass/round heap-preservation proof. |
| C15-077 | `ltree(lheap_list2 xs)`. | New pass/round rankedness proof, independent of priority order laws. |
| C15-078 | The new pass has the same complexity as `merge_adj`, in particular no appended accumulator traversal. | In the selective model its merge-work cost equals `TA` of the unprocessed input: it merges the same original pairs once. For a full-call model, separately count one tail call per pair/base; do not conflate those tariffs. |
| C15-079 | Equality `merge_adj2 [] ts=merge_adj ts` is expressly not required. | The accumulator candidate returns `reverse(merge_adj ts)` from empty accumulator. Preserve invariants/contents, and prove any new whole-round cost bound independently; different pair orientation in later rounds can change exact merge counts. |

## Explicit cost conventions and boundary clients

The first cost layer counts invocations of recursive `merge`, including its
empty base. `mht` and `node` have cost zero in the source abstraction;
`T_mht_0` is proved in `Leftist_Heap.thy`. Insertion and deletion are wrappers
whose costs are exactly those stated above. The construction layer then counts
only those merge invocations, omitting the traversals around them. An actual
measured execution should erase to the existing value algorithm and prove
each selected count; an ordinary observational equality does not do this.

Useful boundaries are:

| Input | Exact source count / observation |
|---|---|
| Merge two empty heaps | Cost 1; both minimum heights 0, so the height bound is exact. |
| Insert into empty | Cost 1, because merge stops immediately. The published insertion bound is 2 and is deliberately loose. |
| Delete empty | Empty source view / `none` in existing Option API, cost 0. |
| Delete a singleton | Empty residual, cost 1 from merging two empty children. |
| Build an empty or singleton list | Merge-only construction cost 0. Only the singleton belongs to the power-of-two hypothesis with `k=0`. |
| Build two elements | One singleton/singleton merge, cost 2. Lemma 15.1 at `k=1` gives bound 3. |
| Equal priorities with distinct items | Content includes both occurrences; the first merge root wins a `≤` tie. Item equality/order is irrelevant. |
| A long left chain | Leftist and shallow on the right, despite linear maximum height. This distinguishes `rightPath`/`shortPath` from maximum height. |
| A singleton carrying cache 0 | Its annotation-free shape is leftist, but `Ranked` and source cached `ltree` fail. This prevents misusing `rank_paths` as the complete Exercise 15.1 proof. |

## Missing all-length extension: a concrete bounded route

For input length `N≥1`, let `k=Nat.clog 2 N` and `P=2^k`. Standard Mathlib
facts give `N≤P` and `P<2*N` when `N>1`; the singleton is immediate.
No padding or monotonicity of the actual comparison-dependent execution is
necessary. Instead establish round invariants:

1. Before round `i` (numbered from 1), each heap has at most `2^(i−1)` nodes.
   Merging adds sizes and an unpaired carried heap also satisfies the next
   upper bound.
2. There are at most `P/2^(i−1)` heaps, hence at most `P/2^i` merge calls
   in that round, for `1≤i≤k`.
3. Each such merge costs at most `2*i+1`, because each input has at most
   `2^(i−1)` nodes and therefore log leaf count at most `i`.
4. After at most `k` rounds there is at most one heap.

The same finite sum as Lemma 15.1 therefore bounds total merge work by
`5*P−2*k−5`, hence by `10*N`. Handle `N=0` directly. This is a proposed
proof route, not a compiled theorem, and its constant is not attributed to
the book. It avoids claiming exact source costs for a right-fold constructor
or assuming exact equal heap sizes when an odd heap is carried.

## Source qualification: “sublinear” is insufficient if it means little-o

For a size-additive merge of total input size `m`, take integer work

```text
c(m) = ceil(m / (floor(log₂ m)+1))    for m≥1,
c(0) = 0.
```

This is `o(m)`. For `N=2^k` singleton inputs, round `i` has `2^(k−i)`
merges whose total input size is `2^i`. Consequently

```text
S_k = Σ(i=1..k) 2^(k−i) * ceil(2^i/(i+1))
S_k / N ≥ Σ(i=1..k) 1/(i+1).
```

The harmonic sum is unbounded, so these costs are not uniformly `O(N)`.
An independent Python integer calculation gave `S_k/N` approximately
`1.50, 2.08203125, 2.69561768, 3.34487141, 4.01534871` at
`k=4,8,16,32,64`. These finite checks support the exact recurrence; the
unbounded harmonic lower bound is the mathematical counterexample. They are
not claimed as Lean proofs. Mathlib's `log_add_one_le_harmonic` in
`NumberTheory/Harmonic/Bounds.lean` is an available future divergence route.

For a fixed polynomial exponent `0≤c<1`, the normalized level costs instead
form a bounded geometric sum with ratio `2^(c−1)<1`, so the intended linear
conclusion follows under that stronger, precise assumption. The book's
specific logarithmic proof remains valid. Its reference to a master theorem
does not itself supply the missing hypothesis or a checked generalization.

## Integration boundary and acceptance gaps

Extend `Applications/Search/LeftistQueue` or narrow neighboring modules with
the source observation bridges, direct minimum access and pairwise-round
constructor. Keep source count execution and bounds in
`Applications/Resources`, importing the value operations. Reuse the existing
exact occurrence interface from Chapter 14 for clients. Do not copy another
leftist datatype or substitute `makeQ` for the source round schedule.

The substantial gaps are the cache/actual-height invariant equivalence,
annotation-free shape/weight exercise, exact measured merge/wrapper laws,
pairwise construction and its measured proof, the all-length extension,
properly qualified generic complexity claim, and the tail-recursive exercise.
Existing value proofs, logs and matrix-independent queue clients should be
reused at their exact strengths. Chapter acceptance remains queued until all
these obligations have checked witnesses and the project's required reviews.

# Chapter 17: Binomial Priority Queues — source obligations and reuse limits

Research date: 2026-11-02. Local ticket: `FDSA-017`.

**State: queued; source preparation only.** No Lean implementation, build,
ticket/acceptance change or remote write is performed by this note. Chapter 1
remains the active sequential chapter. Coverage rows are obligations for future
checked correspondence and review, not completed formalization claims.

## Sources and inspected pins

| Source | Inspected identity |
|---|---|
| Book | Peter Lammich, Chapter 17, printed pp. 195–202; p. 203 is the Part IV title and p. 204 blank. PDF pages 201–210, July 27, 2026 version of *Functional Data Structures and Algorithms: A Proof Assistant Approach*. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Direct companion | <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Binomial_Heap.html>. Pinned reading copy is `src/HOL/Data_Structures/Binomial_Heap.thy` at Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`. |
| Exact theory | <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Binomial_Heap.thy>; 22,737 bytes; SHA-256 `821d4236fb294b3b73b9c119a40f36225d3f16d4030b805c045da39dcf63210a`. Full file inspected. Source authors are Peter Lammich and Tobias Nipkow (tuning). |
| Shared sources | `Priority_Queue_Specs.thy`, SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`; `HOL/Library/Time_Functions.thy`, SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`. Appendix B B-039–045 inventories the source time recurrences; Chapter 14 owns the shared PQ/merge contract. |
| Isabelle license | BSD-3-Clause; pinned COPYRIGHT SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Preserve applicable notices when adapting code. |
| Lean reuse | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Inspected Batteries binomial files carry Apache-2.0 notices and credit de Moura, Limperg and Carneiro. |

The source revision postdates the book; this note records actual correspondence,
not an assertion that it built the manuscript. Source copies and extraction
remain in `book-source/`; this original note and provenance are the durable
deliverable, not the manuscript. A scoped admission-marker scan found none in
`Binomial_Heap.thy`. No Isabelle build or Lean build was run.

Scope includes the n-ary rank-cached tree/forest, all operations and helper
contracts, exact occurrence semantics, logarithmic bounds with their constants,
and both exercises, including every part of sparse binary addition. The
companion contains the main correctness/cost development but not complete
solutions of those two exercises.

## Carriers, invariants and reuse conclusions

Write `T r x cs` for the source's single tree constructor with cached Nat rank,
root payload and list of child trees. **There is no empty tree constructor**;
an empty priority queue is an empty forest list. Let `r(t)` be cached rank,
`root(t)` its root, `M_T(t)` its multiset, and `M_F(fs)` the multiset sum over
all forest entries, retaining multiplicities. Let `B(t)` be the binomial shape
predicate, `H(t)` heap order, `BH=B∧H`, and `V(fs)` the forest invariant.

Child ranks descend exactly from `r-1` to 0, while forest ranks ascend
strictly. Source rank fields are Nat, not Int. The structural/multiset
definitions need no payload ordering in principle; comparison and heap/minimum
proofs use the source's lawful linear order. Preserve the source contracts as
stated while avoiding gratuitous order assumptions on a reusable purely
structural observation.

### Batteries is substantial support, but not the same implementation

The full `Batteries/Data/BinomialHeap/{Basic,Lemmas}.lean` slices were inspected
by an independent read-only reuse subagent as well as targeted parent reads.

| Existing interface | Actual relationship to the book |
|---|---|
| `Batteries.BinomialHeap.Imp.HeapNode` | A binary child/sibling encoding of a whole child forest. It has `nil` and `node value child sibling`; internal cached ranks are absent. On well-formed values the binary shape is perfect. It is not definitionally the source's rank-cached n-ary tree. |
| `Imp.Heap` | Top-level `nil` or `cons rank value children next`, with Nat rank and a packed `HeapNode` child forest. An explicit decode/encode can relate this to the source forest on valid shapes. Invalid source caches need separate consideration; source raw-domain multiset laws must not be silently restricted. |
| `Imp.combine` | Same root comparison/tie direction as source `link`, and an exact child/sibling encoding of prepending the losing tree. A representation correspondence is still required. |
| `Imp.Heap.merge` | **Different equal-rank recurrence.** It checks the next heads' ranks before deciding whether to emit the carry, merge it into either remainder, or emit it while merging both remainders. Source always merges both tails first, then calls `ins_tree` on the linked heads. A concrete valid four-element counterexample below shows decoded tree equality fails, although contents agree. |
| `HeapNode.rank`, `.rankTR`, `.toHeap` | `rank` scans the sibling spine; `toHeap` first computes that rank, then reverses/rebuilds children into an ascending forest. Source reads cached rank in constant time and uses explicit `itrev` on an already-present child list. Preserve this cost difference. |
| `Imp.Heap.headD`, `.head?` | A left-to-right accumulator scan with optional empty result. Source `get_min` is a right-recursive minimum. A lawful-order value bridge is plausible, but not a literal recurrence identity. |
| `Imp.Heap.findMin`, `.deleteMin` | Uses a continuation/difference-list `before` field while scanning left to right, then `toHeap` and the optimized merge. Source `get_min_rest` recursively scans the tail and reconstructs a list with exactly one tree removed. Both prefer the first tied minimal root under a lawful non-strict comparison, but deletion shapes still inherit different merge behavior. |
| `HeapNode.WF`, `Heap.WF` and preservation lemmas | Useful structural and heap-edge invariant support. The node invariant combines perfect binary shape with local order edges guarded by totality of the Boolean relation. A LinearOrder specialization supplies totality/transitivity for leastness. Do not conflate these predicates with source `B` without an encoding proof. |
| `HeapNode.WF.realSize_eq`, `Heap.WF.size_eq` | Relate packed real size to powers/rank-based size. Useful after decoding correspondence; they do not directly prove the source forest-length bound. |
| `Heap.findMin_val`, `Heap.deleteMin_fst` | Establish consistency of selected value with the library's own `headD`/`head?`. The inspected files do **not** provide the complete source multiset/permutation content laws or minimum-leastness theorem. Those are genuine remaining gaps, not consequences of a theorem name. |

Use the existing `Search.PriorityInterface.ExactQueue` / `ExactLaws` in
`Applications/Search/ExactPriority.lean` for exact occurrence clients. Their
`add_exact` and `remove_spec` are stronger and more appropriate than the keyed
replacement interface. Chapter 14 plans a separate small compatibility
contract for merge; neither existing interface currently contains it. A
binomial realization still needs the source root scan, single insertion,
multiset observation and merge laws. The leftist implementation is not a
binomial implementation merely because both realize that interface.

Existing `Resources.BinaryCounter` uses a dense low-bit-first `List Bool`;
`RandomAccess` uses cached perfect binary blocks with zero/one digit slots.
Their arithmetic observations, measured-erasure patterns and potential proofs
are useful, but neither is Exercise 17.2's sparse ascending list of set-bit
positions. `Nat.choose` and the hockey-stick identity already exist in
Mathlib; details appear with Exercise 17.1 below.

## Trees, forests and sizes: pp. 195–197

| ID | Source obligation | Exact hypotheses, reuse or remaining work |
|---|---|---|
| C17-001 | N-ary datatype `T rank root children`; forest is `List Tree`; rank/root projections. | Reuse a genuinely matching recursive carrier if available; the inspected binary/packed carriers need explicit adapters. Root is total because every source tree is nonempty. |
| C17-002 | `B(T r x cs) ↔ (∀t∈cs, B t) ∧ map rank cs=reverse(range r)`. | Exact cached-rank and child-order invariant. It implies exactly `r` children, one of each smaller rank. |
| C17-003 | `H(T r x cs) ↔ ∀t∈cs, H t ∧ x≤root t`; `BH t ↔ B t∧H t`. | Local parent-to-child comparisons extend to all descendants by transitivity. Shape and heap order should remain separately identifiable. |
| C17-004 | `V fs ↔ (∀t∈fs, BH t) ∧ List.Pairwise (<) (map rank fs)`. | Source `sorted_wrt (<)` is strict all-pairs ordering. Equal ranks are forbidden at forest level but are precisely the domain of `link`. |
| C17-005 | Cons characterization: `V(t::fs) ↔ BH t ∧ V fs ∧ ∀u∈fs, rank t<rank u`. | `invar_Cons`; standard list Pairwise laws supply the logical form. |
| C17-006 | `M_T(T r x cs)={x}+M_F(cs)`; `M_F(fs)=Σ(t in fs) M_T(t)`. | Multiset/list sum retains repeated subtrees and repeated payloads. Do not use a set sum over distinct forest elements. |
| C17-007 | Every tree multiset is nonempty and contains its root; `M_F([])=0`, `M_F(t::fs)=M_T(t)+M_F(fs)`, and `M_F(fs)=0 ↔ fs=[]`. | `mset_tree_nonempty`, `root_in_mset`, `mset_forest_Nil/Cons`, `mset_forest_empty_iff`; no shape/heap premise. |
| C17-008 | Reversal does not change forest multiset; a binomial heap node's reversed child list is a valid forest. | `mset_forest_rev_eq` is unconditional; `invar_children` assumes `BH(T r x cs)` and concludes `V(reverse cs)`. Keep these distinct assumptions. |
| C17-009 | `B t → card(M_T t)=2^(rank t)`. | `size_mset_btree`, lines 417–441. Heap order is not needed for this count. Its combined-invariant corollary is `size_mset_tree`. |
| C17-010 | Supporting geometric sum `Σ(i<r) 2^i=2^r-1`, hence the children plus root contain `2^r` occurrences. | Reuse standard Nat power sums with the exact 0-through-`r-1` range and `r=0` boundary. No empty tree appears at rank 0: it is a single root. |
| C17-011 | Forest size equals the sum of individual tree sizes; on shape-valid trees it is `Σ(t∈fs)2^(rank t)`. | Ordinary finite list sum, not a quotient ignoring duplicates. This is the bridge to sparse binary numbers. |
| C17-012 | Strictly ascending natural ranks satisfy `i≤rank(fs[i])` at every valid zero-based index. | Source uses `sorted_wrt_less_idx`; prove via standard Pairwise/strict-monotone list facts. |
| C17-013 | `V fs → 2^(length fs)≤card(M_F fs)+1`. | Combine the minimum rank sequence `0,…,length-1` with the geometric sum. No assumption that ranks are consecutive is allowed. |
| C17-014 | Equation (17.1): `V fs → length fs≤log₂(card(M_F fs)+1)`. | `size_mset_forest`, lines 450–471; right side is a real logarithm, with no ceiling. A Nat-log bound can be proved first and bridged. `N+1≥1` handles empty input. |
| C17-015 | Introductory binomial level-count claim: a rank-`r` binomial tree has `choose r l` nodes at level `l`. | Retain as Exercise 17.1, C17-059–062, not a drawing-only observation. Level 0 contains the root. |

## 17.2.1 Linking and insertion: pp. 197–199

| ID | Source obligation | Exact algorithm and theorem strength |
|---|---|---|
| C17-016 | `link(T r x cs,T r' y ds)` compares `x≤y`; true yields `T(r+1)x((T r' y ds)::cs)`, false yields `T(r+1)y((T r x cs)::ds)`. | Output cached rank always uses the **first** rank `r+1`, even on invalid unequal-rank inputs. Ties keep the first root. |
| C17-017 | `rank(link t u)=rank t+1`, without any validity/equal-rank premise. | `rank_link`. This raw fact underlies lower-rank-bound preservation and the sparse carrying analogy. |
| C17-018 | `BH t ∧ BH u ∧ rank t=rank u → BH(link t u)`. | `invar_link`; equal ranks are essential to binomial shape. |
| C17-019 | `M_T(link t u)=M_T(t)+M_T(u)` for all raw trees. | `mset_link`; no shape, equal-rank or heap premise. This strength differs from the rank-power numerical analogy on invalid trees. |
| C17-020 | `ins_tree t []=[t]`; at `u::fs`, prepend `t` unchanged if `rank t<rank u`; otherwise recursively insert `link t u` into `fs`. | It intentionally lacks the general `rank t>rank u` insertion case. The intended rank-lower-bound premise ensures the linking branch has equal ranks. |
| C17-021 | `BH t ∧ V fs ∧ (∀u∈fs,rank t≤rank u) → V(ins_tree t fs)`. | `invar_ins_tree`; all three premises matter. On a nonempty valid forest the last premise can be reduced to the head but source states it over all entries. |
| C17-022 | `M_F(ins_tree t fs)=M_T(t)+M_F(fs)` unconditionally. | `mset_forest_ins_tree`; even malformed rank caches do not alter the payload multiset. |
| C17-023 | Strict lower rank bound is preserved by carrying: if `k<rank t` and `k<rank u` for every `u∈fs`, then every result tree has rank greater than `k`. | `ins_tree_rank_bound`, written in the source using `rank t₀` instead of arbitrary `k`. No heap/shape invariant is required. |
| C17-024 | `insert x fs=ins_tree(T 0 x []) fs`; rank-0 singleton satisfies `BH`. | `bheap0`; global forest lower bound is automatic because ranks are natural. |
| C17-025 | `V fs → V(insert x fs)` and `M_F(insert x fs)={x}+M_F(fs)` with the latter unconditional. | `invar_insert`, `mset_forest_insert`. Exact repeated occurrence addition, not set insertion or keyed replacement. |

## 17.2.2 Forest merge: p. 199

| ID | Source obligation | Exact algorithm and theorem strength |
|---|---|---|
| C17-026 | Either empty forest returns the other. With two heads, smaller first rank emits first head and recurses on first tail/full second; smaller second rank is symmetric. | `merge`, lines 167–174. These are rank comparisons, not payload/root comparisons. |
| C17-027 | Equal ranks: compute `mergedTail=merge firstTail secondTail`, then `ins_tree(link firstHead secondHead) mergedTail`. | Preserve this actual dependency and link argument order. Batteries' optimized carry-before-tail strategy is not the same recurrence or always the same decoded result. |
| C17-028 | Recursive `merge` terminates by sum of forest lengths; `ins_tree` terminates by its forest length. | Rank may grow along carrying; it is not the decreasing measure. The recursively produced tail is a value used by subsequent insertion. |
| C17-029 | If every input tree has rank greater than `k`, then every tree in `merge fs gs` has rank greater than `k`. | `merge_rank_bound`, lines 181–187; no `V` premises. Source words “lower bound” are realized by a strict inequality. |
| C17-030 | `V fs ∧ V gs → V(merge fs gs)`. | `invar_merge`. For unequal ranks use C17-029 to prepend safely; for equal ranks it establishes `rank linked≤rank eachMergedTailTree`, needed by `ins_tree`. |
| C17-031 | `M_F(merge fs gs)=M_F(fs)+M_F(gs)` for arbitrary raw forests. | `mset_forest_merge`; multiplicities add and no invariant is needed. |

## 17.2.3–17.2.4 Minimum and removal: pp. 200–201

| ID | Source obligation | Exact domain and theorem strength |
|---|---|---|
| C17-032 | `get_min [t]=root t`; on at least two trees, `get_min(t::fs)=min(root t,get_min fs)`. | No empty result is specified. Follow the shared valid-domain or `Option` convention; no global payload inhabitant. |
| C17-033 | A binomial heap's root is below every payload in its multiset. | `bheap_root_min` assumes `BH t`; a heap-only strengthening is possible but should remain explicit. |
| C17-034 | On nonempty valid forest, `get_min fs` is below every payload; on any nonempty raw forest it belongs to `M_F(fs)`. | `get_min_mset` needs `V`; `get_min_member` does not. Root scan alone is not a true payload minimum without heap order. |
| C17-035 | `V fs ∧ M_F(fs)≠0 → get_min fs=Min(M_F fs)`. | Source `get_min`; equivalent nonempty-domain formulation via C17-007. |
| C17-036 | `get_min_rest [t]=(t,[])`; for at least two trees, recurse on tail to `(u,rest)`. If `root t≤root u`, return `(t,originalTail)`; otherwise `(u,t::rest)`. | Preserve original tail in the first branch. Ties select the earliest minimum-root tree in the original forest; only one occurrence is removed. |
| C17-037 | If `fs≠[]` and `get_min_rest fs=(t,rest)`, then `root t=get_min fs`. | `get_min_rest_get_min_same_root`; no invariant premise. |
| C17-038 | Under the same hypotheses, the **multiset of trees** satisfies `mset(fs)={t}+mset(rest)`. | `mset_get_min_rest`; implies selected membership and exact removal before mapping to payload multisets. The set corollary alone is weaker. |
| C17-039 | With additionally `V fs`, both `BH t` and `V rest` hold. | `invar_get_min_rest`; strict forest order is preserved after deleting the selected tree. |
| C17-040 | `del_min fs`: obtain `(T r x children,rest)=get_min_rest fs`, then `merge(itrev children []) rest`. | Actual accumulator reversal, not quadratic naive reversal. The reversed children become a valid ascending-rank forest. Defined source behavior is only needed on nonempty `fs`; choose an explicit total failure/empty extension separately. |
| C17-041 | `V fs ∧ fs≠[] → V(del_min fs)`. | `invar_del_min`, using extracted validity, `invar_children`, reversal correspondence and `invar_merge`. |
| C17-042 | `fs≠[] → M_F(fs)=M_F(del_min fs)+{get_min fs}`. | `mset_forest_del_min`; **no forest invariant**. It removes a minimum root even when that root is not the least interior payload. Preserve this stronger raw-domain occurrence statement. |
| C17-043 | All eight `Priority_Queue` laws plus the two merge laws hold. | Source `bheaps : Priority_Queue_Merge`, lines 385–411. The shared interface/adapters must retain exact occurrences, valid-domain minimum, empty behavior and merge semantics. |

## 17.3 Costs: pp. 201–202, Appendix B.7

Use the exact selected-function tariff: `T_link=T_rank=T_root=T_min=0`;
`ins_tree`, `merge`, `get_min`, `get_min_rest` count their recursive entries;
nonrecursive `insert` and `del_min` add no wrapper tick. `T_itrev cs []`
equals `length cs+1`, including the empty base call. These are abstract
recursive-call observations, not a claim that comparisons or link allocation
literally take zero machine time. Reuse B-039–045 and the existing measured
accumulator reversal after proving the concrete value correspondence.

| ID | Source obligation | Exact recurrence or bound |
|---|---|---|
| C17-044 | `T_ins_tree t []=1`; at a head, stop/prepend costs 1; linking branch pays recursive tail insertion plus 1. | B-040; link itself has zero tariff. Thread the actual linked tree into the recursive call. |
| C17-045 | `T_ins_tree t fs≤length fs+1`, without invariants. | `T_ins_tree_simple_bound`, lines 489–490. |
| C17-046 | `T_insert x fs=T_ins_tree(T 0 x []) fs`; `V fs → T_insert x fs≤log₂(card(M_F fs)+1)+1`. | B-041, `T_insert_bound`. Empty input has exact cost 1 and right side 1. |
| C17-047 | `T_merge` on either empty argument is 1; each unequal-rank branch adds 1 to the selected tail merge. Equal ranks pay tail-merge time plus `T_ins_tree` of linked heads into the **actual merged tail**, plus 1. | B-042; do not count independently chosen abstract forests or charge a second tail merge. |
| C17-048 | Exact potential identity `T_ins_tree t fs+length(ins_tree t fs)=2+length fs`. | `T_ins_tree_length`, lines 516–518; all raw inputs. Every carry consumes a forest tree while contributing to time. |
| C17-049 | Coupled merge bound `T_merge fs gs+length(merge fs gs)≤2·(length fs+length gs)+1`. | `T_merge_length`, lines 520–523; all raw inputs. This is the essential linear proof, not a loose independent quadratic estimate of each nested insertion. |
| C17-050 | For valid forests with payload sizes `N₁,N₂`, `T_merge fs gs≤4·log₂(N₁+N₂+1)+1`. | `T_merge_bound`, lines 526–546. An intermediate bound is `2log₂(N₁+1)+2log₂(N₂+1)+1`; logarithm monotonicity gives the displayed constant 4. |
| C17-051 | Nonempty `T_get_min fs=length fs`; hence for valid nonempty forest `T_get_min fs≤log₂(card(M_F fs)+1)`. | B-043, `T_get_min_estimate`, `T_get_min_bound`, lines 559–570. No empty-source equation; no extra wrapper charge. |
| C17-052 | Nonempty `T_get_min_rest fs=length fs`; same logarithmic bound under validity. | B-044, `T_get_min_rest_estimate/bound`, lines 576–587. Same count does not identify its returned tree/remainder with a root-only minimum. |
| C17-053 | `T_del_min fs=T_get_min_rest fs+T_itrev children []+T_merge(reverse children) rest`, where `(T r x children,rest)` is the actual extraction. | B-045. Include reversal work; no separate `get_min` call occurs during deletion. |
| C17-054 | The extracted child forest and remaining forest are valid; if their payload sizes are `N₁,N₂` and original size is `N`, then `N₁+N₂+1=N`. | Source proof only needs `N₁≤N` and `N₁+N₂≤N`, but exact occurrence decomposition supplies the stronger identity. Needed to bound all parts of deletion. |
| C17-055 | Child reversal bound `T_itrev children []=length children+1≤log₂(N₁+1)+1`. | Use validity of the **reversed child forest** and preservation of length/multiset; original forest length alone is insufficient. |
| C17-056 | `V fs ∧ fs≠[] → T_del_min fs≤6·log₂(card(M_F fs)+1)+2`. | `T_del_min_bound`, lines 591–625; three terms have logarithmic coefficients 1, 1 and 4. Keep both constant base charges. |
| C17-057 | Introductory `O(log n)` bounds for insertion, minimum, deletion and merge. | Use `log(n+1)` for total size boundaries or state an eventual positive-size domain; merge size is combined input payload count. These are worst-case upper bounds, not matching lower bounds on every input. |
| C17-058 | The p. 201 suggestion that the operations are all linear in original forest length needs qualification for deletion. | On a singleton forest containing a valid rank-`r` tree, the exact source count is `1+(r+1)+1=r+3`, while forest length is always 1. The final `6log+2` theorem remains correct because it separately bounds the extracted child forest. |

## 17.4 Exercises: p. 202

### Exercise 17.1: binomial coefficients

| ID | Exact obligation | Reuse and proof scope |
|---|---|---|
| C17-059 | Define `nol : Nat → Tree α → Nat` counting nodes at a given edge distance from the root. | Concrete recursion: `nol 0(T r x cs)=1`; `nol(k+1)(T r x cs)=Σ(t∈cs) nol k t`. Any implementation must count every child occurrence. |
| C17-060 | Prove `B t → nol l t=Nat.choose (rank t) l`, for every `l`, including `l>rank t`. | Root level 0 and levels beyond the rank are part of the quantification. Heap order and payload values are irrelevant. |
| C17-061 | Hint identity `Σ(i<r) Nat.choose i k=Nat.choose r (k+1)`. | Mathlib `Nat.sum_Icc_choose (n k)` in `Data/Nat/Choose/Sum.lean` states `Σ(m∈Icc k n) choose m k=choose(n+1)(k+1)`; drop zero terms for `m<k` and handle `r=0` to obtain the required range version. `Nat.choose_eq_zero_of_lt`, `choose_zero_right` and Pascal's recurrence are reusable. |
| C17-062 | Connect the level-count result to the rank-size count and the introductory binomial interpretation. | Summing levels 0 through rank yields `2^rank`, via existing `Nat.sum_range_choose`. This is a useful checked connection; it does not replace the exercise's pointwise level theorem. |

### Exercise 17.2: sparse binary numbers

Sparse numbers are lists of set-bit positions, **not** lists of zero/one
digits. Positions are natural numbers and must be strictly ascending. The
printed example `[1,3,4]` denotes 26, binary `11010`. The following concrete
algorithm mirrors the source's carry-after-tail-merge strategy.

| ID | Exercise part and exact obligation | Concrete recurrence, domain and proof |
|---|---|---|
| C17-063 | Part 1: `invar_sn : List Nat → Bool` checks strictly ascending positions. | Logical invariant is `List.Pairwise (<)`. Reuse a standard executable checker with an iff bridge; an adjacent-pair checker is sufficient because `<` on Nat is transitive. Do not accept duplicates. |
| C17-064 | Part 1: `num_of ps=Σ(p∈ps)2^p`. | Finite list sum, defined for all raw lists. Validity gives the canonical sparse representation, while invalid duplicates still contribute multiple powers. `num_of []=0`, `[0]` denotes 1. |
| C17-065 | Carry helper `carry p []=[p]`; `carry p(q::qs)=p::q::qs` if `p<q`, otherwise `carry(p+1) qs`. | Intended domain: `invar_sn qs` and `p≤` every position in the input number. In the recursive branch this makes `p=q`; without it a numeric bit is incorrectly consumed. |
| C17-066 | Part 1 addition: empty input returns the other; smaller first head is emitted and its tail added to full second; smaller second head is symmetric; equal `p` calls `carry(p+1)(add firstTail secondTail)`. | Exact analogue of binomial `merge`; recursive tail addition must be computed once and passed into carry. Sum of input lengths gives addition termination; carry decreases its list length. |
| C17-067 | Carry correctness on its domain: valid output and `num_of(carry p ps)=2^p+num_of ps`. | Needs valid ascending input and lower-bound precondition. Link's unconditional **payload multiset** law does not turn this numerical equation into a raw-domain theorem. |
| C17-068 | Strict lower bounds on positions are preserved by carry and addition. | Mirror C17-023/C17-029. These support ascending order after emitting a smaller head and the carry precondition after equal heads. |
| C17-069 | Part 2: two valid inputs yield a valid `add` result and `num_of(add ps qs)=num_of ps+num_of qs`. | Preserve the input validity premises for the direct carry algorithm. The invalid-input counterexample below rules out an unconditional numerical correctness claim. |
| C17-070 | Part 3: define time on actual carry/add branches, with one per recursive entry, empty cases included, and primitive position comparisons/increment free/unit according to the stated model. | State the tariff explicitly. `num_of` is an observation used in correctness, not a huge-power computation executed by `add`. |
| C17-071 | Exact helper identity `T_carry p ps+length(carry p ps)=length ps+2`. | Holds for all raw position lists because it concerns branch lengths, independently of numeric validity. |
| C17-072 | Linear addition bound `T_add ps qs+length(add ps qs)≤2·(length ps+length qs)+1`, hence `T_add≤2·(length ps+length qs)+1`. | Prove by the same combined time/output-length induction as forest merge. The count bound can hold on all raw lists even though numeric correctness requires valid inputs. |
| C17-073 | Check empty, equal single positions, long consecutive carries, separated sparse positions, and the source example. | Concrete values such as `add [0,1,2] [0]=[3]` and `num_of [1,3,4]=26` connect the general theorems to the intended binary interpretation. Cases are future checked specializations, not acceptance claims here. |
| C17-074 | Harmonize with existing dense counter observations through an explicit set-bit-position conversion if used. | Existing `Resources.BinaryCounter.value`, `.Canonical`, `.inc`, `.value_inc` and potential facts are useful support. Dense increment is not sparse two-number addition, and its bit-flip count is not the sparse carry/add recursive-call count. |

## Implementation-sensitive counterexamples and scope checks

| ID | Issue | Concrete disposition |
|---|---|---|
| C17-075 | Batteries optimized merge is not structurally identical to the source on valid forests. | Preserve the explicit four-element example below. A source-faithful algorithm over an encoded carrier or a clearly named optimized realization needs its own correspondence; a multiset equivalence does not transport the book's exact recurrences. |
| C17-076 | Source raw `link` accepts unequal ranks but its shape theorem does not. | For example, linking a rank-0 leaf with a valid rank-1 tree still has cached rank 1 from the first argument but contains 3 payloads, not `2^1`. Its multiset theorem remains true. Keep shape premises and source projection behavior exact. |
| C17-077 | Direct sparse addition on invalid lists need not compute numerical addition. | With the proposed source-analogue recurrence, `add [1,0] [1]=[3]`, so output value 8 differs from input sum `3+2=5`. The first list violates ascending order. Retain a checked counterexample alongside the conditional arithmetic theorem. |
| C17-078 | Priority-queue minimum is a root scan, not an unconditional minimum of every raw tree's contents. | A malformed heap root larger than an interior label yields a larger selected root even though minimum extraction still removes exactly that root occurrence. Keep heap/order hypotheses on leastness, not on unconditional occurrence laws. |
| C17-079 | Figure 17.1 caption allows equal roots while drawing one orientation. | Both orientations preserve heap order at equality, but the actual displayed `link` deterministically keeps its **first** root on `≤`. The drawing's admissibility does not override the algorithm's tie choice. This is a presentation qualification, not a false heap-order assertion. |
| C17-080 | Strong resource claims require recurrence correspondence. | No measured cost for Batteries merge, child-spine rank scan or continuation-based minimum extraction was found in the inspected files. Its `O(log n)` comments and shape proofs are not a proof of the source's constants or potential identity. |

### Concrete valid merge counterexample

Let `L(v)=T 0 v []` and `U=T 1 0 [L(1)]`. Both input forests

```text
A = [L(0), U]
B = [L(2)]
```

satisfy `V`: each is a min-heap, and A's ranks are 0 then 1. In the book's
algorithm the rank-0 heads link to `V=T 1 0 [L(2)]`. Merging the remaining
forests gives `[U]`, then `ins_tree V [U]` links `V` as the first argument;
their root tie keeps V's root. The final forest is

```text
[T 2 0 [T 1 0 [L(1)], L(2)]] .
```

In Batteries, the equal-rank optimization merges the first remainder `[U]`
with the newly linked singleton `[V]`; that later link receives U first and
keeps U's tied root. Decoding its packed child/sibling result gives

```text
[T 2 0 [T 1 0 [L(2)], L(1)]] .
```

The trees differ, though both are valid and both have payload multiset
`{0,0,1,2}`. A small independent Python evaluation of the two displayed
recurrences checked this example during research; no Lean theorem or runtime
test is asserted. It should become a checked representation/cost-boundary
example if both implementations are exposed.

### Deletion's input-length qualification

For a valid single rank-`r` tree, the original forest has one entry but its
selected root has `r` children. The source costs are exactly:

```text
T_get_min_rest = 1
T_itrev children [] = r + 1
T_merge (reverse children) [] = 1
T_del_min = r + 3 .
```

Thus the p. 201 broad phrase “operations are linear in the length of the
forest” cannot be used as a uniform theorem for deletion in terms of only
the original forest length. The subsequent detailed logarithmic proof is
sound: the original root represents `2^r` elements, and the reverse-child
forest has its own valid rank/size bound. Retain this counterfamily and the
corrected explanation, not a weakened `6log+2` theorem.

## Handoff

Start from Chapter 14's exact occurrence interface and the source n-ary
rank/child-order contracts. Decide a reusable encoded carrier only after
proving how it realizes those contracts; do not identify Batteries merge with
the book's different carry strategy. Establish raw-domain multiset laws and
conditional structural/heap laws separately. Keep the actual extraction,
accumulator reversal and merge dependency for deletion. Attach B-039–045 to
the actual operations, prove the two coupled time/output-length estimates,
and derive every displayed logarithmic constant. Complete both exercise
families, especially sparse-add numeric preconditions and linear time, and
retain the counterexamples above. All 80 rows remain queued obligations or
identified shared integration requirements.

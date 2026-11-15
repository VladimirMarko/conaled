# Chapter 7 source obligations: 2-3 Trees

Status: **queued; source preparation only**. No Lean implementation, accepted
chapter, or completed theorem is asserted. This note preserves the exact
algorithmic branches, assumptions, mathematical statements, exercise, and
cost model needed for later recovery. It also records a substantive confusion
between internal nodes and stored keys in the printed book. Read with
`../DECISIONS.md` and Chapters 4–6 inventories.

## Pins and source scope

- Book: July 27, 2026 version, Chapter 7 by Tobias Nipkow, printed pp. 85–94
  (PDF pp. 91–100), and Appendix B.3, printed p.349 (PDF p.355).
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  Printed pages 85–86 were rendered and visually checked for the size error.
- Isabelle mirror:
  <https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21>.
  License: BSD-3-Clause, `COPYRIGHT` SHA-256
  `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  This is the inspected companion revision, not an assertion about which
  revision generated the PDF.
- Raw source prefix:
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.
- Shared support: `Cmp`, `Set_Specs`, `Sorted_Less`, and `List_Ins_Del`, with
  exact pins/hashes in Chapters 5–6 inventories. The list-conversion source
  imports `HOL/Library/Time_Commands`; the generated cost recurrences were
  cross-checked against Appendix B.3 rather than inferred from final outputs.
- Reuse inspection: conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` / release v4.35.0.
  No exact 2-3 tree carrier or operations were found by the inspected
  `Tree23`/`tree23`/`TwoThreeTree` and phrase searches in integrated project
  modules or Mathlib. This is a scoped reuse search, not a proof of absence
  from every dependency.

| Source path | SHA-256 | Content inspected |
|---|---|---|
| `src/HOL/Data_Structures/Tree23.thy` | `ee94f404cf06f4b373d9a899623dbce06a38c9560fdcbd6bc8230203e6937ff6` | Carrier, inorder, height, completeness, exponential lower size bound |
| `src/HOL/Data_Structures/Tree23_Set.thy` | `ae1317555ff4e8223d2e047098c62a954f09b8e45e8fd1b1d6522ecdbc888c31` | All insertion/deletion branches, helper laws, completeness, Set interpretation |
| `src/HOL/Data_Structures/Tree23_of_List.thy` | `dcb3ef5eff58d65a4bb95b915870dd527d0bb9dcffd13c9c41e9fb5421ba7240` | Alternating lists, bottom-up conversion, value/completeness/time proofs |

## Measurements and invariant boundaries

Use `E`, `N2(l,a,r)`, and `N3(l,a,m,b,r)` for the three constructors. Let
`nodes t` count each N2 or N3 as **one** internal node, as printed on p.85;
let `keys t = length(inorder t)` count stored labels, so an N3 contributes
two. These are not interchangeable. Let `h` have empty height zero, and C
mean completeness: all children at each node are complete and have equal
height. Let S mean strict `<` sortedness of inorder, so valid set states have
`C t ∧ S(inorder t)`. Duplicates are not allowed by this search invariant.

Most structural completeness/height results do not need S or any order on
labels. Membership and insertion inorder correctness need S but do not need C.
The displayed deletion implementation, however, relies on C even for its
functional correctness: it uses sibling shapes and nonempty replacement
subtrees justified by completeness. Preserve these distinct hypotheses.

The raw insertion cases are exhaustive. Deletion helpers `nodeij` omit some
invalid-shape cases; `split_min E` and `join_adj (T t)` are unspecified in HOL.
Use explicit valid-domain/`Option` realizations, or a typed algorithm with a
checked erasure to the displayed recurrences. Prove every call made from a
valid public state stays in its domain. Avoid a global default label assumption.

### Prospective reuse

- Chapters 5–6 supply lawful comparators, strict ordered-list insertion and
  deletion, Set operations/laws, and `Set_by_Ordered`-style refinement. These
  should be actual shared consumers, with the extra invariant C instantiated.
- Existing `Squares`/`Relational` composition handles semantic refinement;
  resource observations remain separate. A binary-tree carrier does not have
  the source's N3 constructor without an explicit representation translation.
- Chapter 4's accumulator inorder (C04-017–018) is a pattern for a **new
  2-3-tree traversal** with a checked linear count. Its binary carrier theorem
  does not apply unchanged.
- Mathlib `Nat.factorial_le_pow` and
  `Real.sum_log_eq_log_factorial` / `sum_log_add_one_eq_log_factorial`
  (`Mathlib/Analysis/SpecialFunctions/Log/Sum.lean`) support the p.91
  arithmetic. Source base-2 logarithms need the appropriate base-change bridge.
- A fused height-indexed completeness predicate may simplify insertion proofs;
  the companion's `full`/`full_i` alternative is described below. It is not a
  reason to discard the printed `complete` and height observations.

Reuse labels: **R** existing infrastructure, **P** checked adapter needed,
**G** gap, **X** cross-chapter dependency. None is a coverage certificate.

## Carrier, size, height, and Exercise 7.1: pp. 85–86

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-001 | Define the E/N2/N3 carrier and inorder: empty []; N2 emits left, one label, right; N3 emits left, first label, middle, second label, right (p.85; `Tree23.inorder`). | G/P. Labels need no order for these definitions. |
| C07-002 | Define source node size: 0 for E, sum of children's sizes plus 1 for either nonempty constructor (p.85). | G. Do not count N3 as 2 in this source observation. |
| C07-003 | Define stored-key count by inorder length; prove N2 adds 1, N3 adds 2, and `nodes t<=keys t<=2*nodes t`. A leaf-count bridge `externalLeaves t=keys t+1` is useful if employed. | G/support. This distinction is required to repair C07-008 and relate size bounds to abstract set cardinality under S. |
| C07-004 | Height: E=0; N2=`max hl hr+1`; N3=`max hl (max hm hr)+1` (p.85). | G. Make the relation to ordinary max/natural arithmetic explicit. |
| C07-005 | C E; C N2 iff children complete and equally high; C N3 iff three children complete with `hl=hm` and `hm=hr` (p.85). | G. Completeness does not prescribe equal constructor shapes or equal node counts. |
| C07-006 | `C t -> 2^(h t)<=nodes t+1` (p.86; `ht_sz_if_complete`). | G/P. Exact source size is internal-node count. |
| C07-007 | Deduce logarithmic height, e.g. `h t<=log₂(nodes t+1)` after natural/real coercion, with appropriate empty case (p.86). | P/G: source's complexity premise is C and positive log argument; no balance argument is needed for invalid trees. |
| C07-008 | Correct the p.86 every-size claim: for each n there is a complete tree with **n stored keys**, e.g. convert a list of n unit values; for a strict search-tree witness use n distinct natural keys. | G, source correction. This is not the statement with C07-002's node count. The later conversion's inorder/completeness laws provide the constructive witness. |
| C07-009 | Preserve a checked counterexample to the printed internal-node reading: no complete 2-3 tree has exactly 2 internal nodes. | G. Height 0 gives 0; height 1 gives 1; height>=2 has at least 3 by C07-006. Do not silently redefine `nodes` to make the sentence true. |
| C07-010 | Exercise 7.1: define `maxt : Nat -> Tree23 Unit` maximizing nodes at the prescribed height, using only N3 at every nonempty level (p.86). | G. Concrete recurrence: maxt0=E; maxt(n+1)=N3(maxt n,(),maxt n,(),maxt n). |
| C07-011 | Prove `h(maxt n)=n` and `C(maxt n)` to witness that the construction has the prescribed height. | G/support to Exercise 7.1. |
| C07-012 | Exercise 7.1 exact count: `nodes(maxt n)=(3^n-1)/2` using natural subtraction/division (p.86). | G. A useful division-free stronger identity is `2*nodes(maxt n)+1=3^n`. |
| C07-013 | Exercise 7.1 maximality: for **every** tree t, `nodes t <= (3^(h t)-1)/2`; C is not required (p.86). | G. The division-free inequality `2*nodes t+1<=3^(h t)` supplies a clean proof route. |
| C07-014 | Discharge the natural subtraction/division or equivalent real-cast arithmetic used to derive C07-012–013 from the division-free properties (p.86's suggested method). | P/G. The exercise allows either route; exact displayed natural bounds still need a checked bridge if those are the chosen coverage statements. |

## Set search and insertion: pp. 86–88

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-015 | Define empty=E and the set abstraction `set(inorder t)` with valid state `C t ∧ S(inorder t)` (p.86, overall source interpretation `S`). | X Chapters 5–6. Name node size and set cardinality separately. |
| C07-016 | `isin` uses the Chapter 5 empty/N2 equations; at N3, compare x with a first, and only on GT compare with b, selecting l/m/r or equality true (p.86). | G/P. At most two comparator calls per visited nonempty node, one recursive child. |
| C07-017 | `S(inorder t) -> isin t x ↔ x∈set(inorder t)` (`isin_set`). | G/P. No completeness premise is needed for this semantic theorem. |
| C07-018 | Insertion result type `UpI = Eqi Tree23 \| Of Tree23 α Tree23`; projection `treei(Eqi t)=t`, `treei(Of l a r)=N2(l,a,r)` (pp.86–87). | G. The tag records a height effect, not a Boolean validity flag. |
| C07-019 | `ins x E=Of E x E` (Figure 7.1, p.87). | G. Leaf overflow grows the final tree. |
| C07-020 | N2 insertion: recurse on the compared child; Eqi rebuilds N2; overflow is absorbed into N3 in the order given in the insertion matrix below; equality returns Eqi of the old node (p.87). | G. Both left/right overflow cases and both no-overflow cases are required. |
| C07-021 | N3 insertion: recurse in l/m/r by the two-key comparisons; Eqi rebuilds N3; overflow splits into two N2 trees and promotes the correct middle key, as in the matrix; equality to either resident key leaves the node unchanged (p.87). | G. Preserve all three split placements; sorting only the output values would lose the specified algorithm. |
| C07-022 | `S(inorder t) -> inorder(treei(ins x t))=ins_list x (inorder t)` (`inorder_ins`). | G/P. Completeness is not assumed; comparator/order semantics suffice. |
| C07-023 | Public `insert x t=treei(ins x t)` (Figure 7.1). | G. Preserve the result projection and its overflow behavior. |
| C07-024 | Ordered-list and set insertion semantics for public insert, with duplicate suppression (`inorder_insert`, shared list-to-set refinement). | G/P/X. Inorder equality under S is the strong observation; node count need not increase when a new key is inserted. |
| C07-025 | `hi(Eqi t)=h t`, `hi(Of l _ _)=h l` (p.88). | G. It represents the old level only under the established completeness/overflow relationship, not for arbitrary malformed Of values. |
| C07-026 | `C t -> C(treei(ins a t)) ∧ hi(ins a t)=h t` (p.88; `complete_ins`). | G. For Of, completeness of treei also proves left/right equal heights, so the right subtree is not ignored semantically. |
| C07-027 | Recover the stated insertion height effects: Eqi output has old height; Of's two children have old height and its projected tree has old height+1. Thus public insertion preserves height or raises it by one (pp.86–88). | G/P. No claim that every insertion raises height or even changes node count. |
| C07-028 | `C t -> C(insert a t)` (p.88; `complete_insert`). | G. Together with C07-024 gives validity preservation. |
| C07-029 | If using the companion's alternative proof, relate indexed `full n t` to `C t ∧ h t=n`, define `full_i n (Eqi t)=full n t` and `full_i n (Of l a r)=full n l ∧ full n r`, and prove `full_i_ins`. | P/G, optional proof route. Do not require both independent proof scripts unless they become distinct reusable consumers; do retain the printed theorem via the bridge. |

### Insertion overflow matrix (Figure 7.1)

The selected recursive result in each row is `Of(u,c,v)`; other children and
keys are the original node's. These rows fix the source's exact rebuilding.

| Original node and selected child | Returned result |
|---|---|
| N2(l,a,r), left | `Eqi(N3(u,c,v,a,r))` |
| N2(l,a,r), right | `Eqi(N3(l,a,u,c,v))` |
| N3(l,a,m,b,r), left | `Of(N2(u,c,v),a,N2(m,b,r))` |
| N3(l,a,m,b,r), middle | `Of(N2(l,a,u),c,N2(v,b,r))` |
| N3(l,a,m,b,r), right | `Of(N2(l,a,m),b,N2(u,c,v))` |

## Deletion and completeness: pp. 88–91

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-030 | Deletion result type `UpD=Eqd Tree23 \| Uf Tree23`; `treed` erases either tag. Eqd reports unchanged height, Uf one level less (p.88). | G. Uf cannot arise from a valid input of height zero in the proved height law. |
| C07-031 | Implement all three `node21` equations: changed left child of an N2, with no underflow, 2-node sibling, or 3-node sibling (Figure 7.3, p.90). | G; exact matrix below. Partial source shape when Uf meets E must be excluded/proved unreachable. |
| C07-032 | Implement all three `node22` equations, the right-child counterpart (p.90). | G. Preserve source key placement, not a guessed symmetric formula. |
| C07-033 | Implement all three `node31` equations for changed left child of N3 (p.90). | G. The source always returns Eqd here. |
| C07-034 | Implement all three `node32` equations for changed middle child of N3, using the right sibling to repair underflow (p.90). | G. It does not inspect the left sibling for a preferred rebalance. |
| C07-035 | Implement all three `node33` equations for changed right child of N3, using the middle sibling (p.90). | G. |
| C07-036 | Prove the five inorder-rebuilding laws (`inorder_node21`–`33`), using a positive-height sibling as listed below. | G/P. These laws do not need S or C beyond their actual shape-domain premise. |
| C07-037 | `split_min` (Figure 7.2, p.89): bottom N2 returns first key with `Uf E`; bottom N3 returns first key with `Eqd` of the remaining singleton N2; otherwise recurse into l and reconstruct using node21 or node31. | G. Valid domain: nonempty complete tree. Source partiality also matters on incomplete trees whose l is empty but other children are not. |
| C07-038 | `del` base cases: E returns Eqd E; bottom N2 removes matching key with Uf E, otherwise unchanged; bottom N3 removes a matching first/second key to a singleton N2, otherwise unchanged, always Eqd (p.89). | G. Both comparisons and no-match branch are required. |
| C07-039 | Internal N2 deletion: LT uses node21 on del l, GT uses node22 on del r, EQ obtains successor from r and passes its UpD result to node22 (p.89). | G. Completeness and non-bottom shape ensure r is nonempty in EQ. |
| C07-040 | Internal N3 deletion: LT-a uses node31 on l; EQ-a replaces from m and uses node32; between a/b uses node32 on del m; EQ-b replaces from r and uses node33; GT-b uses node33 on del r (p.89). | G. Preserve all five routing cases. |
| C07-041 | Public `delete x t=treed(del x t)` (p.89). | G. The tag is necessary during recursion although discarded at the root. |
| C07-042 | Under C t and h t>0, if split_min returns `(x,u)`, then `x::inorder(treed u)=inorder t` (`split_minD`). | G/P. Unlike generic Chapter 5 split-min, this helper genuinely uses completeness to justify its rebuilding. |
| C07-043 | Under `C t ∧ S(inorder t)`, `inorder(treed(del x t))=del_list x (inorder t)` and the public-delete corollary (`inorder_del`, `inorder_delete`). | G/P. Do not drop C by imitating the unbalanced BST theorem. |
| C07-044 | Under valid state, delete represents set difference by `{x}`, and preserves strict inorder via the shared del_list theorem. | G/P/X. Completeness preservation is separate below. |
| C07-045 | `hd(Eqd t)=h t`, `hd(Uf t)=h t+1` (p.91). | G. |
| C07-046 | Prove all five helper completeness laws: complete projected changed child and complete unchanged children, with their heights equal to the changed child's hd, imply complete projected reconstruction (p.91 plus the explicitly omitted analogous cases). | G. Exact source assumptions are in the helper-law matrix below. |
| C07-047 | Prove all five hd reconstruction identities under a positive-height repaired-against sibling (p.91; `height'_node21`–`33`). | G. These formulas use max of old/reported child heights and do not assume equality/completeness. |
| C07-048 | If split_min t=(x,u), C t, and h t>0, prove `hd u=h t` (p.91; `height_split_min`). | G. |
| C07-049 | Under the same premises, prove `C(treed u)` (p.91; `complete_split_min`). | G. |
| C07-050 | `C t -> hd(del x t)=h t` (p.91; `height_del`). Deduce public deletion preserves height or lowers it by one, with impossible negative-height case excluded. | G. No order hypothesis needed. |
| C07-051 | `C t -> C(treed(del x t))` (p.91; `complete_tree_d_del`). | G. |
| C07-052 | `C t -> C(delete x t)` (p.91; `complete_delete`). | G. |
| C07-053 | Instantiate the complete seven-law Set specification with extra invariant C and abstraction set∘inorder (`Tree23_Set.S`). | G/P/X. Functional correctness is omitted from the book's exposition by reference to Chapter 5, not omitted from requested formal coverage. |
| C07-054 | Formalize the p.86 logarithmic-operation claim under its stated constant-time-per-node model: instrument the actual search/insert/delete paths and helper work, prove `work<=A*h t+B`, then combine with C07-006–007. | G. Comparator cost must be explicitly constant in this abstract model. Deletion's successor descent and retracing repairs are part of the count. No logarithmic guarantee for invalid/incomplete inputs or variable-cost comparisons is automatic. |

### Underflow reconstruction matrix (Figure 7.3)

Each helper also has an Eqd equation that simply rebuilds the original N2 or
N3 with the changed subtree and returns Eqd. The following are its two Uf
cases. Labels are schematic bound variables, retaining source order.

| Call pattern | Returned result |
|---|---|
| `node21 (Uf t1) a (N2(t2,b,t3))` | `Uf(N3(t1,a,t2,b,t3))` |
| `node21 (Uf t1) a (N3(t2,b,t3,c,t4))` | `Eqd(N2(N2(t1,a,t2),b,N2(t3,c,t4)))` |
| `node22 (N2(t1,b,t2)) a (Uf t3)` | `Uf(N3(t1,b,t2,a,t3))` |
| `node22 (N3(t1,b,t2,c,t3)) a (Uf t4)` | `Eqd(N2(N2(t1,b,t2),c,N2(t3,a,t4)))` |
| `node31 (Uf t1) a (N2(t2,b,t3)) c t4` | `Eqd(N2(N3(t1,a,t2,b,t3),c,t4))` |
| `node31 (Uf t1) a (N3(t2,b,t3,c,t4)) d t5` | `Eqd(N3(N2(t1,a,t2),b,N2(t3,c,t4),d,t5))` |
| `node32 t1 a (Uf t2) b (N2(t3,c,t4))` | `Eqd(N2(t1,a,N3(t2,b,t3,c,t4)))` |
| `node32 t1 a (Uf t2) b (N3(t3,c,t4,d,t5))` | `Eqd(N3(t1,a,N2(t2,b,t3),c,N2(t4,d,t5)))` |
| `node33 t1 a (N2(t2,b,t3)) c (Uf t4)` | `Eqd(N2(t1,a,N3(t2,b,t3,c,t4)))` |
| `node33 t1 a (N3(t2,b,t3,c,t4)) d (Uf t5)` | `Eqd(N3(t1,a,N2(t2,b,t3),c,N2(t4,d,t5)))` |

### Exact helper-law domains

Write `D u=treed u`, `H u=hd u`, and `I t=inorder t` in this table.
The listed positive sibling premise belongs to the inorder and height laws;
the separate completeness premises make valid reconstructed inputs automatically.

| Helper call | Inorder / hd law premise | Inorder result | hd result | Completeness premises |
|---|---|---|---|---|
| `node21 u a r` | `h r>0` | `I(D u)++[a]++I r` | `max(H u)(h r)+1` | C r, C(D u), h r=H u |
| `node22 l a u` | `h l>0` | `I l++[a]++I(D u)` | `max(h l)(H u)+1` | C l, C(D u), h l=H u |
| `node31 u a m b r` | `h m>0` | `I(D u)++[a]++I m++[b]++I r` | `max(H u)(max(h m)(h r))+1` | C(D u), C m, C r, H u=h r, h m=h r |
| `node32 l a u b r` | `h r>0` | `I l++[a]++I(D u)++[b]++I r` | `max(h l)(max(H u)(h r))+1` | C l, C(D u), C r, h l=h r, H u=h r |
| `node33 l a m b u` | `h m>0` | `I l++[a]++I m++[b]++I(D u)` | `max(h l)(max(h m)(H u))+1` | C l, C m, C(D u), h l=H u, h m=H u |

The source's unnumbered **companion-only** exercise observes that the bottom
patterns of `del`/`split_min` need test only one child for E: under C, all other
children then have height zero and hence are E. This is a possible separately
checked optimized realization; it must have a valid-input value/height bridge
to the full displayed patterns. It is not already the printed algorithm's
implementation, and it is not necessary to introduce an unsafe partial match.

## 7.3 Repeated insertion and the linear conversion goal: p. 91

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-055 | `sum_{i=1..n} log₂ i = log₂(n!)` (p.91). | R/P: existing real logarithm/factorial sum lemmas plus base change; state casts and n=0 empty-sum convention deliberately. |
| C07-056 | `n!<=n^n`, hence `log₂(n!)<=n*log₂ n` for n>=1 (p.91). | R/P: `Nat.factorial_le_pow`; logarithmic monotonicity requires positive arguments. |
| C07-057 | `n^n <= (n!)^2`, via `n<=i*(n+1-i)` for 1<=i<=n and multiplying all factors; hence `(n*log₂ n)/2<=log₂(n!)` for n>=1 (p.91). | G/P. Preserve the lower bound rather than proving only big-O. |
| C07-058 | Deduce `log₂(n!)` and the sum of logs are Θ(n log n) as n tends to infinity (p.91). | P/G: exact two-sided estimates give a stronger witness; n=0/1 are not grounds for dividing by log n. |
| C07-059 | Correctly qualify repeated-insertion Θ(n log n): when n distinct keys are inserted and the source model charges the full complete-tree path, cardinality grows each time and height is Θ(log of key count). Prove the stated total bound in this domain, or formulate the source's explicit hypothesis that each insertion costs proportional to the log of the growing size. | G, scope correction. A logarithmic **upper** bound alone gives only O(n log n), not the claimed lower bound. |
| C07-060 | Preserve the unqualified claim's counterfamily: inserting n repetitions of one key repeatedly reaches the same singleton tree and performs only constant work per repetition, so total work is linear in n. | G. The semantic and counted recurrence witnesses should be checked; neither set size nor tree height grows with these duplicates. |
| C07-061 | Account for the p.91 comparison-to-sorting conclusion: a correct search-tree construction on distinct input keys followed by linear inorder is a comparison sorter, so its comparison complexity cannot beat the appropriate comparison-sorting lower bound. | G/P, explicit model. State distinct input/permutation and comparison-decision model; no universal lower bound is implied for restricted integer keys, pre-sorted inputs, or a set operation discarding duplicates. If using a known lower-bound theorem, record its exact source/assumptions. |
| C07-062 | Supply a linear-time 2-3-tree inorder implementation used in C07-061, with value correspondence to displayed inorder and actual linear cost in node/key count. | G/X: adapt Chapter 4's accumulator traversal. The direct append-based inorder does not inherit linear runtime merely from equal output. |

## 7.3 Bottom-up list conversion: pp. 91–94

This algorithm preserves **the entire input list**, including order and
duplicates. It is a shape balancer, not a sorter or duplicate eliminator.
A strict search tree follows only from strict sortedness of the input. The
algorithm never compares labels; a linear order is unnecessary for conversion,
its inorder result, completeness, and timing.

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-063 | Define nonempty alternating sequences `Tree23s = T Tree23 \| TTs Tree23 α Tree23s`, starting and ending with a tree (p.92). | G. A representation by a list of pairs plus final tree may be used with a checked isomorphism; no malformed even-ending sequence should enter the core recurrence. |
| C07-064 | `len(T t)=1`, `len(TTs t a ts)=len ts+1`; prove positive length and `not_T ts -> len ts>=2` (pp.92–93; `len_ge_1`, `len_ge2`). | G/P. len counts tree slots, not all alternating entries and not stored labels. |
| C07-065 | Define `trees` as the set of constituent trees and `inorder2` as their inorder lists interleaved with the separating labels (p.92). | G. `trees` is a set observation, while `inorder2` retains order/multiplicity. |
| C07-066 | `join_adj`: two tree slots become one N2; three become one N3; with at least four slots, combine the first two into N2, retain the next separator, and recurse on the remainder starting at the third tree (p.93). | G. The special final N3 case is essential to preserve completeness for odd lengths; do not leave a final unjoined tree at the old level. |
| C07-067 | `not_T ts := ¬∃t, ts=T t` is the valid domain of join_adj (p.93). Prove every join_all call meets it; adapt the omitted singleton case explicitly. | G. No source behavior is promised for join_adj(T t). |
| C07-068 | (7.1): `not_T ts -> len(join_adj ts)<=len ts/2` using natural division (p.93; `len_join_adj_div2`). | G. The exact equality also follows from this recurrence and may be proved as a useful stronger lemma, but the printed bound is the required statement. |
| C07-069 | Derive `not_T ts -> len(join_adj ts)<len ts`; source auxiliary `len(join_adj(TTs t a ts))<=len ts` (`len_join_adj1`, `len_join_adj2`). | G/P. This is actual termination evidence, not a fuel cutoff. |
| C07-070 | `join_all(T t)=t`; otherwise recurse on join_adj; establish well-founded termination by len (p.92). | G. The measure ignores tree size/height, which increase as slots combine. |
| C07-071 | `leaves []=T E`; `leaves(a::as)=TTs E a (leaves as)` (p.93). Prove `len(leaves as)=len as+1`. | G. Empty input is included. |
| C07-072 | `tree23_of_list as=join_all(leaves as)` (p.93). | G. Preserve this bottom-up implementation; repeated balanced insert is a different algorithm and asymptotic cost. |
| C07-073 | `not_T ts -> inorder2(join_adj ts)=inorder2 ts` (p.93; `inorder2_join_adj`). | G/P. |
| C07-074 | `inorder(join_all ts)=inorder2 ts` (p.93; `inorder_join_all`). | G. |
| C07-075 | `inorder2(leaves as)=as` (`inorder2_leaves`, supporting p.93). | G/P. |
| C07-076 | `inorder(tree23_of_list as)=as` (p.93; source `inorder`), hence its key count is exactly input length. | G. This proves C07-008 with an explicit list witness; it does not prove its node count equals input length. |
| C07-077 | If every constituent tree is complete with height n, and not_T ts, then every tree in join_adj ts is complete with height n+1 (p.93; `complete_join_adj`). | G. Equal initial heights are essential; completeness of each constituent alone is insufficient. |
| C07-078 | If all constituent trees are complete at one common height, join_all ts is complete (p.93; `complete_join_all`). | G. The final height need not be specified by this theorem. |
| C07-079 | Every tree appearing in leaves as is complete with height zero (p.94; `complete_leaves`). | G/P. |
| C07-080 | `C(tree23_of_list as)` for all lists (p.94; source `complete`). | G. No sortedness premise. |
| C07-081 | Under S as, the conversion is a valid 2-3 search-tree representation of exactly that set; without S it remains a complete shape with exact inorder (p.91's intended sorted-input use). | G/P/X. A nondecreasing list with duplicate keys does not give the strict set invariant. |

### Exact conversion time functions: Appendix B.3 and p.94

These counts follow the Chapter 1 call-count convention, with constructor
assembly and primitive projections uncharged and the displayed nonrecursive
wrapper expanded. They are not comparison counts: the conversion performs no
key comparisons. Tree traversal inside the specification `inorder2` is not
executed by the construction and must not be charged as though it were.

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C07-082 | `Tjoin_adj` is 1 for the two-slot and three-slot base patterns; the longer pattern is `Tjoin_adj remainder+1` (Appendix B.3). | G. Same valid domain as join_adj; instrument the actual source branches or prove a recurrence correspondence. |
| C07-083 | `Tjoin_all(T t)=1`; for non-T, `Tjoin_all ts=Tjoin_adj ts+Tjoin_all(join_adj ts)+1` (Appendix B.3). | G. Both the pass and recursive joining call are charged. |
| C07-084 | `Tleaves []=1`, `Tleaves(a::as)=Tleaves as+1` (Appendix B.3). | G. Includes terminating empty call. |
| C07-085 | `Ttree23_of_list as=Tleaves as+Tjoin_all(leaves as)` (Appendix B.3). | G. No extra +1 wrapper charge in the pinned equation; state any alternate instrumentation through an explicit count adapter. |
| C07-086 | (7.2): `not_T ts -> Tjoin_adj ts<=len ts/2` (p.94; `T_join_adj`). | G. The recurrence actually permits an exact equality if useful; source only needs this bound. |
| C07-087 | `Tjoin_all ts<=2*len ts` (p.94; `T_join_all`), proved by join_all computation induction using C07-068 and C07-086. | G. Include singleton base and natural floor arithmetic; the prose's induction-function name is corrected below. |
| C07-088 | Exact `Tleaves as=len as+1` and `len(leaves as)=len as+1` (`T_leaves`, `len_leaves`). | G/P. Two different observations coincide here; preserve both reasons. |
| C07-089 | Final exact affine upper bound `Ttree23_of_list as<=3*len as+3` (p.94; `T_tree23_of_list`). | G. Empty input's actual count is 2 under B.3, safely below 3. |
| C07-090 | Connect C07-089 to an actual executable construction instrumented with this call model, proving value projection equals tree23_of_list; derive linear asymptotic time with the constant-time constructor/primitive assumptions named. | G/P. A time function with no branch/value connection or an extensionally equal insertion-based tree is insufficient. |

## Corrections and checked-negative targets

1. **Every size, p.86.** With p.85's stated size function, the every-n
   completeness assertion is false at n=2. This is visually confirmed in the
   PDF and consistent with the companion's `ht_sz_if_complete`. The corrected
   every-key-count theorem is constructive via list conversion. Keep both
   C07-008 and C07-009. Neither changing the size definition nor treating the
   false sentence as an axiom is acceptable.
2. **Repeated insertion lower bound, p.91.** The literal Θ claim needs growing
   distinct cardinalities or an explicit lower-bound hypothesis on each
   insertion. Repeated equal keys stop at the singleton root. Formalize the
   corrected distinct-input/full-path claim and a linear repeated-key family;
   the unconditional logarithmic upper bound alone cannot establish Θ.
3. **Wrong induction name, p.94.** The sentence deriving the bound for
   Tjoin_all says to induct on the computation of join_adj. The displayed
   inductive hypothesis is about join_all of the shortened sequence; the
   companion proves `T_join_all` by `join_all.induct`. Preserve this harmless
   proof-description correction instead of inventing a different recurrence.
4. **Completeness is needed for deletion semantics.** The missing helper
   patterns and the base-case ordering make the source meaningful on complete
   inputs. `split_minD` and `inorder_delete` explicitly retain C. Importing the
   unbalanced-tree premise set would make a stronger statement not supported
   by these equations.
5. **No equality between node count and number of keys.** A bottom N3 has one
   internal node and two keys. Inserting a second distinct key into a singleton
   N2 can leave node count at one. Exercise 7.1 counts nodes; list conversion
   preserves key count; abstract set cardinality equals key count only under
   strict sortedness. Keep these as distinct observations and bridges.
6. **The faster traversal is a separate realization.** The source's naive
   append-based inorder can do more than linear copying. The p.91 reduction
   requires a linear traversal such as an accumulator implementation, with its
   own erasure/cost proof. Mathematical equality of inorder results does not
   change operational cost.
7. **Ordering does not follow from complete shape.** `tree23_of_list [1,1]`
   has a bottom N3 with equal keys, so is complete but not a strict search
   tree. The source's constructor accepts arbitrary lists; no hidden sorting
   or deduplication occurs.

All negative examples above are future Lean witness requirements when used to
resolve a false or overstrong source statement. Mathematical reasoning in this
inventory is not a substitute for the checked counterexample at acceptance.

## Coverage map and handoff

| Source item | Inventory witnesses |
|---|---|
| Definitions and exponential height/size bound, pp.85–86 | C07-001–009 |
| Exercise 7.1, all requests | C07-010–014 |
| Figure 7.1 insertion | C07-018–028 and five overflow matrix rows |
| Figure 7.2 deletion/split-min | C07-030, C07-037–044 |
| Figure 7.3 all 15 helper equations | C07-031–035, Eqd convention, ten Uf matrix rows |
| p.91 seven displayed preservation laws and omitted helper analogues | C07-045–052 and exact helper-law matrix |
| Full Set implementation and logarithmic-operation conclusion | C07-015–017, C07-024, C07-044, C07-053–054 |
| p.91 factorial/Θ argument and conversion-to-sorting discussion | C07-055–062 |
| Alternating-sequence construction and value/completeness results | C07-063–081 |
| (7.1), (7.2) | C07-068, C07-086 |
| Appendix B.3 and final affine time bound | C07-082–090 |

There are no named theorems/lemmas in the printed chapter and only one numbered
exercise. The chapter notes' historical attributions and implementation-source
citations are provenance, not a requirement to port every cited paper. All
mathematical claims actually made in the chapter, including unnumbered
complexity conclusions, remain accounted for here. Later acceptance must attach
checked declarations, domain adapters, source corrections, concrete Set clients,
and exact validation/review evidence; source inventory alone closes none of
these obligations.

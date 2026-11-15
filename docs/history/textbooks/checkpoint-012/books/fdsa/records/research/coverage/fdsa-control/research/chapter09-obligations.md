# Chapter 9 source obligations: AVL Trees

Status: **queued; source preparation only**. This note inventories the
height-cache implementation, the balance-factor optimization, all seven
exercises, Lemmas 9.1–9.2, Corollary 9.3, Theorems 9.4–9.7, and the
generalized-height claim in the chapter notes. It does not assert a Lean
implementation, acceptance, or completed coverage. Read with
`../DECISIONS.md` and the Chapters 4–6 inventories.

## Pins and source scope

- Book: July 27, 2026 version, Chapter 9 by Tobias Nipkow, printed pp.105–116
  (PDF pp.111–122).
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  Printed pp.111 and 116 were rendered and visually checked to resolve the
  exponent in Exercise 9.1 and the exact restrictions of Exercises 9.6–9.7.
- Isabelle mirror:
  <https://github.com/isabelle-prover/mirror-isabelle/commit/f86f290225eebcc52c1ae7dba2e098f405f51c21>.
  BSD-3-Clause, `COPYRIGHT` SHA-256
  `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  The inspected revision is explicitly pinned; it is not asserted to be
  the revision used to build the PDF.
- Raw source prefix:
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.
- Shared theories: `Tree2`, `Tree`, `Tree_Real`, `Balance`, `Cmp`, `Isin2`,
  `Sorted_Less`, `List_Ins_Del`, and `Set_Specs`, pinned and described in
  Chapters 4–6. The height proof additionally imports `HOL-Number_Theory.Fib`.
- Reuse search: conaled baseline
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679` / release v4.35.0;
  Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`.
  Scoped searches for AVL, height-balanced, balance-factor, and avl0 found
  no matching AVL implementation in integrated conaled modules or the
  inspected Mathlib/Batteries source trees. The binary carrier, Fibonacci
  arithmetic, golden ratio, logarithms, and abstract Set infrastructure
  have concrete reuse described below. Red-black/size-balanced libraries
  do not by themselves implement the chapter's AVL recurrences.

| Companion path | SHA-256 | Inspected content |
|---|---|---|
| `src/HOL/Data_Structures/AVL_Set_Code.thy` | `423ea6e7e5d415a9d279ca24c48ce45b2d1bd60f591fae50a00ffa6e852cb2e3` | Height-cached algorithms and their independent inorder proofs; authors Tobias Nipkow and Daniel Stüwe |
| `src/HOL/Data_Structures/AVL_Set.thy` | `282cf829b7efc3421428cbe7ee3e590492d45ed0b8c7b80eff1ae3c57630f3b9` | AVL invariant, simultaneous height/preservation proofs, Set interpretation, Fibonacci/real-log bounds |
| `src/HOL/Data_Structures/AVL_Bal_Set.thy` | `f347f9d6f788e1a057e82c4e5fd0a274cfb95593d1a0fc6094e00ceef83bdcae` | Printed balance-factor algorithms, change detection, helper/domain/list proofs and Set interpretation |
| `src/HOL/Data_Structures/AVL_Bal2_Set.thy` | `fa10708db83b01b9727a0366e23b5c558574fd922facbd69dca8cdb20a0f78e3` | An additional Same/Diff return-tag variant; inspected to prevent misidentification as an exercise solution |

`AVL_Bal2_Set` is **not** the Exercise 9.7 four-constructor tree, and its
name does not mean generalized tolerance d=2. It retains a color-like
balance annotation and reports height changes in a separate result tag.
That unprinted alternative is available background, not a replacement
for either printed implementation or the exercise's requested carrier.

### Cited generalized-height source

Chapter Notes p.116 and bibliography p.362 cite Manuel Eberl's
*Height Bounds for Height-Balanced Trees*, AFP, July 7, 2026:
<https://isa-afp.org/entries/Height_Balanced_Tree_Bounds.html>.
The dated archive preceding the manuscript date is
<https://isa-afp.org/release/afp-Height_Balanced_Tree_Bounds-2026-07-07.tar.gz>,
SHA-256 `3ff0cf90941fc6c77e6377ef86238fef5d27af512182ea8196f0377579088737`.
The entry labels it BSD; the fetched AFP license at
<https://isa-afp.org/LICENSE> is the three-clause BSD license, SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`.
The entry HTML inspected has SHA-256
`9bdc23eaad9ce1b678c68b3b73b3985dec66b6254e09f5af1c24ec5d3a0b6c5d`.

| Archive source | SHA-256 | Scope inspected |
|---|---|---|
| `HBT_Bounds.thy` | `45abbbf6bc06cb63da152c2c485f5b8ea3c0bd2e4b4a2fee6ac01c1ad54ec793` | Generalized invariant, exact minimum-leaf recurrence and witnesses, exponential and logarithmic bounds; later asymptotic development inventoried by declaration names only |
| `HBT_Fun.thy` | `9eb9c0d1360f7ae1865d418efa8638405fb483a93c18e4fe96515f7cbe10fb84` | Pinned dependency, not independently reviewed in full |
| `HBT_Lemma_Bucket.thy` | `8bc8f10166b560e37429303ca9aef561cc52ec7e501aefd829750e4cdd16bc90` | Pinned dependency, not independently reviewed in full |

The book asserts generalized logarithmic height but does not reproduce
the cited paper's complete optimal-constant/asymptotic theory. A checked
sufficient logarithmic bound answers that book claim; this citation does
not silently turn every theorem in the external AFP entry into a new
chapter requirement. The source's relevant formal declarations and
several prose errors are recorded at the end of this note.

## Measurements, invariants, and domain distinctions

Write E/N for empty/binary-node constructors; I erases the outer annotation
and computes inorder; h is **actual structural height**, with h E=0;
`nodes` counts internal nodes, and `leaves=nodes+1`. S means strict
sortedness of inorder, as in the shared Set-by-Ordered refinement.

Use Aht for the height-annotated AVL invariant, A0 for the unannotated
shape invariant, and Abal for the balance-factor invariant. None contains
search ordering. Aht includes both correct height caches and the recursive
condition `abs((h l : Int)-(h r : Int))<=1`. Abal's tags record the exact
one-level relationship. Natural subtraction alone would lose the negative
side of the difference; alternatively use the two equivalent natural
inequalities `h l<=h r+1` and `h r<=h l+1`.

The two algorithm families have different raw-domain boundaries:

- **Height caches:** apparently omitted patterns in balL/balR are
  unreachable even for incorrectly cached trees. A rotation test implies
  the heavy tree has cached height at least 2, hence is nonempty because
  ht E=0; a double-rotation test makes the middle tree's cached height
  positive, hence nonempty. This explains the source's unconditional
  inorder lemmas. Correctness of the caches is needed for structural
  balance/height results, not for these shape guards.
- **Balance factors:** old-root Lh/Rh tags can demand a rotation on a
  malformed empty child, and rot2 requires a nonempty middle subtree.
  The companion's semantic lemmas use appropriate nonempty/AVL premises.
  Do not transplant the unconditional cache-family claims to this family.

Both split_max functions are unspecified on E in HOL. Use a nonempty
domain or explicit failure interface without imposing a global default
payload, and prove public calls remain in the domain. Boolean is_bal is
also unspecified on E in the printed source; a chosen total Boolean
extension is acceptable only with a proof that reachable operation tests
do not depend on that choice. Empty tests inspect shape and need no
decidable equality on payloads.

Reuse labels: **R** existing infrastructure, **P** checked bridge needed,
**G** gap, **X** cross-chapter dependency. They are preparation labels,
not proof certificates.

## Height-cache foundations and logarithmic height: pp.105–107

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C09-001 | Use the shared binary tree labelled by `(payload,Nat)` for tree_ht (p.105; `AVL_Set_Code`). | R/P Chapter 4 and Mathlib BinaryTree. Preserve which component is semantic payload. |
| C09-002 | `ht E=0`; ht of a nonempty node is its stored natural cache (p.105). | P. It is not actual h on arbitrary malformed trees. |
| C09-003 | Smart constructor `node l a r=N(l,(a,max(ht l)(ht r)+1),r)` (p.105). | R/P Chapter 4 augmentation. It reads child root caches in constant local work under the declared arithmetic/access model. |
| C09-004 | Smart construction has unconditional inorder `I l ++ [a] ++ I r` and actual height `max(h l)(h r)+1`; annotation erasure preserves shape, height, nodes, and leaves (`height_node` and support). | R/P Chapter 4 observation lemmas. Correctness of its stored cache needs correct child caches. |
| C09-005 | Define Aht exactly: E valid; a node's signed child-height difference has absolute value ≤1, its cache equals actual node height, and both children are valid (p.105; `AVL_Set.avl`). | G/P. Search ordering remains separate. |
| C09-006 | Aht t implies `ht t=h t` (`ht_height`); expose the local smart-constructor preservation law under valid children and the child-height balance condition. | P/G. Keep actual height in specifications and cached access in executable branches. |
| C09-007 | Define A0 by the same recursive height-balance condition without caches, and relate Aht to A0 after erasure together with recursive cache correctness (pp.105,111). | G/support. This is the shared invariant bridge for Exercises 9.2–9.6. |
| C09-008 | Empty is E; search is the shared augmented-tree `isin`, ignoring the cache and following one comparator-selected child (§9.2, companion imports/interpretation). | R/P Chapters 5–6. |
| C09-009 | Under S, search agrees with membership in set(I t); empty has empty inorder and is Aht. | R/P. No Aht assumption is needed for the search-value theorem. |
| C09-010 | Use Fibonacci numbers with F0=0, F1=1, F(n+2)=F(n+1)+F n (p.106). Supply a two-step computation-induction rule matching the source proof method. | R `Nat.fib`, `fib_zero`, `fib_one`, `fib_add_two`, `Nat.twoStepInduction`; orient the summands by commutativity as needed. The standard executable fib is optimized, so its costs are not those of naive double recursion. |
| C09-011 | Lemma 9.1: `Aht t -> F(h t+2)<=leaves t` (p.106; `avl_fib_bound`, alternative proof `avl_fib_bound_auto`). | P/G. `Nat.fib_mono` supports the child-height comparison. No S hypothesis. |
| C09-012 | Let φ=(1+sqrt 5)/2; prove/reuse φ>1, φ<2, φ²=φ+1, and the natural-power recurrence used by the exponential argument (p.106). | R `Real.goldenRatio`, `one_lt_goldenRatio`, `goldenRatio_lt_two`, `goldenRatio_sq`; all in the pinned Mathlib GoldenRatio module. |
| C09-013 | Lemma 9.2: for every natural n, `φ^n <= (F(n+2):Real)` (p.106; `fib_lowerbound`), with bases n=0 and n=1 and the two-step recurrence. | P/G short arithmetic proof from C09-010/012. No exact existing theorem with this signature was found by the scoped search; Binet identities are available but unnecessary. |
| C09-014 | Combine the preceding inequalities to get `Aht t -> φ^(h t)<=leaves t` (`avl_size_lowerbound`). | P/G. Natural/real casts and positive leaves must be explicit. |
| C09-015 | Corollary 9.3: `Aht t -> (h t:Real) <= (1/log₂ φ)*log₂(leaves t)` (pp.106–107; `avl_height_upperbound`). | R/P log monotonicity/base change and G invariant bridge. φ>1 is the essential base condition. |
| C09-016 | Preserve the p.107 approximate coefficient by proving a checked rational enclosure, e.g. `1440/1000 < 1/log₂ φ < 1441/1000`, or equivalent bounds that justify rounding to 1.44 at the displayed precision. | P/G, mandatory numerical correspondence. Keep the exact coefficient in C09-015; neither `1/log₂ φ=1.44` nor `1/log₂ φ<=1.44` is the source's valid theorem. Use exact real/rational reasoning rather than an unchecked floating-point evaluation. The listed enclosure remains a proof target, not a result established by this inventory. |
| C09-017 | Retain the introductory minimum-leaf claim: the minimum at height n is F(n+2), with M0=1, M1=2, and `M(n+2)=M(n+1)+M n` (p.106). | X Exercise 9.2, especially C09-048–050. A lower bound plus a matching Fibonacci-tree witness formalizes the minimum without introducing an underspecified minimum over an empty set. |

## Height-cached insertion and deletion: pp.107–111, Figures 9.1–9.3

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C09-018 | Implement balL with the exact cached-height threshold, single/double rotation condition, and nested smart construction shown in Figure 9.1 (p.108; table below). | G/P. The algorithm reads ht, not actual h. |
| C09-019 | Implement the mirror balR of Figure 9.2, with its exact tie convention `ht B<=ht C` for the single rotation (p.109). | G/P. Equality belongs to the single-rotation branch on both sides. |
| C09-020 | Prove the omitted heavy-child and middle-child patterns cannot be reached from the cache tests for **all** inputs, since ht E=0 and caches are natural. Supply a total Lean realization with the same reachable equations. | P/G. This domain argument does not need Aht. |
| C09-021 | Unconditionally, I of balL or balR is `I l ++ [a] ++ I r` (`AVL_Set_Code.inorder_balL`, `inorder_balR`). | G/P list associativity and shape cases. No ordering or cache validity premise. |
| C09-022 | If Aht l, Aht r, and `h l=h r+2`, then `h(balL l a r)∈{h r+2,h r+3}` (`height_balL`). | G/P. Both possible output heights matter for insertion and deletion. |
| C09-023 | If Aht l, Aht r, and `h r=h l+2`, then `h(balR l a r)∈{h l+2,h l+3}` (`height_balR`). | G/P. |
| C09-024 | Under Aht children and absence of the relevant exact +2 imbalance, either balancer has actual height `1+max(h l)(h r)` (`height_balL2`, `height_balR2`). | G/P. The cache/actual-height bridge justifies selecting the fallback branch. |
| C09-025 | `Aht l ∧ Aht r ∧ (h r-1<=h l) ∧ (h l<=h r+2) -> Aht(balL l a r)` (p.110; `avl_balL`). | G. Here subtraction is natural truncated subtraction, exactly as in the source; equivalently `h r<=h l+1`. |
| C09-026 | Mirror helper law: Aht children, `h l-1<=h r`, and `h r<=h l+2` imply Aht of balR (p.110; `avl_balR`). | G. Do not require both children to be already within one level: the helper repairs a two-level difference. |
| C09-027 | Insertion E gives a singleton cached with 1. At a node, LT uses balL of the recursively inserted left child; EQ returns the original labelled node; GT uses balR of the right insertion (p.107). | G/P shared comparator/list insertion. |
| C09-028 | Under S, `I(insert x t)=ins_list x (I t)` (`AVL_Set_Code.inorder_insert`). | G/P. This functional theorem does not require Aht, unlike its balance-factor counterpart. |
| C09-029 | Theorem 9.4: Aht t implies Aht(insert x t) and `h(insert x t)∈{h t,h t+1}` (p.107; `avl_insert`, `avl_insert_auto`). | G. Preserve the simultaneous invariant/height conclusion; proving only AVL preservation misses the inductive contract. |
| C09-030 | split_max of a nonempty node returns (l,a) when r=E; otherwise recursively gets (r',a') from r and returns `(balL l a r',a')` (Figure 9.3, p.109). | G. This chapter chooses the **left-subtree maximum**, unlike the preceding chapter's right-subtree minimum. |
| C09-031 | Make split_max's nonempty domain/failure explicit and prove recursive and deletion calls meet it. | P/G. Do not require an inhabited payload for an unreachable E result. |
| C09-032 | If nonempty t and split_max t=(t',a), then `I t' ++ [a]=I t` (`AVL_Set_Code.inorder_split_maxD`). | G/P. No S or Aht premise; maximality under S follows. |
| C09-033 | Aht t and t≠E imply Aht of the returned tree and `h t∈{h t',h t'+1}` (p.110; `avl_split_max`). | G/P shared balancing laws. |
| C09-034 | Delete E=E; LT uses **balR** after deleting left; GT uses **balL** after deleting right; EQ returns r if l=E, otherwise replaces the payload with the extracted left maximum and uses balR (p.109). | G. Retain the direction reversal relative to insertion and the exact predecessor policy. |
| C09-035 | Under S, `I(delete x t)=del_list x (I t)` (`AVL_Set_Code.inorder_delete`). | G/P. Again no Aht premise for this cache-family semantic theorem. |
| C09-036 | Theorem 9.5: Aht t and t'=delete x t imply Aht t' and `h t∈{h t',h t'+1}` (p.111; `avl_delete`, `avl_delete_auto`). | G. The source supplies manual and more automatic proofs of the same contract; duplicate Lean proofs are not required. |
| C09-037 | Instantiate all seven Set-by-Ordered obligations for cached AVL trees (`AVL_Set.S`), combining strict-order semantics with Aht preservation. | X Chapter 6. This is a concrete consumer of the shared refinement interface. |
| C09-038 | Preserve the mathematical content of the rotation diagrams (pp.108,110): the single/double rewrites preserve inorder, restore the permitted balance, and have the height effects covered by C09-022–026. In the deletion double rotation, at least one middle grandchild has the indicated maximal height. | G/P. A rendered diagram alone is not a proof; exact helper laws may discharge its cases without new duplicate declarations. |
| C09-039 | Instrument actual cached search/insert/split_max/delete and local constructors/balancers if deriving running time; count cached ht access and explicitly state the unit-charge arithmetic/comparator convention. | G/X resource layer. Replacing ht by a recursive height computation changes the algorithm's cost. |
| C09-040 | Prove the actual search/update paths plus bounded local rotations have linear-in-input-height bounds, including predecessor extraction in deletion. | G. Counting only comparisons omits rebuilding/rotation work; keep the observations named separately if both are exposed. |
| C09-041 | Combine C09-015 with C09-040 for logarithmic valid-state operations; relate node count to abstract set cardinality only under S. | P/G. No machine-time or physical-memory result follows without an explicit target model. |

### Cached-height balancers

The heavy-child and middle-child destructuring is justified by C09-020.

| Case | Output |
|---|---|
| balL AB c C, ht AB≠ht C+2 | node AB c C |
| balL N(A,(a,_),B) c C, ht AB=ht C+2 and ht B≤ht A | node A a (node B c C) |
| Same imbalance, ht A<ht B, B=N(B1,(b,_),B2) | node (node A a B1) b (node B2 c C) |
| balR A a BC, ht BC≠ht A+2 | node A a BC |
| balR A a N(B,(c,_),C), ht BC=ht A+2 and ht B≤ht C | node (node A a B) c C |
| Same imbalance, ht C<ht B, B=N(B1,(b,_),B2) | node (node A a B1) b (node B2 c C) |

## Exercises 9.1–9.5: pp.111–112

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C09-042 | Exercise 9.1 literally asks `Aht t ∧ h t=n -> 2^(n div 2)<=leaves t`, proved by Fibonacci/two-step computation induction on n (p.111). | R/P `Nat.twoStepInduction`, plus G generalized tree-height induction statement. The exponent is floor division, visually confirmed. |
| C09-043 | Supply the extra arithmetic strength needed for the claimed zero-additive logarithmic consequence. A concrete direct route is the stronger `Aht t ∧ h t=n -> 2^((n+1) div 2)<=leaves t`, proved by the same two-step induction. | G/proof-gap repair. Prove the proposed stronger target before using it; it is not established by this inventory. |
| C09-044 | Retain Exercise 9.1's final exact conclusion `Aht t -> h t<=2*log₂(leaves t)` with a direct proof route, without importing the golden-ratio/Fibonacci size theorem as a substitute for the requested argument. | G/P logarithm arithmetic. C09-043 can imply both C09-042 and this conclusion. |
| C09-045 | Record the limitation of the floor estimate as an arithmetic counterexample: n=3,L=2 satisfies `2^(n div 2)<=L` but violates `n<=2*log₂ L`. | G/source proof-boundary witness. This pair is not claimed to be an AVL tree; the final AVL theorem is true. The missing inference must be filled, not declared false or silently given an additive constant. |
| C09-046 | Exercise 9.2 fibt recurrence: fibt0=E; fibt1=N(E,(),E); fibt(n+2)=N(fibt(n+1),(),fibt n) (p.111). | G. This is an executable unannotated shape construction, not merely a count sequence. |
| C09-047 | Prove A0(fibt n) (Exercise 9.2), using the exact signed/two-sided balance predicate of C09-007. | G. |
| C09-048 | Prove `h(fibt n)=n`, which is needed to justify the claimed minimum **at the prescribed height**. | G/support. Count equality alone would not establish a height-minimizing witness. |
| C09-049 | Prove `leaves(fibt n)=F(n+2)` (Exercise 9.2). | R/P Fibonacci recurrence and G structural induction. Internal nodes are one fewer. |
| C09-050 | Conclude `Aht t -> leaves(fibt(h t))<=leaves t`, and combine C09-048–049 with the shape version of C09-011 to characterize the exact minimum for each height and its recurrence (Exercise 9.2 and p.106 introduction). | G/P. Annotation can be restored with a correct height-decoration function if the minimum is stated over cached trees. |
| C09-051 | Preserve the distinction between size meanings in the minimality statement: the printed bound is leaves; node minimality follows by `leaves=nodes+1` and must be explicitly translated if used. | R/P Chapter 4. |
| C09-052 | Use Chapter 4 almost-completeness and its inheritance to children, preserving its global height/minimum-height definition. | X C04-042/C04-046. AVL is a local balance condition, so the predicates must not simply be identified. |
| C09-053 | Exercise 9.3: `acomplete t -> A0 t` for arbitrary payloads (p.111). | G/P C09-052 plus two-sided height bounds. The converse is not asserted. |
| C09-054 | Exercise 9.4: fix an integer d≥1, replace the local ±1 condition by signed absolute difference ≤d, and retain recursive cache correctness (pp.111–112). A natural d with a checked integer-coercion bridge is acceptable. | G. d is fixed for the family, not an unchecked arbitrary negative integer. |
| C09-055 | Define concrete generalized cached balancers/insert/delete. One candidate is the same single/double rotation scheme with the imbalance trigger changed from +2 to +(d+1), preserving the side/tie tests and predecessor policy. | G/design candidate. The recurrence and all domain/height cases require proof; merely stating the generalized invariant is not a solution. |
| C09-056 | Prove generalized local rebalancing and cache/domain laws, with the one-sided permitted range appropriate to a single insertion/deletion from a d-balanced tree. | G. For balL a useful target is `h r-d<=h l<=h r+d+1`, mirrored for balR; verify the candidate's exact height effects rather than assuming d=1 proofs apply verbatim. |
| C09-057 | Prove generalized insertion's same contract as Theorem 9.4: preserves the d-invariant and changes height by 0 or +1; prove exact strict ordered-list insertion semantics. | G/X shared list refinement. This is quantified over every fixed d≥1, not only d=2. |
| C09-058 | Prove generalized extraction and deletion's same contracts as Theorem 9.5: preserve the d-invariant, decrease height by 0 or 1, and satisfy predecessor/list deletion observations. | G. Preserve simultaneous height effects, including equal child-height/tie cases. |
| C09-059 | Instantiate Set correctness for the generalized implementation under its invariant and S. | X Chapter 6. A rebuild-from-sorted-list function with the right output set would not establish correspondence with the proposed local-update algorithm or its costs. |
| C09-060 | Relate d=1 to the original cached algorithms and invariant if generalized code is used as their implementation, including exact recurrence/cost specialization. | P/G adapter requirement. No duplicate implementation is required if this transport is checked. |
| C09-061 | Retain the Chapter Notes p.116 claim: for each fixed d≥1, these trees still have logarithmic height. A sufficient prospective bound is `h t <= (d+1)*log₂(leaves t)`, obtainable from `2^ceil(h t/(d+1))<=leaves t`; alternatively port the cited AFP exponential-base theorem. | G/X. Exercise 9.4 waives this proof pedagogically, but the user requests the book's mathematical claims in Lean; the note's explicit claim remains an obligation. Constants may depend on fixed d. Optimal constants/asymptotics not stated in the book are not required. |
| C09-062 | Exercise 9.5: define an executable linear-time avl_of_list for arbitrary lists, following the bottom-up construction idea (p.112). A concrete route is Chapter 4 sequential prefix balancing with cached heights built simultaneously, or its almost-complete tree followed by one linear height-annotation pass. | X Chapter 4/G. Repeated insert or repeated take/drop/height traversals are not interchangeable with this linear algorithm. |
| C09-063 | Preserve the construction's successful-domain invariant and suffix-consumption contract; every extracted list head exists, and the wrapper consumes exactly the original length. | X C04-047–051. No default payload/inhabited-type assumption. |
| C09-064 | Prove `I(avl_of_list xs)=xs` for all lists, including duplicates and empty input (Exercise 9.5). | P/G Chapter 4 inorder preservation. |
| C09-065 | Prove Aht(avl_of_list xs), using almost-completeness→A0 plus correct annotation for the proposed route (Exercise 9.5). | G/P C09-053. No input sortedness assumption. |
| C09-066 | Prove a linear bound for the actual traversal and cache-building recurrence, including any initial length pass and any separate annotation pass; name local constructor/ht charges. | G/X C04-061 and resource layer. A value equivalence to a linear conversion does not transfer its cost automatically. |
| C09-067 | Strictly sorted input yields a valid AVL search tree; repeated input still satisfies the exercise's structural/inorder contracts but can violate S. | P/G. The list `[1,1]` separates these claims. |

The candidate generalized bounds and algorithms above are original planning
targets. They are mathematically motivated by the one-level update
contracts, but are **not** recorded as Lean-checked results. Later work
must retain any additional cases exposed by their proofs.

## Balance-factor optimization: pp.112–115, Figure 9.4

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C09-068 | Define balance tags Lh/Bal/Rh and tree_bal as the shared binary tree with `(payload,tag)` labels (p.112; `AVL_Bal_Set`). | R/P shared carrier, G specialized code. These three cases encode differences +1/0/-1, not arbitrary height caches. |
| C09-069 | Abal E holds; at a node Lh means `h l=h r+1`, Bal means equal heights, Rh means `h r=h l+1`, and both children satisfy Abal (p.112). | G. Uses actual height only in the invariant, not executable operation branches. |
| C09-070 | Relate Abal to A0 after erasure and to the exact tagged height difference; preserve height, nodes, leaves and inorder under erasure. | R/P Chapter 4 plus G tag correspondence. This is sufficient to transport shape-based height bounds. |
| C09-071 | `is_bal` on a nonempty node reports tag=Bal; give its E behavior a deliberate domain/totalization policy and prove reachable comparisons are independent of that policy (p.113). | P/G. The source omits E and supplies no payload default. |
| C09-072 | `incr t t'` is true when t=E, or when t is Bal and t' is not Bal; retain its polymorphic payload types (p.113). | G. Implement empty tests by shape; do not require equality on payloads. |
| C09-073 | `decr t t'=(t≠E ∧ incr t' t)` (p.113). Where the old tree is already nonempty, prove the simplified `incr t' t` form used by extraction/deletion. | G. The explicit old-nonempty condition matters for E. |
| C09-074 | Keep the detector contract operation-relative: Theorems 9.6–9.7 prove it for actual insertion/deletion outputs. Preserve a small boundary witness `incr E E=true` although both heights are zero. | G/support. Abal of two arbitrary trees alone does not make incr a generic height comparison. |
| C09-075 | rot2 destructures its middle nonempty tree B=N(B1,(b,bb),B2), sets left output tag to Lh iff bb=Rh else Bal, right output tag to Rh iff bb=Lh else Bal, and returns a Bal-rooted double rotation (p.114; table below). | G. Retain all three middle-tag cases and its nonempty domain. |
| C09-076 | Implement balL with all five tag/shape cases of Figure 9.4: old Bal/Rh only retag; old Lh examines heavy child Lh/Bal/Rh and selects the exact single/double rotation (p.114). | G. The heavy-child Bal single-rotation case is required for deletion even if insertion does not reach it. |
| C09-077 | Implement the five mirrored balR cases including its heavy-child Bal branch (p.114). | G. Preserve every output tag as shown in the matrix below. |
| C09-078 | Prove operation calls satisfy every heavy-child/middle-child nonempty pattern requirement, and give an explicit domain/Option correspondence for raw partial helpers if needed. | P/G. Unlike C09-020, arbitrary malformed tags do not imply these domains. |
| C09-079 | Retain the exact companion inorder-helper hypotheses: balL needs Abal l and `(oldTag=Lh -> l≠E)`; balR needs Abal r and `(oldTag=Rh -> r≠E)`; each returns `I l ++ [a] ++ I r` (`inorder_balL/R`). | G. The opposite child is unrestricted in these semantic helper laws. |
| C09-080 | Insert E is a Bal singleton. LT/GT recursively compute the new child once; if incr old new, call the corresponding balancer with the **old parent tag**; otherwise rebuild with the old tag. EQ returns the old node (p.113). | G. Do not recompute structural heights to choose the branches. |
| C09-081 | Theorem 9.6: Abal t and t'=insert x t imply Abal t' and `h t'=h t+(if incr t t' then 1 else 0)` (p.115; `AVL_Bal_Set.avl_insert`). | G. The exact equality proves both bounded growth and correct detection. |
| C09-082 | Under Abal t and S, `I(insert x t)=ins_list x (I t)` (`AVL_Bal_Set.inorder_insert`). | G/P. The source uses Abal here to rule out missing rotation patterns; do not advertise the cache-version's weaker premise without a new proof/totalization argument. |
| C09-083 | Preserve the source support facts used by deletion/semantics: under Abal, height=1 iff a Bal singleton; insertion output is nonempty; it cannot have a Rh root with empty right or an Lh root with empty left (`height_1_iff` and auxiliary lemmas). | G/P. These are domain/shape facts, not additional ordering assumptions. |
| C09-084 | split_max N(l,(a,ba),r): if r=E return (l,a); otherwise get (r',a'), then use balL l a ba r' iff incr r' r, else rebuild with old ba, and return a' (p.115). | G. Detection arguments are new,old in this decrease test; preserve their order. |
| C09-085 | Nonempty Abal t and split_max t=(t',a) imply Abal t' and `h t=h t'+(if incr t' t then 1 else 0)` (p.115; `avl_split_max`). | G. This is the printed exact-height extraction contract. |
| C09-086 | Nonempty Abal t and split_max t=(t',a) imply `I t' ++ [a]=I t`; under the same hypotheses, split_max t=(E,x) iff t is the Bal singleton carrying x (`inorder_split_maxD`, `split_max_Leaf`). | G/P. Unlike cache-family extraction, these source list/helper statements assume Abal. |
| C09-087 | Delete E=E. LT/GT compute the changed child once and balance on decr, on the **opposite** side. EQ returns r if l=E, otherwise extracts left maximum and balances right iff incr l' l; all no-change branches keep the old parent tag (p.115). | G. Payload replacement and old-tag preservation both matter. |
| C09-088 | Theorem 9.7: Abal t and t'=delete x t imply Abal t' and `h t=h t'+(if decr t t' then 1 else 0)` (p.115; `avl_delete`). | G. Includes empty input and absent-key cases. |
| C09-089 | Under Abal and S, exact ordered-list deletion semantics (`AVL_Bal_Set.inorder_delete`). | G/P shared ordered-list laws. Structural preservation alone is not content correctness. |
| C09-090 | Instantiate all seven Set-by-Ordered obligations for the factor implementation (`AVL_Bal_Set.S`). | X Chapter 6. It must be an actual second concrete refinement, sharing abstract clients. |
| C09-091 | Transfer the logarithmic height theorem to Abal trees through the shape invariant or the checked height-decoration bridge of Exercise 9.6. | P/G. Do not assume identical annotated carriers or execute decoration inside each update. |
| C09-092 | Instrument factor-family operations and show the saved height fields are replaced by bounded root-tag/shape tests and local rotations; prove linear-in-height and resulting logarithmic operation bounds under the explicit model. | G/X. Count the actual detection/rotation recurrence, not a cache-family cost theorem attached to the same abstract set result. |
| C09-093 | Verify the optimization's executable functions never traverse a subtree to compute h. Actual h remains in propositions/proofs, where it is not runtime work. | G/recurrence correspondence. Computing h in a Boolean branch would defeat the described optimization. |
| C09-094 | Harmonize both implementations through the common Set abstraction and observations, preserving their different annotations, helper domains, and resource models. If one is implemented by transport from the other, prove the exact operation/representation correspondences actually used. | X project representation/refinement infrastructure. Shared abstract behavior alone does not establish equal concrete trees or costs. |

### Balance-factor case matrix

Write `N_b(l,a,r)` for a node with payload a and tag b. The input tag in
balL/balR is the old parent tag, before the selected child's height changed.

| Function/case | Result |
|---|---|
| balL AB c Bal C | N_Lh(AB,c,C) |
| balL AB c Rh C | N_Bal(AB,c,C) |
| balL N_Lh(A,a,B) c Lh C | N_Bal(A,a,N_Bal(B,c,C)) |
| balL N_Bal(A,a,B) c Lh C | N_Rh(A,a,N_Lh(B,c,C)) |
| balL N_Rh(A,a,B) c Lh C | rot2 A a B c C |
| balR A a Lh BC | N_Bal(A,a,BC) |
| balR A a Bal BC | N_Rh(A,a,BC) |
| balR A a Rh N_Lh(B,c,C) | rot2 A a B c C |
| balR A a Rh N_Bal(B,c,C) | N_Lh(N_Rh(A,a,B),c,C) |
| balR A a Rh N_Rh(B,c,C) | N_Bal(N_Bal(A,a,B),c,C) |

For rot2 A a N_bb(B1,b,B2) c C, the output is
`N_Bal(N_b1(A,a,B1),b,N_b2(B2,c,C))`, with:

| bb | b1 | b2 |
|---|---|---|
| Bal | Bal | Bal |
| Lh | Bal | Rh |
| Rh | Lh | Bal |

These include the balanced-heavy-child cases needed after deletion.
Leaving those out because a particular insertion proof does not reach
them would not implement Figure 9.4 or Theorem 9.7.

## Exercises 9.6–9.7: p.116

| ID | Exact obligation | Reuse or gap |
|---|---|---|
| C09-095 | Exercise 9.6 debal: E→E; replace each factor-annotated node by the recursively converted children and cache `max(h l)(h r)+1`, where h is actual height of the **original** children. | G/P. Preserve this explicit reference algorithm even though it repeats height traversals. |
| C09-096 | Prove `Abal t -> Aht(debal t)` (Exercise 9.6). | G/P C09-070 and annotation correctness. |
| C09-097 | Define debal2 of the same result type using one recursive traversal and **no calls to h** in the algorithm. A helper returning both the rebuilt tree and its height can compute each node cache from child summaries. | G. Reusing smart construction over recursively rebuilt, correctly cached children is another valid concrete design if its local work is counted. |
| C09-098 | Prove `Abal t -> debal2 t=debal t` as requested. For the shape-summary route the stronger equality for all input trees is available as a proof target because original balance tags are ignored by both conversions. | G. A stronger theorem may discharge the printed conditional theorem; do not claim it without a proof. |
| C09-099 | Formalize the single-traversal requirement and linear cost of debal2's actual recurrence. A direct pair-returning traversal has `2*nodes+1` recursive tree entries under one entry charge and inlined primitive arithmetic; separately called ht/node helpers change the total function-call constant. | G/X resource layer. Value equality C09-098 does not equate the repeated-height reference algorithm's cost. |
| C09-100 | Prove conversion preserves erased inorder/shape and hence height, nodes and leaves, so its invariant and height results compose with the shared abstraction and C09-091. | R/P Chapter 4 and G conversion bridge. |
| C09-101 | Exercise 9.7's tree4 has **four constructors**: Leaf, Lh(left,payload,right), Bal(left,payload,right), Rh(left,payload,right), with no separate annotation field (p.116). | G. This is not AVL_Bal2_Set's Same/Diff result type. |
| C09-102 | Define the structural equivalence between tree4 and factor-annotated binary trees, with both inverse laws, inorder/height/size preservation, and constructor/tag correspondence. | G/P. This allows proof transport without hiding runtime conversion costs. |
| C09-103 | Define tree4's exact local balance invariant and prove its equivalence to Abal under the representation map. | G. Keep the independent strict search-order predicate. |
| C09-104 | Implement the shape/tag versions of is_bal, incr, and decr, with the same empty/domain conventions and checked detector correspondence. | G. Payload equality is still unnecessary. |
| C09-105 | Implement all necessary tree4 helpers, including rot2, all balL/balR cases, and predecessor split_max, and prove their correspondence to the printed factor recurrences on their valid domains. | G/P C09-075–079/C09-084–086. Replacing the carrier while leaving algorithms only on the old type does not solve the exercise. |
| C09-106 | Implement tree4 insertion/deletion directly through the constructor cases and prove their operation correspondence. | G. An implementation may share a generic recursor, but it must actually execute the specified local update pattern on tree4. |
| C09-107 | Prove exact analogues of Theorems 9.6 and 9.7 on tree4, preserving the invariant and the detector-indexed equalities for height increase/decrease. | G/P transport permitted after C09-102–106. These are the exercise's explicit theorem targets. |
| C09-108 | Establish strict ordered-list/set semantics and the common Set refinement for tree4, so the exercise is harmonized with conaled rather than an isolated datatype. | X Chapter 6/project integration, sharing existing clients through the checked representation. |
| C09-109 | Retain executable/resource correspondence: a whole-tree encode→old operation→decode wrapper incurs linear conversion work and is not the intended local-update implementation. Prove local recurrence/cost transport if reusing proofs. | G/X. A proof-only representation equivalence has no such runtime cost. |
| C09-110 | State the space claim at its justified level: tree4 carries the factor in the constructor rather than an additional label field; record the chosen structural storage observation. Any exact compiled byte saving requires the actual compiler/runtime layout and is not implied by datatype isomorphism alone. | G/qualified analysis plus formal storage count if quantified. The book supplies no exact byte tariff. |

## Reuse and proof organization

### Shared tree and Set domains

Mathlib `BinaryTree` is the matching empty-leaf/node-labelled carrier.
Its `numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ`,
`numLeaves_pos`, `height_le_numNodes`, map, and recursion principles are
available. Chapters 4–5 supply the required inorder, annotation erasure,
cache laws, almost-complete balancing, and strict list observations; Chapter
6 supplies the Set refinement laws. Reuse those as genuine shared domains
instead of creating chapter-indexed copies.

Existing conaled `Squares.Rep`, commuting-square composition, and the
relational invariant pattern can express valid representations and
observational agreement between cached/factor/constructor encodings.
Resource observations remain separate and must follow the concrete
recurrences. The three AVL representations do not become definitionally
equal by sharing their abstract set behavior.

### Arithmetic already in Mathlib

`Mathlib/Data/Nat/Fib/Basic.lean` contains `Nat.fib`, its base/recurrence
laws, `fib_mono`, and `fib_add_two_strictMono`.
`Mathlib/Data/Nat/Init.lean` has `Nat.twoStepInduction`, the precise
two-base/two-successor induction pattern requested by the book.
`Mathlib/NumberTheory/Real/GoldenRatio.lean` has the real definition,
positivity, the >1/<2 bounds, and φ²=φ+1. It also proves Binet's formula
and identities such as `goldenRatio_mul_fib_succ_add_fib`; a short
two-step proof is a more direct route to Lemma 9.2 than importing an
unnecessary closed-form asymptotic development.

The library fib implementation is an iterator on pairs. It matches the
mathematical recurrence, but source-style naive Fibonacci **runtime**
would require a separate executable recurrence/cost bridge if later used.
Here fib is a mathematical bound, so this distinction creates no need to
reimplement it just to state Lemmas 9.1–9.2.

### Generalized-height provenance and scope

The dated AFP source defines `hbt d t` with signed child-height difference
bounded by natural d and a locale assuming d>0. It defines:

- `hbt_lb 0=1` and `hbt_lb(n+1)=hbt_lb n+hbt_lb(n-d)`, with natural
  truncated subtraction;
- `hbt_lb n=n+1` for n≤d;
- `hbt_size1_height_bound`: hbt d t implies
  `hbt_lb(height t)<=size1 t`;
- `hbt_wc 0=Leaf`, `hbt_wc(n+1)=Node(hbt_wc(n-d))()(hbt_wc n)`;
- `height_hbt_wc`, `hbt_hbt_wc`, and `size1_hbt_wc`, which prove the
  bound is attained at each prescribed height;
- `hbt_lb_altdef`, characterizing the minimum leaf count over the finite
  family of unit-labelled d-balanced trees of the prescribed height.

In locale `hbt_lower_bound_constant`, the assumptions are c>1 and
`hbt_charfun c<=0`, where the characteristic expression is
`c^(d+1)-c^d-1`. It proves `hbt_lb_ge: c^n<=hbt_lb n` and
`hbt_height_bound: hbt d t -> height t<=log_c(size1 t)`.
This is precise primary-source support for C09-061. The later theory
constructs the optimal base, proves its d=1 golden-ratio instance, and
develops exact/asymptotic expressions. Only the generalized logarithmic
claim is explicitly asserted in the book's note; full external coverage
is not silently required.

The cached generalized algorithms of Exercise 9.4 are **not implemented
by this bounds-only AFP entry**. Neither its height theorem nor an
unrelated balanced-tree library discharges the exercise's insertion and
deletion contracts. Those algorithms and their local shape/domain proofs
remain C09-055–060.

## Source proof gaps, prose errors, and recovery handoff

1. **Exercise 9.1 floor exponent, p.111.** The displayed natural bound is
   true, and the final logarithmic AVL bound is true. The first inequality
   alone only yields a bound with rounding slack; it does not establish
   the printed zero-additive consequence by itself. Preserve the numeric
   nonimplication witness and the missing strengthened AVL proof, such as
   C09-043. Do not weaken the final target or import the chapter's earlier
   Fibonacci proof in place of the exercise's requested direct argument.
2. **Source-domain differences.** Cached-height balancer patterns are
   guarded by elementary positivity facts even on invalid caches; factor
   balancers instead require invariant/domain reasoning. Both split_max
   functions and the factor `is_bal` omit an empty equation. Record the
   actual chosen Lean domain/totalization and prove reachable behavior.
3. **The factor detectors are not arbitrary height comparators.** The
   equations in Theorems 9.6–9.7 are certified specifically on the output
   of the corresponding operation. Even E,E refutes a naive universal
   interpretation of incr as strict height increase.
4. **Dated AFP prose-only errors.** In the inspected `HBT_Bounds.thy`,
   the explanation of natural `n-d` says min with zero; it should say
   max with zero. For n=2,d=1, truncated subtraction is 1 but min(0,1)=0.
   A later paragraph says leaves are *at most* hbt_lb(height), while its
   formal theorem correctly proves *at least*. For d=1 a complete
   height-2 tree has four leaves whereas hbt_lb 2=3, refuting that prose
   upper bound. Some prose also calls the measured quantity nodes, but
   the formal statements use size1, i.e. leaves; the minimum height-2
   witness has two internal nodes and three leaves. Preserve these
   corrections if this supporting development is ported. Its checked
   recurrences and theorem directions are unambiguous.
5. **Numerical and resource claims.** Keep the exact golden-ratio
   coefficient. The printed ≈1.44 is not an exact multiplier bound.
   Likewise, single-pass conversion, cached root access, tag-only update,
   and local rotations must be tied to actual algorithms. A shared
   output list/set or representation isomorphism alone supplies no
   running-time or compiled-space equality.
6. **Acceptance remains queued.** Every exercise's mathematical
   conclusion and algorithmic restriction remains a Lean obligation.
   The book's permission to omit a generalized-height proof from an
   exercise does not erase the explicit mathematical claim in its
   chapter notes. Source preparation, plausible derivations, and existing
   dependency theorems are not accepted coverage. Later closure requires
   exact declaration mappings, relevant validation, and both review axes
   on the same immutable candidate.

All 110 numbered entries identify book mathematics, algorithmic
restrictions, or explicit support/integration work needed to preserve
those claims. The note is original reconstruction rather than a copy of
the manuscript. Provenance keeps the mutable official PDF URL and its
exact hash explicit; no immutable official URL for this complete PDF
edition has been established.

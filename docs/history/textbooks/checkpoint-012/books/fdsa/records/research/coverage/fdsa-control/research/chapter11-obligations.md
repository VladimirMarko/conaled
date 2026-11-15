# Chapter 11: Arrays via Braun Trees — source obligations and reuse

Research date: 2026-11-02. Local ticket: `FDSA-011`.

**State: queued; source preparation only.** This original reconstruction note
does not activate Chapter 11, add Lean code, run a build, certify a cost model,
or accept any obligation. Chapter 1 remains the active sequential chapter. Every
row needs a checked implementation or reuse witness, statement review,
applicable validation, and the project's independent reviews before acceptance.

## Evidence, provenance and scope

| Source | Inspected identity |
|---|---|
| Book | Tobias Nipkow, Chapter 11, printed pp. 127–147, with p. 148 blank; PDF pages 133–154 of *Functional Data Structures and Algorithms: A Proof Assistant Approach*, July 27, 2026 version. <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. The book's evolving URL is not an immutable version identifier. |
| Isabelle source revision | <https://github.com/isabelle-prover/mirror-isabelle> at `f86f290225eebcc52c1ae7dba2e098f405f51c21`. This shared inspection pin postdates the book; statements and recurrences were compared explicitly. |
| `Array_Specs.thy` | `src/HOL/Data_Structures/Array_Specs.thy`; 1,679 bytes; SHA-256 `f510de82de0f2b36014f9a963a0ec7f23b19b66ff501f9bdcf1e0f05ea673a50`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Array_Specs.html>. Full file inspected. |
| `Braun_Tree.thy` | `src/HOL/Data_Structures/Braun_Tree.thy`; 6,544 bytes; SHA-256 `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Braun_Tree.html>. Full file inspected, including the converse index characterization omitted from the prose proof. |
| `Array_Braun.thy` | `src/HOL/Data_Structures/Array_Braun.thy`; 26,980 bytes; SHA-256 `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f`. Direct PDF link: <https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Array_Braun.html>. Full file inspected. |
| Shared supporting sources | `src/HOL/Library/Tree_Real.thy`, SHA-256 `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6`; `src/HOL/Data_Structures/Balance.thy`, SHA-256 `6d14341de140a4cf5d811798aa1796c143a9127aedfeae0b600f8d174e6bb3fc`; `src/HOL/Library/Tree.thy`, SHA-256 `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9`. These supply Chapter 4 conventions, almost-completeness, and the `bal` implementation for Exercise 11.4. |
| Cost translation | `src/HOL/Library/Time_Functions.thy`, SHA-256 `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01`. Appendix B inventory, especially B-028, owns the shared `T_nodes` recurrence. This chapter retains the operation, its correctness and the composed bounds. |
| Isabelle license | BSD-3-Clause at the same revision; `ISABELLE-COPYRIGHT` SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`. Preserve relevant notices for translated source. The chapter attributes the development to Nipkow and Sewell; the source identifies Sewell's contributions to the conversion proofs and algorithms. |
| Lean reuse | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Relevant sources carry Apache-2.0 notices. Exact inspected interfaces are listed below. |

Pinned raw Isabelle URLs consist of
<https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/>
followed by the path in the table. Reading copies, extracted chapter text and
selected rendered pages are under `book-source/`; the manuscript is not a
deliverable. No `sorry`, `oops`, `axiomatization` or `admit` occurrence was found
in the three chapter theories. That is a scoped source scan, not an Isabelle
build or an independent proof audit. The inspected theories do not contain all
eight exercise solutions; this does not remove their obligations.

The complete chapter includes the array and flexible-array interfaces,
least-significant-bit indexing, Braun characterization, simple and fast
constructors/converters, quantitative cost claims, all numbered and unnumbered
mathematical results, and Exercises 11.1–11.8. Assertions described as interesting
but not proved in the exposition remain mathematical coverage obligations.
Chapter 16's priority-queue operations are outside this chapter.

## Conventions and actual reuse

Write `E` for an empty leaf and `N l a r` for a node. Let `n(t)` count labelled
nodes, `ell(t)=n(t)+1` count empty leaves, `h(t)` be maximum height, and `mh(t)`
minimum height, all as in Chapter 4. `B(t)` denotes Braun validity. `L(t)` is
the array-order list, **not inorder or ordinary preorder**. `sp` abbreviates
the book's splice operation. All division and subtraction of natural numbers
use floor division and truncated subtraction. Indices passed to the raw
`lookup1`/`update1` functions start at 1; the public array index starts at 0.

The choices in `fdsa-control/DECISIONS.md` apply. In particular, arbitrary Lean
payloads may be empty types; no global `Inhabited α` is justified by HOL's
underspecified leaf lookup. Use a valid-input proof or the existing `Option`
failure convention, and prove its source correspondence. Raw `update1` is
total and intentionally inserts at the first reached empty leaf, even on
invalid indices. The array wrapper only promises the valid-index update laws;
do not infer a total no-op contract for that wrapper from its conditional ADT.

| Existing interface | Precise reuse and limit |
|---|---|
| Mathlib `BinaryTree α` in `Data/Tree/Basic.lean` | Exact empty-leaf, node-labelled carrier; `node` takes label first in Lean. Reuse `numNodes`, `numLeaves`, `height`, `left`, `right`, mapping and structural induction. The deprecated `Tree` aliases are unnecessary. Braun validity and array-order conversion remain new domain facts. |
| Mathlib `BinaryTree.get` in `Data/Tree/Get.lean` | Already has the exact positive-bit path: `PosNum.one` selects root, `bit0` goes left, `bit1` goes right, empty tree returns `none`. A checked positive-Nat/`PosNum` conversion, valid-domain theorem, and any Nat-recursion cost bridge are still required. `getOrElse` merely adds a caller default and is not needed for the generic payload interface. |
| Batteries `List.interleave` in `Batteries/Data/List/Interleave.lean` | Exact two source equations for `sp`, including keeping the remainder of the nonempty list. Reuse `nil_interleave`, `cons_interleave`, `interleave_nil`, `length_interleave`, `interleave_perm_append`, `interleave_append_left` and `interleave_append_right`. The last two already have the source's asymmetric length assumptions. The `ofFn` even/odd theorems can support indexed splice laws. No separate `splice` algorithm is needed. |
| Standard list operations and Appendix A adapters | Reuse `List.set`, optional/proof-domain indexing, `tail`, `dropLast`, `take`, `drop`, `replicate`, `map`, `filter`, `sum`, `List.Ico`, and extensionality. The source's out-of-range-update sentence is inconsistent with its own Appendix A; retain standard total no-op update behavior for lists. |
| `Applications/Sequences/RandomAccess/{Basic,Access,Representation,TreeBuild}.lean` | Existing array observations, optional lookup, valid representation and `Squares` composition are reusable integration patterns. Their `RandomAccess.Tree` has payloads at leaves, cached unlabelled forks, and complete ranked blocks in a digit list. Its `fetchT` uses interval splitting by cached size. It is not the Braun carrier, index path, array-order list or algorithm. |
| `Applications/Resources/RandomAccess/{Lookup,End,...}.lean` | Existing measured-value erasure, resource composition and independent list observation patterns apply. Their exact binary-carry/borrow and perfect-block costs do not certify this chapter. In particular the existing linear `toRA` bound is not the repeated-`update1` constructor's bound. |

No integrated Braun implementation or its exact cost development was found in
the inspected conaled slices. This is a scoped reuse finding, not an assertion
that every dependency file or external formalization has been searched.

## 11.1 Array contracts: pp. 127–128, Figure 11.1

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-001 | Array carrier, element type, `lookup : Ar → Nat → α`, `update : Nat → α → Ar → Ar`, `len`, constructor `array`, abstraction `L`, invariant `V`. | Reuse the shared representation/ADT approach from Chapter 6. Failure/domain adaptation belongs at lookup; no order or decidable equality on payloads is required. |
| C11-002 | `V ar ∧ i < len ar → lookup ar i = (L ar)[i]`. | Source `Array.lookup`; express valid indexing or a `some` equality. Preserve the explicit index bound. |
| C11-003 | `V ar ∧ i < len ar → L(update i x ar) = (L ar).set i x`. | `Array.update`. Standard list update is already total; the array representation contract here is conditional. |
| C11-004 | `V ar ∧ i < len ar → V(update i x ar)`. | `Array.invar_update`. Length correctness does not replace validity preservation. |
| C11-005 | `V ar → len ar = length(L ar)`. | `Array.len_array`; this is cached-size correctness, not runtime recomputation of tree size. |
| C11-006 | `L(array xs)=xs` and `V(array xs)` for every list, including empty and duplicate-filled lists. | `Array.array`, `Array.invar_array`. No set-style deduplication or sortedness premise. |
| C11-007 | Lists are the abstract functional model; linear-time list indexing/update do not constrain implementation cost. Array entries are contiguous zero-based indices. | Mathematical list behavior is covered by Appendix A. Preserve the distinction between abstraction and executable array operations in integration. |

## 11.2 Braun shape and indices: pp. 128–130

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-008 | `B E=True`; `B(N l a r) ↔ (n l=n r ∨ n l=n r+1) ∧ B l ∧ B r`. Equivalent inequalities `n r≤n l≤n r+1`. | `Braun_Tree.braun`, `braun_Node'`. Define on the shared `BinaryTree`; label values are irrelevant to the invariant. |
| C11-009 | Positive index path: root 1; read low bits first, even goes left, odd goes right, divide by 2; stop at the leading 1. | `BinaryTree.get` has this positive-bit recursion. Prove the Nat/positive-bit bridge and path validity; no most-significant-bit or heap-array index substitution. |
| C11-010 | Index set recurrence `idx E=∅`; `idx(N l a r)={1} ∪ (2·)[idx l] ∪ (2·+1)[idx r]`. | `braun_indices`. The child indices are relative to their child root, not conventional breadth-first heap numbering. |
| C11-011 | All indices are positive, the set is finite, and its cardinality is `n(t)`. | `braun_indices1`, `finite_braun_indices`, `card_braun_indices`. Injectivity and disjoint even/odd images justify cardinality, including arbitrary non-Braun trees. |
| C11-012 | `B t → idx t={1,…,n(t)}`. | `braun_indices_if_braun`. This proves contiguity and the valid range, rather than assuming them from size. |
| C11-013 | Converse `idx t={1,…,n(t)} → B t`, hence equivalence. The prose expressly mentions but does not prove this fact. | `braun_if_braun_indices`, `braun_iff_braun_indices` supply the full proof. Retain as Lean coverage. Supporting interval-base, even/odd filtering and image-injectivity lemmas can be reused without public wrappers. |
| C11-014 | Lemma 11.1: almost-complete `l,r` and `n l=n r+1` imply almost-completeness of `N l a r`. | `Tree_Real.acomplete_Node_if_wbal1`, already shared with Chapter 4. Preserve node/leaf counts in the floor/ceiling-log proof. |
| C11-015 | Proof identities for Lemma 11.1: `h(N l a r)=ceil(log₂(ell r+1))+1`, `mh(N l a r)=floor(log₂(ell r))+1`; for `2^i≤ell r<2^(i+1)`, also `2^i<ell r+1≤2^(i+1)`. | Natural floor/ceiling casts or equivalent Nat-log statements must be connected to the displayed real-log formulas. `ell r≥1` is automatic, including empty `r`. |
| C11-016 | Lemma 11.2: every Braun tree is almost complete. | `acomplete_if_braun`; equal-child-size and left-one-larger cases both matter. Reuse Chapter 4 almost-complete results after a checked predicate bridge. |
| C11-017 | Consequences claimed in the prose: Braun trees attain the minimum possible height for their size, and `h t=ceil(log₂(n(t)+1))`; minimum height is the corresponding floor. | Chapter 4 optimality and logarithmic height results supply the derivation. Keep `n+1`, not `n`, at the empty boundary. |
| C11-018 | The almost-completeness argument also works when every sibling-size difference has absolute value at most 1, without choosing the left side as larger. | `acomplete_Node_if_wbal2`, `acomplete_if_wbalanced`. This does not imply that those trees have contiguous Braun indices. |
| C11-019 | Source support: valid Braun shape is uniquely determined by node count after erasing labels. | `braun_unique` is stated for `Unit` labels. Useful for shared shape/canonical representation arguments; it does not assert equality of trees carrying different payloads. |

## 11.3 Basic implementation and correctness: pp. 130–133

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-020 | `lookup1 (N l a r) i` returns `a` for `i=1`, otherwise recurses on `l` for even `i` and `r` for odd `i`, at `i/2`. | Empty case is unspecified in HOL. Optional empty lookup is suitable; recursion terminates structurally on the tree even at `i=0`. Reuse `BinaryTree.get` for positive indices with an explicit bridge. |
| C11-021 | `update1 i x E=N E x E`; on a node replace root at `i=1`, otherwise update the parity-selected child at `i/2`. | Preserve the leaf insertion for **every** raw `i`, rather than silently returning empty, failing, or constructing an entire missing path. Valid-index guarantees are separate. |
| C11-022 | `adds [] m t=t`; `adds (x::xs) m t=adds xs (m+1) (update1 (m+1) x t)`. | This is sequential high-end extension in input order. It is not the linear-time constructor in §11.5.3 or existing `toRA`. |
| C11-023 | Raw tree abstraction `L E=[]`; `L(N l a r)=a :: sp (L l) (L r)`. | `List.interleave` is the exact `sp`. A standard inorder/BFS traversal is not definitionally equal to this recurrence. |
| C11-024 | `sp [] ys=ys`; `sp (x::xs) ys=x::sp ys xs`; `length(sp xs ys)=length xs+length ys`. | Exact Batteries operation and length theorem; preserve asymmetric base call in any cost model. |
| C11-025 | `length(L t)=n(t)` for arbitrary trees. | `size_list`; follows from `length_interleave`, without Braun validity. |
| C11-026 | Arithmetic descent: if `B(N l a r)`, `1≤i≤n(N l a r)` and `i>1`, then odd `i` gives `1≤i/2≤n r`, even `i` gives `1≤i/2≤n l`. | `div2_in_bounds`. Both positivity and upper bounds are needed for valid recursive lookup/update calls. |
| C11-027 | If `j<length xs+length ys`, `length ys≤length xs≤length ys+1`, then `(sp xs ys)[j]=(if even j then xs else ys)[j/2]`. | `nth_splice`. Can use Batteries `interleave_ofFn_ofFn_even/odd` plus list extensionality, or prove the same indexing law. Derived selected-index bounds are part of the proof-domain formulation. |
| C11-028 | Equation (11.1): `B t ∧ i<n(t) → (L t)[i]=lookup1 t (i+1)`. | `nth_list_lookup1`; zero/one-based adapter must be explicit. |
| C11-029 | Equation (11.2): `B t → L t = map (lookup1 t) [1..<n(t)+1]`. | `list_eq_map_lookup1`. A valid-index map or optional list traversal avoids a global default; prove every listed index succeeds. |
| C11-030 | List extensionality: equal lengths and equal valid-index observations imply equality, and conversely. | Reuse standard List extensionality, not a duplicate axiom. This supports the lookup-based update proof. |
| C11-031 | `B t ∧ 1≤i≤n(t) → n(update1 i x t)=n(t)`. | `size_update1`; raw invalid updates may extend the shape. |
| C11-032 | Same hypotheses imply `B(update1 i x t)`. | `braun_update1`; proof depends on the exact unchanged-size result. |
| C11-033 | Same valid-update hypotheses, but **arbitrary query `j`**: `lookup1 (update1 i x t) j = if i=j then x else lookup1 t j`. | `lookup1_update1`. Under optional lookup the true branch becomes `some x`; invalid/zero queries return the unchanged failure result. Do not unnecessarily restrict `j` or introduce a payload default. |
| C11-034 | Same hypotheses imply `L(update1 i x t)=(L t).set (i-1) x`. | `list_update1`; subtraction is safe because `i≥1`. The alternative source proof `list_update2` is not a distinct behavior obligation. |
| C11-035 | Alternate proof support: under the splice length/bounds hypotheses, updating `sp xs ys` at `j` updates the selected side at `j/2` and splices again. | `list_update_splice`; useful exact standard-operation bridge. Both even/odd branches are required if this proof route is used. |
| C11-036 | Equation (11.3): `B t → n(update1 (n(t)+1) x t)=n(t)+1`. | `size_add_hi`; the source permits an explicit equality `m=n(t)` for the cached argument. |
| C11-037 | Equation (11.4): `B t → B(update1 (n(t)+1) x t)`. | `braun_add_hi`. This extension theorem is separate from existing-index preservation. |
| C11-038 | Equation (11.5): `B t → L(update1 (n(t)+1) x t)=L t ++ [x]`. | `list_add_hi`; requires the Braun index layout, not merely height balance. |
| C11-039 | If `length ys≤length xs`, then `sp (xs++[x]) ys=sp xs ys++[x]`. If `length xs≤length ys+1`, then `sp xs (ys++[y])=sp xs ys++[y]`. | Exact instances of `interleave_append_left/right`. Do not strengthen to equal lengths or omit the asymmetric hypotheses. |
| C11-040 | If `B t` and `m=n(t)`, then `n(adds xs m t)=n(t)+length xs` and `B(adds xs m t)`. | `size_braun_adds`. Cache agreement is necessary; an arbitrary starting `m` is not valid. |
| C11-041 | Under the same hypotheses, `L(adds xs m t)=L t++xs`. | `list_adds`. Preserves list order and multiplicity. |
| C11-042 | Figure 11.3 carrier is `(t,m)`; lookup at zero-based `i` calls `lookup1 t (i+1)`; update calls `update1 (i+1) x t` and keeps `m`; `len=m`; constructor is `(adds xs 0 E,length xs)`. | Implement the actual wrapper, with optional/proof-domain lookup. No recomputing `n(t)` in each lookup/update; source uses the cached size. |
| C11-043 | Wrapper invariant is `B t ∧ m=n(t)`; abstraction ignores cache and returns `L t`. All six Array obligations hold. | Source interpretation `A` at `Array_Braun.thy` lines 147–170. Keep both validity conjuncts and every ADT law. |

## 11.3.2 Basic costs: p. 134

The source does not define these four time functions in the inspected theory;
the following rows specify the claims and a concrete route for completing their
proofs. A proposed recurrence remains unaccepted until attached to the actual
operation. Count one invocation of each recursive function, including an empty
base call, except the explicit zero-base convention of Exercise 11.8. Arithmetic,
constructor formation and primitive parity tests are unit/free primitives in the
book's abstract model, not claims about arbitrary-precision machine cost.

| ID | Source obligation | Exact model or remaining proof |
|---|---|---|
| C11-044 | Valid `lookup1` and existing-index `update1` take logarithmic time on Braun trees. | Each follows one path. For positive valid `i`, recursive invocation count is `floor(log₂ i)+1≤h(t)`. For optional invalid lookup, a separate height-plus-one bound can cover failure. Prove recurrence correspondence rather than reuse the different `fetchT` count. |
| C11-045 | High-end extension `update1 (n(t)+1) x t` costs logarithmic time. | Under `B t`, recursive invocation count is `floor(log₂(n(t)+1))+1≤h(t)+1`; the final empty-node call creates the entry. This is the count needed by `adds`. |
| C11-046 | `sp` takes time proportional to combined balanced lengths; empty-left case is constant. | Count recurrence `S([],ys)=1`, `S(x::xs,ys)=1+S(ys,xs)`. Generally `S≤length xs+length ys+1`; with `length ys≤length xs≤length ys+1`, equality holds. Value equality alone does not import this cost into another interleaving implementation. |
| C11-047 | Array-order `L` runs in `O(n log n)` on Braun trees. | Measured recursion must charge two child calls and `sp`. A uniform proof, beyond the book's complete-tree sketch, is `T_L(t)≤n(t)·h(t)+2n(t)+1` for all trees, then use Braun height. Interpret asymptotics with `log(n+1)` or an eventual `n≥2` domain. |
| C11-048 | The complete-tree level argument: at level `k<h`, there are `2^k` nodes and each splice has two lists of length `2^(h-k-1)-1`. | Correct node count is `2^h-1`, not the printed `2^h`. In the stated recursive-call model `T_L(C_h)=(h+1)·2^h`; this supplies a matching worst-case family as well as the upper estimate. |
| C11-049 | Construction by repeated high-end updates has `Θ(n log n)` cost from an empty tree. | With per-`adds` call charge 1, the exact proposed count is `1+2n+Σ(i=1..n) floor(log₂ i)`. Prove the sum bounds; unlike set insertion, every extension grows the structure regardless of duplicate payloads. Do not obtain a lower bound solely from an upper bound for `update1`. |
| C11-050 | The whole `array` wrapper remains `Θ(n log n)` after computing/storing `length xs`; `len` is constant-time cached projection. | State which nonrecursive wrapper calls are charged. Length traversal adds linear cost and does not change this asymptotic claim; omit neither actual traversal nor cache invariant from the implementation analysis. |

## 11.4 Flexible arrays: pp. 134–137, Figures 11.4–11.5

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-051 | Extend Array with `add_lo`, `del_lo`, `add_hi`, `del_hi`. For each of four operations, preserve validity; list observations are respectively `x::xs`, `tail xs`, `xs++[x]`, `dropLast xs`. | `Array_Flex` adds exactly eight laws to the six Array laws. Deletions on an empty array remain valid and empty; no nonempty premise appears. |
| C11-052 | Raw `del_hi i E=E`; on `N l a r`, return `E` for `i=1`; otherwise recursively delete in the parity-selected child at `i/2`, retaining the other child and root. | Exact source recurrence. At invalid `i=1` on a larger arbitrary tree it removes the whole tree; the correctness theorem therefore uses `i=n(t)`. |
| C11-053 | `add_lo x E=N E x E`; `add_lo x (N l a r)=N (add_lo a r) x l`. | Child swapping and passing the old root into the old right subtree implement the index shift. A normal leftmost insertion is not this operation. |
| C11-054 | `merge E r=r`; `merge (N l a r) rr=N rr a (merge l r)`. | This is the array-child merge, unrelated to sorted-list or heap merge. Both recursive arguments change to the first tree's children. Termination is structural in its first argument. |
| C11-055 | `del_lo E=E`; `del_lo (N l a r)=merge l r`. | Keep empty deletion total. This auxiliary-based definition is the baseline for Exercise 11.6. |
| C11-056 | Figure 11.5: wrapper `add_lo x (t,m)=(add_lo x t,m+1)`, `del_lo(t,m)=(del_lo t,m-1)`. | Natural cache subtraction saturates at zero. Recompute neither full tree size nor list abstraction while executing. |
| C11-057 | Wrapper `add_hi x(t,m)=(update1 (m+1) x t,m+1)` and `del_hi(t,m)=(del_hi m t,m-1)`. | Cache correctness supplies the exact index precondition; names on raw tree and wrapper must be disambiguated in Lean. |
| C11-058 | `B t → B(del_hi (n t) t)` and equation (11.6) `L(del_hi (n t) t)=dropLast(L t)`. | `braun_del_hi`, `list_del_hi`; include `t=E`, so `i=0` is allowed only in that case. |
| C11-059 | `dropLast(sp xs ys)=if length ys<length xs then sp (dropLast xs) ys else sp xs (dropLast ys)`. | `butlast_splice`, with **no Braun or length-balance hypothesis**. Retain all empty/unequal-list cases. |
| C11-060 | `B t → L(add_lo x t)=x::L t` and `B(add_lo x t)`. | `list_add_lo`, `braun_add_lo`; together with list length prove cache increment. |
| C11-061 | `B(N l a r) → L(merge l r)=sp (L l) (L r)`. | `list_merge`. The condition is validity of an assembled parent, hence includes the precise sibling-size relation; independent validity of `l,r` alone is insufficient. |
| C11-062 | Same parent-Braun condition implies `B(merge l r)`. | `braun_merge`; combine with its list law to establish the size of deletion. |
| C11-063 | `B t → L(del_lo t)=tail(L t)` and `B(del_lo t)`. | `list_del_lo`, `braun_del_lo`; include empty/singleton cases. |
| C11-064 | All eight flexible-array equations and preservation laws hold for the cached pair representation. | Source interpretation `AF`, lines 237–264. Previously proved high-end insertion laws discharge only two of the eight new laws. |
| C11-065 | All four flexible-array operations have logarithmic worst-case time on Braun trees. | Charge their actual single recursive branch; raw `merge l r` follows descendants of `l`. Bounds by `h+O(1)` follow, then `h=ceil(log₂(n+1))`. `del_lo` wrapper and `merge` entry costs must be stated; no list reconstruction occurs operationally. |

## 11.5.1 Fast size: pp. 137–138

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-066 | `diff E m=0`; on a node return 1 when `m=0`, otherwise recurse right at `m/2-1` if `m` is even, left at `m/2` if odd. | `Array_Braun.diff`. This helper follows a different parity branch from `lookup1`; preserve its truncated subtraction and early return. |
| C11-067 | `size_fast E=0`; `size_fast(N l a r)=let m=size_fast r; 1+2m+diff l m`. | Compute right size once and share it. Replacing the call by ordinary `n(r)` would have the same mathematical value on valid inputs but a different algorithm and cost. |
| C11-068 | `B t ∧ n(t)∈{m,m+1} → diff t m=n(t)-m`. | Source `diff`. Both size alternatives, including `m=0`, are essential. Without the relation the helper need not compute the difference. |
| C11-069 | Lemma 11.3: `B t → size_fast t=n(t)`. | Source `size_fast`; use the helper contract and the right-child recursion. |
| C11-070 | Time is quadratic in tree height, as made precise by Exercise 11.8's upper bound. | The prose reference to Exercise 11.3 is wrong. The source value theory has no `T_diff`/`T_size_fast` theorem; retain the full exercise as a cost gap. |

## 11.5.2 Shared initialization: pp. 138–139

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-071 | `braun_of_naive x 0=E`; for `n>0`, `m=(n-1)/2`; odd `n` constructs `N (f m) x (f m)`, even `n` constructs `N (f(m+1)) x (f m)`. | Exact two-recursive-call algorithm; identical calls in the odd branch are not implicitly memoized in the source. Termination uses both argument sizes strictly smaller than `n`. |
| C11-072 | The displayed naive initializer has the claimed `O(n log n)` upper bound. | This is a loose bound, not a `Θ(n log n)` claim: in the recursive-call model its exact count is `2n+1` (or `n` if empty calls are free), hence linear. Preserve this distinction when explaining why sharing improves it. |
| C11-073 | `braun2_of x 0=(E,N E x E)`; for positive `n`, compute `(s,t)=braun2_of x ((n-1)/2)` **once**; odd returns `(N s x s,N t x s)`, even returns `(N t x s,N t x t)`. | Preserve the shared recursive pair and repeated references. Expanding each component independently would destroy the logarithmic invocation recurrence. |
| C11-074 | If `braun2_of x n=(s,t)`, then `n(s)=n`, `n(t)=n+1`, and both trees are Braun. | `braun2_of_size_braun`; all four conclusions, including the base pair, are needed. |
| C11-075 | Under the same pair equality, `L s=replicate n x` and `L t=replicate (n+1) x`. | `braun2_of_replicate`; list equality, not just an element set or count. |
| C11-076 | `braun_of x n=fst(braun2_of x n)`; `B(braun_of x n)` and `L(braun_of x n)=replicate n x`. | `braun_braun_of`, `list_braun_of`; the pair operation is the actual implementation. |
| C11-077 | Shared initializer takes logarithmic time. | Recursive-call recurrence `T(0)=1`, `T(n>0)=1+T((n-1)/2)` gives `floor(log₂(n+1))+1`. Constructors/pair projections have fixed local charge; the logical expanded tree still has `n` nodes. Physical sharing/allocated-node claims require a separate runtime/storage model. |

## 11.5.3 Linear list-to-tree conversion: pp. 139–143

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-078 | For nonempty `xs`, `brauns k xs` takes `ys=take (2^k) xs`, `zs=drop (2^k) xs`, recursively computes `ts=brauns (k+1) zs`, and returns `nodes ts ys (drop (2^k) ts)`; empty `xs` returns `[]`. | `brauns`, lines 435–440. Pass **all** `ts` as left list; the source deliberately omits `take (2^k) ts`. Restore neither this extra traversal nor an unrelated level-order routine without a checked value/cost bridge. |
| C11-079 | Termination: on nonempty input, `length(drop (2^k) xs)<length xs`, since `2^k≥1`. | Recursion is on decreasing list length while `k` increases. A structural recursion on `k` or fixed tree height is not available here. |
| C11-080 | `nodes` with nonempty left, payload and right lists constructs `N l x r` and recurses on all tails. | `nodes` first equation. Payload list controls output length; there are no ordering requirements. |
| C11-081 | Three remaining nonempty-payload cases: left-only uses `N l x E`, right-only `N E x r`, neither uses `N E x E`; recurse consuming available side heads and payload head. | Preserve all padding cases, including the right-only case that may not arise under certain Braun-level premises. A truncating `zipWith3` is not equivalent. |
| C11-082 | `nodes ls [] rs=[]`, ignoring remaining side lists. | Exact fifth equation; no equal-length hypothesis or shape test. |
| C11-083 | `brauns1 []=E`; nonempty input extracts index 0 from `brauns 0 xs`, whose length is 1. | `brauns1`; prove the nonempty/index domain before extraction, or give a total optional internal interface with success proof. `Tree α` itself has `E`, so a payload default is unnecessary. |
| C11-084 | `take_nths i k []=[]`; on a cons, when `i=0` emit the head and reset offset to `2^k-1`, otherwise skip head and decrement offset. | Exact source helper, lines 338–341; period is `2^k`, not `k`. The conceptual result selects positions `i+j·2^k`. |
| C11-085 | Equation (11.7): `take_nths i k (drop j xs)=take_nths (i+j) k xs`. | `take_nths_drop`; no index-bound hypothesis. |
| C11-086 | Equation (11.8): `take_nths 0 0 xs=xs`. | `take_nths_00`; period 1 base is important for top-level conversion. |
| C11-087 | Equation (11.9): `sp (take_nths 0 1 xs) (take_nths 1 1 xs)=xs`. | `splice_take_nths`; all lists, including empty. |
| C11-088 | Equation (11.10): `take_nths i m (take_nths j k xs)=take_nths (i·2^k+j) (m+k) xs`. | `take_nths_take_nths`; both offset multiplication and period addition must be preserved. |
| C11-089 | Equation (11.11): `take_nths i k xs=[] ↔ length xs≤i`. | `take_nths_empty`; valid for every natural `k`, because the period is positive. |
| C11-090 | Equation (11.12): `i<length xs → head(take_nths i k xs)=xs[i]`. | `hd_take_nths`; explicit nonempty proof or `head?=some` equality. |
| C11-091 | Equation (11.13): if `length xs=length ys` or `length xs=length ys+1`, extracting offsets 0 and 1 with period 2 from `sp xs ys` gives `xs` and `ys`. | `take_nths_01_splice`; neither direction of length imbalance can be swapped. |
| C11-092 | Equation (11.14): counts of even/odd-position extractions are equal or the first is one larger. | Source name `length_take_nths_00` despite parameters `0,1` and `1,1`. Use its statement rather than infer from the name. |
| C11-093 | Companion support: `take_nths i k xs` equals the standard indexed subsequence at positions `i+j·2^k`. | `take_nths_eq_nths`. This can justify standard-library reuse after verifying operation order and multiplicity; mere set equality is insufficient. |
| C11-094 | `braun_list E xs ↔ xs=[]`; on `N l a r`, require nonempty `xs`, root `a=head xs`, left related to `take_nths 1 1 xs`, right to `take_nths 2 1 xs`. | Exact recursive graph predicate. The offsets are 1 and 2 in the **full** list, not 0 and 1; these account for the root. |
| C11-095 | Lemma 11.4: `braun_list t xs ↔ B t ∧ xs=L t`. | `braun_list_eq`; both directions are used by fast forward/inverse conversion. |
| C11-096 | Equation (11.15): `length(nodes ls xs rs)=length xs`. | `length_nodes`, no side-size or Braun hypotheses. |
| C11-097 | Equation (11.16): for `i<length xs`, output node `i` has payload `xs[i]`, left `ls[i]` if present else `E`, right `rs[i]` if present else `E`. | `nth_nodes`; each side gets its own domain test. |
| C11-098 | Equation (11.17): `length(brauns k xs)=min(length xs,2^k)`. | `length_brauns`; required for both child-index domains and top-level extraction. |
| C11-099 | Theorem 11.5: if `i<min(length xs,2^k)`, then `braun_list ((brauns k xs)[i]) (take_nths i k xs)`. | `brauns_correct`; all four left/right-padding cases in `nodes` must be handled, even though the prose expands only one representative case. |
| C11-100 | Corollary 11.6: `B(brauns1 xs)` and `L(brauns1 xs)=xs`. | `brauns1_correct`; uses `i=k=0` for nonempty input and a separate empty case. |
| C11-101 | Equation (11.18): `T_nodes ls xs rs=length xs+1`. | Shared Appendix B B-028; exact generated count, no Braun, side-length, order or nonempty assumptions. Attach to actual `nodes`. |
| C11-102 | `T_brauns k []=1`. Nonempty cost is 1 plus `T_take(2^k,xs)`, `T_drop(2^k,xs)`, recursive `T_brauns(k+1,zs)`, `T_drop(2^k,ts)`, and `T_nodes(ts,ys,drop(2^k,ts))`. | Preserve the primitive-zero exponent convention and all five costs. The empty test branch is inside the final `+1`. The generated recurrence evaluates the already defined value `ts`; it does not charge a second recursive construction. |
| C11-103 | Simplified recurrence for nonempty input of length `q`: `3·(min(2^k,q)+1)+(min(2^k,q-2^k)+1)+T_brauns(k+1,drop(2^k,xs))+1`. | `T_brauns_simple`, lines 503–505; uses `T_take=T_drop=min(request,length)+1`, exact nodes cost and exact result length. |
| C11-104 | Lemma 11.7: `T_brauns k xs≤9·(length xs+1)` for every `k,xs`. | `T_brauns_ub`. Replace the printed equality at the IH substitution with `≤`; all natural subtraction/min identities and nonempty progress must be justified. |
| C11-105 | Consequently `brauns1` and the corresponding array constructor have linear abstract time. | Add only the actually chosen wrapper, extraction and cached-length computation costs. Source time omits exponent computation by assumption; an implementation with nonconstant Nat exponent or different prefix handling needs an explicit adapter/analysis. |

## 11.5.4 Linear tree-to-list conversion: pp. 143–146

| ID | Source obligation | Reuse or precise remaining work |
|---|---|---|
| C11-106 | `list_fast_rec ts`: filter out `E` into `us`; if empty return `[]`; otherwise output `map value us ++ list_fast_rec (map left us ++ map right us)`. | Exact ordering is **all left children followed by all right children** at a level. Pairwise left/right interleaving, ordinary queue BFS, and recursive inorder are different executions. |
| C11-107 | Selectors return node payload and respective children; they are only used after the nonempty-tree filter. | Shared BinaryTree child operations fit. Obtain payload via pattern matching on filtered nodes/proof of nonemptiness, not `Inhabited α`. Recognizing `E` needs no payload equality. |
| C11-108 | Termination: for nonempty `us` containing no `E`, the sum of child node counts is strictly less than the sum of input node counts. | `list_fast_rec_term1`, `list_fast_rec_term`; use measure `Σ(t∈ts) n(t)`, with list multiplicities. Forest list length can increase and is not a termination measure. |
| C11-109 | Top level `list_fast t=list_fast_rec [t]`. | Preserve the singleton forest; an empty tree becomes one filtered-out entry, relevant to exact constants. |
| C11-110 | Proof support: all-empty forests produce `[]`; `braun_list t [] ↔ t=E`; nonempty graph predicate exposes a node with the two offset-related children. | `list_fast_rec_all_Leaf`, `braun_list_Nil`, `braun_list_not_Nil`. These remove all unsafe selector applications. |
| C11-111 | If `length xs-i<2^k`, then `take_nths i k xs=take 1 (drop i xs)`. | `take_nths_eq_single`. This is the stronger source lemma used in the short-input branch of the printed proof. |
| C11-112 | Theorem 11.8: if `length ts=2^k` and every `i<2^k` satisfies `braun_list(ts[i],take_nths i k xs)`, then `list_fast_rec ts=xs`. | `list_fast_rec_correct`; equal forest length is essential to this statement. Generalizing to arbitrary forests requires another invariant, not deleting the premise. |
| C11-113 | Short-input proof branch `length xs<2^k`: `ts=map (fun x => N E x E) xs ++ replicate (2^k-length xs) E`. | Prove pointwise with the graph predicate and short extraction lemma. Correct the printed duplicated left-child condition to one condition on each child. |
| C11-114 | Long-input branch: each root is `xs[i]`, left graph uses offset `i+2^k` with period `2^(k+1)`, right uses `i+2·2^k`; root list is `take (2^k) xs`, recursive child result is `drop (2^k) xs`. | Retain exact offsets and concatenate-left-then-right order. `length xs≥2^k≥1` ensures the recursive input list is strictly shorter. |
| C11-115 | `B t → list_fast t=L t`. | `list_fast_correct` from Theorem 11.8 at `k=0`. This equality is not unconditional for arbitrary trees; an explicit five-node counterexample is below. |
| C11-116 | The prose proposes deriving an efficient fold that visits elements in index order. | Supply a concrete fold scope, such as a fused fold over the same forest order, with `foldl`/`foldr` correspondence to `L t` and linear structural overhead plus the callback costs. A mere `fold (list_fast t)` gives correct order but materializes the intermediate list; state which construction is chosen. |
| C11-117 | Specialized cost wrappers: filtering nonempty nodes and each of `map left`, `map right`, `map value` cost `length input+1`; selectors and nonempty test cost zero as primitives. | Source lines 574–607 explicitly replace problematic generated higher-order map/filter calls with named wrappers. The generic Chapter 1 map recurrence can differ; prove the specialized recurrence bridge rather than copying a constant. |
| C11-118 | Simplified time recurrence: with `us=filter(nonempty,ts)`, `T_fast(ts)=length ts+2` if `us=[]`; otherwise `length ts+1+5·(length us+1)+T_fast(children)+1`. | This charges filter, three maps, two appends and the recursive entry according to the source convention. `children=map left us++map right us`; neither append is free. |
| C11-119 | Equation (11.19): if every tree in `ts` is nonempty, `Σ n(ts)=Σ n(map left ts++map right ts)+length ts`. | `sum_tree_list_children`; finite **list sum**, retaining duplicate tree references. No Braun invariant is required. |
| C11-120 | Theorem 11.9: `T_fast(ts)≤14·Σ n(ts)+length ts+2` for every forest. | `T_list_fast_rec_ub`; no Braun, power-of-two length, or array-order premises for this **cost** theorem. Correct a printed equality to `≤`; use the node-sum induction measure. |
| C11-121 | Singleton specialization: `T_fast([t])≤14·n(t)+3`; `list_fast` has linear abstract time. | Any counted nonrecursive outer wrapper adds its own fixed cost. Combine correctness only when `B t`, but do not unnecessarily restrict the standalone cost bound. |

## 11.6 Exercises: pp. 146–147

| ID | Exercise and exact obligation | Reuse, assumptions and solution boundary |
|---|---|---|
| C11-122 | Exercise 11.1: direct proof `B t → 2^(h t)≤2·n(t)+1`, followed by `h t=ceil(log₂(ell t))`, without first proving almost-completeness. | Retain the requested independent argument. Combine the new bound with general `ell(t)≤2^(h t)`; handle `t=E` separately where needed. Citing Lemma 11.2 alone does not solve this exercise. |
| C11-123 | Exercise 11.2: define left-spine height `lh E=0`, `lh(N l a r)=lh l+1`; prove `B t → lh t=h t`. | A shared spine definition from Chapter 4 can be reused. The property depends on left-biased Braun shape, not symmetric weight balance alone. |
| C11-124 | Exercise 11.3: prove `B(N l a r) → h l=h r ∨ h l=h r+1`, using size/optimal-height facts in a readable proof. | This is the **height** analogue of the size invariant, not the quadratic `size_fast` exercise. Show both lower and upper height relations explicitly. |
| C11-125 | Exercise 11.4: `m≤length xs ∧ bal m xs=(t,zs) → B t`, for Chapter 4's prefix-consuming `Balance.bal`. | Reuse the actual `bal` recurrence, subtree size theorem and split sizes `m/2`, `m-1-m/2`. It consumes input in **inorder**, so this does not say its Braun array-order list equals the input. |
| C11-126 | Exercise 11.5 defines `nat_of []=1`, `nat_of(b::bs)=2·nat_of bs+(if b then 1 else 0)`. Construct `lookup_trie` using false/true for left/right and empty bit list for the root. | Reuse `BinaryTree.get` through an explicit bit-list-to-`PosNum` conversion if appropriate. Bit-list interpretation is least-significant-bit first; positivity, parity and quotient lemmas follow by induction. |
| C11-127 | Exercise 11.5 lookup law: `B t ∧ 1≤nat_of bs≤n(t) → lookup_trie t bs=lookup1 t (nat_of bs)`. | Optional/proof-domain version must prove success on this stated valid domain. An implementation can prove stronger path equality, but must still exhibit the book statement. |
| C11-128 | Exercise 11.5 update law: define `update_trie` and prove **unconditionally** `update_trie bs x t=update1 (nat_of bs) x t`. | On `E`, insert the singleton regardless of remaining bits; on a node with empty bits update its root; otherwise update the selected child. Do not add Braun or index-range hypotheses absent from this equality. |
| C11-129 | Exercise 11.6: define a recursive `del_lo2` with no auxiliary function and prove `del_lo2 t=del_lo t` for every tree. | A concrete solution has clauses `E↦E`, `N E a r↦r`, `N (N l b r) a rr↦N rr b (del_lo2 (N l b r))`. The recursive argument is the old left child. Prove unconditional equality, not only list equivalence on Braun inputs. |
| C11-130 | Exercise 11.7: prove `L(braun_of_naive x n)=replicate n x`. | Retain the displayed naive algorithm; the fast initializer's theorem is not a solution without proving the algorithms equal. Simultaneous size/Braun properties are useful supporting facts. |
| C11-131 | Exercise 11.8: define `T_diff` and `T_size_fast` with zero cost in empty base cases and prove `T_size_fast t≤(h t)^2`. | Concrete convention: `D(E,m)=0`; `D(node,0)=1`; other node cases add 1 to the chosen recursive `D`; `S(E)=0`, `S(N l a r)=1+S(r)+D(l,size_fast r)`. This counts every nonempty invocation. Prove `D(t,m)≤h(t)` and then `S(t)≤h(t)^2`; the inequalities hold even without Braun validity. If the early-return `m=0` case is also assigned zero, record that different convention and its equally valid bound rather than conflating counts. |
| C11-132 | Make the prose's quadratic-height description precise without claiming an unproved lower bound on every input. | Under C11-131's stated convention, the complete-tree family satisfies `D(C_h,n(C_h))=h` and `S(C_h)=h(h+1)/2`, so the upper bound is worst-case sharp up to constants. The exercise itself explicitly asks for the upper bound; this family is a supporting completion of the surrounding asymptotic description. |

## Additional harmonization and coverage discipline

| ID | Connected obligation | Required disposition |
|---|---|---|
| C11-133 | Canonical valid Braun-array representation and operation squares against `List α`. | Reuse `Squares.Rep`, `Squares.Square` and standard optional lookup/update observations. Prove decode/encode and validity independently; a canonical encode/decode result needs array-order injectivity on valid Braun trees, not just equality of sizes. This is integration work, not a new source theorem attributed to the book. |
| C11-134 | Relate simple and fast constructors/converters on valid inputs, with identical list semantics and the same payload order. | Their semantic agreement does not equate their resource counts. The simple constructor is repeated extension; fast `brauns1` groups levels; shared `braun_of` has an intensional sharing argument. |
| C11-135 | Preserve meaningful source defects as corrected checked propositions and small checked examples, with editorial-only defects documented. | Use the explicit dispositions below. A prose correction or this inventory is not itself a checked Lean counterexample or theorem. |

## Source defects, weak estimates and precise dispositions

1. **Out-of-range list update, p. 127.** The prose calls both list lookup and
   update underdefined beyond the length. Appendix A explicitly gives the
   empty-list update equation, and the recursively derived update at an
   out-of-range index returns the original list. For example
   `[1,2].set 2 9=[1,2]`, while optional lookup at 2 gives `none`.
   Preserve this difference. The Appendix A inventory and architecture's
   reported candidate example `Examples.ListLibrary.invalid_index_and_update`
   identify intended shared boundary evidence; that candidate is not yet in
   the canonical checkout inspected here, and this note does not certify its
   integration or validation. No weakened total list-update contract is warranted.

2. **Right-subtree example, p. 132.** The subtree rooted at index 3 is printed
   with list `[1,3,5,7,9,11,13,15]`, including the overall root 1. Its correct
   list is `[3,5,7,9,11,13,15]`. Together with the left list
   `[2,4,6,8,10,12,14]`, splice and an additional root 1 produce `[1,…,15]`.
   The printed list has length 8 although the drawn subtree has 7 nodes;
   retain a small tree/list calculation as the correction witness.

3. **Closed interval definition, p. 132.** The definition uses
   `{k ∣ m≤k ∧ k≤m}` where its upper endpoint must be `n`. For `m=1,n=2`,
   the printed right side omits 2. All chapter interval hypotheses must use
   the standard `{m,…,n}` meaning `m≤k≤n`, as the formal companions do.

4. **Complete-tree size, p. 134.** The running-time paragraph identifies
   node count `n` with `2^h`; the correct equation is `n=2^h-1`, while
   empty-leaf count is `ell=2^h`. A singleton has `h=1,n=1,ell=2`.
   The `O(n log n)` conclusion survives; prove it using the corrected
   correspondence and a uniform Braun bound, not the false equation.

5. **Wrong exercise reference, p. 138.** Quadratic time for `size_fast` is
   Exercise 11.8, not 11.3. The latter is the sibling-height relation.
   Both exercises remain required.

6. **Naive initializer estimate, p. 138.** `O(n log n)` is a true but loose
   upper bound, not a false statement requiring a counterexample. The
   displayed unshared binary recursion does only `2n+1` recursive calls in
   the one-per-call model. Do not turn the printed upper bound into a false
   matching lower bound. The pair-sharing version reduces invocation count
   to logarithmic; a tree's extensional node count does not measure its
   physically shared allocation graph.

7. **IH substitution sign, Lemma 11.7 proof, p. 143.** The line replacing
   `T_brauns(k+1,zs)` by `9(length zs+1)` is printed with `=`; it is `≤`.
   Companion lines 523–527 use `≤`. For `k=0` and singleton input,
   `zs=[]`, so the two displayed expressions are `4+1+5=10` and
   `4+9+5=18`. Retain this numerical witness if formalizing the false step;
   the lemma itself is correct.

8. **Duplicated child and variable names, Theorem 11.8 proof, p. 144.**
   The short-input argument writes the left-child empty predicate twice;
   one must be the right-child predicate. It also writes `t!i` where the
   forest is named `ts`. These are local prose errors; the actual graph
   predicate and companion proof have separate left and right obligations.

9. **Absorbing the constant, Theorem 11.9 proof, p. 145.** The displayed
   step from `14Σchildren+7·length us+length ts+9` to
   `14Σchildren+14·length us+length ts+2` is `≤`, not `=`. The difference
   is `7·(length us-1)`, nonnegative because `us≠[]`. For a forest of two
   singleton trees the expressions are 25 and 32. Companion lines
   700–705 contain the correct inequality.

10. **Forest induction measure, p. 145.** The phrase “size of `ts`” must
    mean total node count, as in the termination discussion and formal
    source, not list length. A one-tree forest with two nonempty children
    recurses to a two-entry forest. Record the measure explicitly.

The p. 132 and p. 143–145 relevant formulas were inspected in rendered PDF
pages, not inferred only from text extraction. Small independent Python
calculations checked the displayed numerical counterexamples and the following
boundary example; these are exploration evidence, not formal acceptance.

### Non-Braun fast-conversion boundary

Let `t=N (N E 2 (N E 8 E)) 1 (N (N E 5 E) 3 E)`. Then
`L t=[1,2,3,8,5]`, while `list_fast t=[1,2,3,5,8]`. This five-node tree
fails Braun validity in its left child. It demonstrates why the correctness
premise cannot be dropped even though the linear **cost** theorem holds on
all forests. Keep this as a useful checked domain example, not as a defect in
Theorem 11.8 or the source implementation.

### Cost assumptions that must remain visible

- `T_brauns` explicitly sets exponentiation cost to zero. The book suggests
  constant-time table lookup when `k` is bounded. This is a conditional
  implementation rationale, not an unbounded arbitrary-precision Nat-cost
  theorem. Carrying a width that doubles can be an implementation option,
  but needs recurrence/value correspondence and its own arithmetic model.
- The source's `list_fast_rec` time construction contains a documented
  workaround for higher-order map/filter translation: named specialized
  wrappers have stipulated `length+1` costs. Reusing a generic map cost
  without reconciling callback/selector charges can change the constants.
- `nodes` and both fast-conversion time bounds quantify over their full
  displayed domains. Do not add Braun or side-length assumptions merely
  because a later correctness theorem needs them.
- The fast initializer's repeated subtree references support sharing in the
  intended functional execution. Lean value equality proves extensional
  content; exact retained-space or target allocation claims need a separate
  observation model. No such physical claim is silently certified here.
- The direct `L` converter and `adds` are still required after fast versions
  exist. Substituting faster code and attaching the slower source recurrence
  would not formalize the algorithms described in the chapter.

## Handoff for eventual implementation

Start with the shared `BinaryTree` and the existing `List.interleave` operation;
connect positive-bit lookup before creating any new equivalent API. Establish
the Braun invariant, interval characterization and array-order abstraction,
then basic/flexible operations and all 14 interface laws. Preserve the two
separate conversion algorithms and the pair-sharing initializer. The exact
`take_nths`/`braun_list` infrastructure connects both linear conversions and
their source-specific orders. Reuse B-028 for `nodes`, but prove every larger
recurrence correspondence and its own domains. Complete all eight exercises,
the stated index-order fold scope, source corrections and connected
representation/resource examples before requesting chapter acceptance. No
checkbox or row in this inventory currently means a checked Lean theorem.

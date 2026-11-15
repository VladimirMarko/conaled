# Chapter 5 source obligations: Binary Search Trees

Status: **queued; source inventory only**. This note does not activate Chapter 5,
implement a Lean declaration, or certify chapter coverage. It records original
coverage requirements and prospective reuse so recovery does not depend on the
continued availability of an evolving manuscript. Read with `../DECISIONS.md`.
The user requested the whole book, so optional reading sections and mathematical
exercise conclusions remain formalization obligations.

## Pins, provenance, and inspected sources

- Book: July 27, 2026 version, Chapter 5, printed pp. 59–76 (PDF pp. 65–82),
  authors Tobias Nipkow and Bohua Zhan. Official PDF:
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>.
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  Page numbers below are printed page numbers. Pages 65 and 75 were also rendered
  and inspected to distinguish printed mistakes from text extraction errors.
- Isabelle companion: <https://github.com/isabelle-prover/mirror-isabelle> at
  commit `f86f290225eebcc52c1ae7dba2e098f405f51c21`. All files in the following
  table were read. Their license is the repository's BSD-3-Clause `COPYRIGHT`,
  SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
  This is the exact inspected companion revision; it is not a claim that the
  evolving official PDF was generated from that commit.
- Conaled reuse inspection: baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`;
  Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679` / release v4.35.0.
  Chapter 1 work proceeding concurrently does not imply that later BST code
  exists. No matching integrated BST/interval-tree implementation was found in
  the inspected `Applications`, `SquareKit`, and `Examples` Lean files.
- Primary companion URLs are obtained by appending the source path to
  `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`.

| Source path | SHA-256 | Chapter role |
|---|---|---|
| `src/HOL/Data_Structures/Tree_Set.thy` | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | Unbalanced BST operations; sorted-list refinement; both deletion variants |
| `src/HOL/Data_Structures/Tree_Rotations.thy` | `745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea` | Listification; positioned rotations; exact number; inverse schedule |
| `src/HOL/Data_Structures/Interval_Tree.thy` | `0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2` | Nonempty intervals, cached endpoint maximum, update/search correctness |
| `src/HOL/Data_Structures/Cmp.thy` | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` | Three-way comparator and its branch laws |
| `src/HOL/Data_Structures/Sorted_Less.thy` | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` | Strict sorting framework, including (5.1)–(5.4) |
| `src/HOL/Data_Structures/List_Ins_Del.thy` | `988921eb88b03519ec3dd365ec90e5fdcead0736065e188e99fc47f7bf206af3` | Ordered duplicate-suppressing insertion, one-occurrence deletion, (5.5)–(5.8) |
| `src/HOL/Data_Structures/Isin2.thy` | `f6b0c6574c8fa618b5d42f3045e9af32731afd80a061173d8bc09eae9808df0c` | Membership search through augmented labels, ignoring annotations |
| `src/HOL/Data_Structures/Set_Specs.thy` | `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0` | Set laws and ordered-list-to-set composition; shared with Chapter 6 |
| `src/HOL/Data_Structures/Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` | Annotation-erasing inorder/set observations |
| `src/HOL/Library/Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` | Chapter 4 tree carrier, height, size, inorder, strict BST invariant |

### Additional pinned source for the sweep-line application

The book cites Zhan 2018, *Efficient verification of imperative programs using
auto2*, DOI <https://doi.org/10.1007/978-3-319-89960-2_2>, for the interval-tree
and rectangle-intersection development. Its public AFP entry is
<https://isa-afp.org/entries/Auto2_Imperative_HOL.html>, *Verifying Imperative
Programs using Auto2*, dated December 21, 2018, licensed BSD. A dated archive
listed by that official entry was downloaded and inspected:

- <https://isa-afp.org/release/afp-Auto2_Imperative_HOL-2026-10-26.tar.gz>,
  SHA-256 `fb60c5d0b1ad9864f0ff0aa615e1522d4ace0be1a56db6c7bf5ae0fdd3f8b6bb`.
- `Auto2_Imperative_HOL/Functional/Interval.thy`, saved for research as
  `book-source/Auto2_Interval.thy`, SHA-256
  `8beda04266632402d535a18130ea083ac64fd43d735e377c926f67ad7e272813`.
- `Auto2_Imperative_HOL/Functional/Rect_Intersect.thy`, saved for research as
  `book-source/Auto2_Rect_Intersect.thy`, SHA-256
  `10fd8b006de4d7b64c48825998e0aa415a3d3e92d4a266a20836d97f612318e0`.

This AFP source is a related formalization, not an identical implementation of
every equation in this chapter. In particular, it tags intervals with rectangle
indices; its functional driver is specialized to natural endpoints; it uses an
explicit validity predicate rather than the book's nonempty-interval subtype;
and its proved functional correctness is not a certificate of the chapter's
conditional balanced-tree `O(n log n)` bound. No full manuscript or external
source text is copied into this control note.

## Conventions, assumptions, and prospective reuse

Write `E` for an empty tree and `N(l,a,r)` for a node, `size t` for internal
nodes, `h t` for height with `h E=0`, and `S xs` for **strict** sortedness with
respect to `<`. Node labels need a linear order for the BST algorithms and
their specification through lists. Rotation results require no order and no
distinctness of labels. The general set interface itself does not require an
order. Separate those hypotheses instead of imposing a linear order globally.

Chapter 2's sortedness uses `<=` and permits duplicates. Here `S` is equivalent
to nondecreasing sortedness plus no duplicates, not to that earlier predicate
alone. `bst` is strict in both subtrees. The Chapter 4 inventory records the
resulting correction to the list-to-BST claim for duplicate inputs.

Use explicit valid-domain/`Option` adapters for source operations whose empty
case or unmatched pattern is unspecified in HOL: `split_min`, `rotR`, `rotL`,
and `apply_at` at a nonexistent position. Prove that constructed schedules and
deletion calls stay in the domain. Source equations on valid inputs must remain
recoverable; an arbitrary global default must not enter public semantics.

Reuse labels in this note are **R** (existing directly relevant infrastructure),
**P** (partial match requiring a checked bridge), **G** (gap), or **X** (a
cross-chapter dependency). These are inspection findings, not checked coverage.

| Candidate | Reuse assessment and boundary |
|---|---|
| Mathlib `BinaryTree` in `Mathlib/Data/Tree/Basic.lean` | R/P: the correct empty-leaf, node-labelled carrier; `numNodes`, `numLeaves`, `height`, `map`, and basic laws already exist. Constructor order is `node value left right`, unlike source notation. Chapter 4 owns the inorder/BST foundation; reuse it here. |
| Conaled `Applications/Sequences/RandomAccess/Basic.lean` and `Applications/Resources/TreeFlattening/Core.lean` | Methodological reuse only: these use leaf-labelled nonempty trees / their erasures, not the BST carrier. Cached size validity and value/cost separation are useful patterns, but do not identify these trees by name. |
| Standard `List.Pairwise`, list membership/append, `List.erase`, `Set` | R/P: support strict-list and set observations. Source `del_list` removes the first equal element, so bridge it to `List.erase`; its set-difference law needs no duplicate of the erased value (strict sorting is sufficient). |
| Existing conaled stable sorting | P for the sweep event ordering and sortedness/perm contracts. `List.orderedInsert` and the project's insertion sorter retain duplicates; they are not the source `ins_list` which suppresses an equal key. |
| Mathlib `NonemptyInterval` in `Mathlib/Order/Interval/Basic.lean` | R/P for endpoint validity, interval-as-set, and point membership. Its default order is **containment** (`t.low<=s.low` and `s.high<=t.high`), not the book's lexicographic endpoint order. Use an explicit lawful comparator/order wrapper with a bridge, not a silent replacement of its global instance. |
| Chapter 6 set representation/specification work | X: the general composition theorem should be shared. Chapter 5 needs concrete checked set clients and the direct proof route requested by Exercise 5.3, not only an interface declaration. |
| Later balanced-search-tree chapters | X: required for the unnumbered balanced interval-tree exercise and for an instantiated `O(n log n)` sweep bound. Record a concrete accepted balanced realization and cache-preservation proof before claiming that dependency discharged. |

## 5.1–5.3 Unbalanced sets and correctness: pp. 59–63

| ID | Exact obligation / source location | Reuse or gap |
|---|---|---|
| C05-001 | Define `bst E=True`; `bst N(l,a,r)` asserts all labels in `l` are `<a`, all in `r` are `>a`, and both subtrees are BSTs (p.59). Prove the Chapter 4 carrier/observation bridge if not already present. | P/X: strict property; tree set semantics ignore multiplicity but the invariant forbids duplicate labels. |
| C05-002 | Set operations interface (p.60): `empty : Rep`, `insert,delete : α -> Rep -> Rep`, `isin : Rep -> α -> Bool`. Abstract operations/laws need no linear order; ordered concrete representations do. | X Chapter 6. Keep operations, representation invariant, semantic laws, and algorithm-specific cost observations separate. |
| C05-003 | Three-way `cmp`: LT iff `x<y`, EQ iff `x=y`, GT iff `y<x`; branch elimination law. Definitions p.60; companion `Cmp.LT`, `EQ`, `GT`, `case_cmp_if`. | P: standard `Ordering`/lawful comparator machinery is a candidate. A custom primitive comparator needs explicit agreement with the chosen order. No runtime speedup follows from that agreement alone. |
| C05-004 | `empty=E`; `isin E x=False`; a node compares the query to its label, searches only the selected child, or returns true on equality (p.61). | G/P: structural recursion plus C05-003. BST hypothesis belongs to its membership theorem, not its definition. |
| C05-005 | `insert x E=N(E,x,E)`; LT/GT rebuild exactly the selected path, EQ returns the original node unchanged (p.61). | G. Retain duplicate suppression and structural behavior; do not replace this recurrence by repeated insertion into a sorted list without correspondence. |
| C05-006 | `split_min` on nonempty `N(l,a,r)`: if `l=E`, return `(a,r)`; otherwise recurse into `l` and rebuild the remaining left path (p.61). | G. Expose a valid domain or failure result; no order assumption is needed to remove the first inorder label. |
| C05-007 | If nonempty `t` yields `(x,t')`, prove `x :: inorder t' = inorder t`; on a BST derive that `x` is a least stored label and the remainder is a BST with `x` removed (p.61's successor explanation; source `split_minD`). | G/P: the first identity is unconditional in labels; leastness and set removal need the strict invariant. |
| C05-008 | Deletion by replacing (p.61): empty stays empty; LT/GT recurse on one child; EQ returns the left child when the right is empty, otherwise replaces the label by the right subtree's inorder successor and uses its residual tree. | G. All `split_min` calls must carry/prove nonemptiness; no stale-root label may survive the EQ branch. |
| C05-009 | `join` recurrence (p.62): either empty input returns the other; for two nodes, recurse on their facing subtrees, then rebuild either `N(t1,a,N(E,b,t4))` for empty result or `N(N(t1,a,u2),x,N(u3,b,t4))` for result `N(u2,x,u3)`. | G. Preserve both reconstruction cases. This is not the simpler `join0`. |
| C05-010 | `inorder (join l r) = inorder l ++ inorder r` for arbitrary trees (p.62; source `inorder_join`). Derive size additivity and the ordered/disjoint-bound BST consequence when applicable. | G/P: no BST hypothesis belongs to the inorder equality. |
| C05-011 | Deletion by joining `delete2`: same LT/GT recursion as deletion, EQ returns `join l r`; prove `inorder (delete2 x t)=del_list x (inorder t)` under strict sortedness and the full set/invariant laws (p.62; `inorder_delete2`, interpretation `S2`). | G. Both deletion variants are in the chapter even though later text concentrates on replacing. |
| C05-012 | Define `join0` with the same empty cases and `join0 N(t1,a,t2) N(t3,b,t4)=N(t1,a,N(join0 t2 t3,b,t4))` (p.62). | G. This deliberately less balanced algorithm is part of Exercise 5.2, not an implementation substitute. |
| C05-013 | The p.62 claim that deletion using `join` or replacing never increases height: prove `h(delete x t)<=h t` and `h(delete2 x t)<=h t`, using the split-min height bound and C05-018. | G. These structural height results can be proved for arbitrary labels/trees; avoid adding BST unnecessarily. They do not assert balancing or logarithmic height. |
| C05-014 | Set semantics (p.63): `set_tree empty={}`; under `bst t`, insertion gives `set_tree t ∪ {x}`, deletion gives `set_tree t \ {x}`, and `isin t x` iff `x∈set_tree t`. | G/P: exact four semantic obligations. Include both supported deletion clients via C05-011. |
| C05-015 | Validity (p.63): `bst empty`; `bst t -> bst(insert x t)`; `bst t -> bst(delete x t)` and the corresponding delete2 law. | G/P. Semantic correctness may not be used in place of preservation. |
| C05-016 | Every tree reachable from `empty` by a finite sequence of interface updates satisfies the invariant (p.63's justification for assuming it). | G/P: use a generated-state relation or trace induction and C05-015; not a claim about arbitrary externally constructed trees. |
| C05-017 | Exercise 5.1 (p.60): define all-node triples `nodes t`; define `bst_nodes` by both strict subtree bounds at every such triple; prove `bst_nodes t ↔ bst t`. | G. The exercise asks for the recursive/nonrecursive characterization, not a renaming of `bst`. |
| C05-018 | Exercise 5.2, first part (p.62): `h(join l r) <= max (h l) (h r) + 1`. | G. Exact additive constant 1, all trees. |
| C05-019 | Exercise 5.2, second part: prove `h(join0 l r) <= h l + h r`. This is a suitable explicit answer to the requested upper-bound function. | G. A coarser bound without the following tightness witness does not answer the exercise. |
| C05-020 | Exercise 5.2 tightness: if both inputs are complete, prove `h(join0 l r)=h l+h r`, including empty inputs. For equal nonzero child height k, deleting the root with join0 can change height from `k+1` to `2*k`, explaining the near doubling (p.62). | G/P: Chapter 4 completeness. Small independent evaluations for heights 0–5 support the proposed target but are not a Lean proof. |
| C05-021 | Exercise 5.3 (p.63): establish all seven p.63 obligations **directly from the recursive BST/set definitions**, without the later inorder/sorted-list detour. | G. Retain this genuinely different proof route; an alias to C05-041 alone does not satisfy the requested exercise method. No duplicate public API is needed. |
| C05-022 | Exercise 5.4 (p.63): define a terminating `union_tree` on two BST representations. | G. Open-ended implementation choice; record a concrete solution and its operational recurrence. |
| C05-023 | Exercise 5.4 suggested split-based solution: define `split_tree x t=(lt,gt)` with sets exactly the labels `<x` and `>x` in `t`; prove both outputs are BSTs for `bst t`. The equal key is excluded from both sides. | G. The hint is a good reusable method; if a different solution is chosen, still document how it answers the exercise and which split obligations are included or solved separately. |
| C05-024 | Exercise 5.4 result: under `bst t1` and `bst t2`, prove `set_tree(union_tree t1 t2)=set_tree t1 ∪ set_tree t2` and `bst(union_tree t1 t2)`. | G. No asymptotic bound is stated in this exercise; do not invent one from the operation's name. |

## 5.4 Sorted-list refinement and reusable proof laws: pp. 64–67

The author's permission to skip this section as a reader does not remove it
from the user's requested coverage. Its useful deliverable is a Lean library
of semantic/refinement laws and concrete consumers, not imitation of Isabelle's
simplifier syntax. The source's `NO_MATCH`, `ASSUMPTION`, and simplifier bundles
are proof-engineering devices; their mathematical statements are below.

| ID | Exact obligation / source location | Reuse or gap |
|---|---|---|
| C05-025 | `bst t ↔ S(inorder t)` and `set_tree t = {x \| x∈inorder t}` (p.64). Strict sortedness has empty/singleton true and adjacent `x<y` recursion; prove equivalence to the chosen all-pairs relation. | P/X Chapter 4 plus standard list relation facts. Do not reuse Chapter 2's `<=` relation without the no-duplicates bridge. |
| C05-026 | `ins_list` (p.64): empty becomes singleton; at `a::xs`, prepend if `x<a`, keep the whole list if `x=a`, otherwise recurse after `a`. | G/P. It suppresses the first equal occurrence it reaches; sortedness is needed for a sorted-set representation, not for defining the function. |
| C05-027 | `del_list` (p.64) deletes the first equal occurrence, scans past every unequal head, and returns empty on empty. | P: `List.erase` with checked orientation/decidable equality; no early `<` termination in the displayed recurrence. |
| C05-028 | Figure 5.1 (p.65): inorder of empty is empty; under `S(inorder t)`, inorder of insert equals `ins_list`, inorder of delete equals `del_list`, and membership search agrees with membership in inorder. | G/P: companion `inorder_insert`, `inorder_delete`, `isin_set`. This is the intermediate specification, with no separately assumed BST invariant beyond the strict inorder premise. |
| C05-029 | (5.1), p.66: `S(xs++y::ys) ↔ S(xs++[y]) ∧ S(y::ys)`. | P: `Sorted_Less.sorted_mid_iff`. |
| C05-030 | (5.2): `S(x::xs++y::ys) ↔ S(x::xs) ∧ x<y ∧ S(xs++[y]) ∧ S(y::ys)`. | P: `sorted_mid_iff2`; keep parsing explicit in Lean. |
| C05-031 | (5.3): `S(x::xs) -> S xs`. | R/P: `sorted_cons`. |
| C05-032 | (5.4): `S(xs++[y]) -> S xs`. | R/P: `sorted_snoc`. |
| C05-033 | (5.5): assuming only `S(xs++[a])`, insertion into `xs++a::ys` equals `ins_list x xs ++ a::ys` if `x<a`, otherwise `xs++ins_list x (a::ys)`. | P/G: `ins_list_sorted`; no sortedness hypothesis on suffix `ys` belongs here. |
| C05-034 | (5.6): under `S(xs++a::ys)`, deletion distributes to the left prefix if `x<a`, otherwise to the suffix `a::ys`. | P/G: `del_list_sorted`. It has the stronger whole-list premise, unlike C05-033. |
| C05-035 | (5.7): `S(x::xs) ↔ (∀y∈xs, x<y) ∧ S xs`. | R/P: `sorted_Cons_iff`. |
| C05-036 | (5.8): `S(xs++[x]) ↔ S xs ∧ (∀y∈xs, y<x)`. | R/P: `sorted_snoc_iff`. |
| C05-037 | `set(ins_list x xs)=set xs ∪ {x}` for every list, with no sortedness premise (p.67; `set_ins_list`). | G/P. Preserve the weaker hypothesis boundary. |
| C05-038 | Under `S xs`, `set(del_list x xs)=set xs \ {x}` (p.67; `set_del_list`). | P. Without distinctness the statement is false, e.g. removing 1 once from `[1,1]`. Retain that boundary example if exposing a broader deletion contract. |
| C05-039 | `S xs -> S(ins_list x xs)` (p.67; `sorted_ins_list`). | G/P. |
| C05-040 | `S xs -> S(del_list x xs)` (p.67; `sorted_del_list`). | P. |
| C05-041 | Compose Figure 5.1 with C05-037–040 and the inorder/set bridge to derive the four abstract set laws and three invariant laws (pp.66–67). | G/X: source `Set_by_Ordered` sublocale `Set`. Reuse one general representation/refinement composition framework with Chapter 6; show the unbalanced implementations instantiate it. |

## 5.5 Positioned rotations and exact rotation counts: pp. 67–71

This section counts **rotations**, not all recursive calls, allocation, path
traversal, or machine time. In particular a list of k positions can cost more
than k to execute in an immutable tree. The book proves a linear number of
rotations; it does not give a linear-time implementation of all positional
updates. Preserve that distinction in any resource interface.

| ID | Exact obligation / source location | Reuse or gap |
|---|---|---|
| C05-042 | Define right rotation of `N(N(A,a,B),b,C)` as `N(A,a,N(B,b,C))`, with left rotation the inverse on its matching shape (pp.67,70). | G/P: use valid domains or explicit failure; neither source operation supplies a meaningful unmatched-case result. |
| C05-043 | Legal rotations preserve inorder (and therefore size, set labels, and strict BST), and opposite rotation undoes a legal rotation (diagram p.67; supporting C05-058). | G/P. Height need not be preserved. Label order, not just label set, is the semantic invariant. |
| C05-044 | `is_list E=True`, `is_list N(l,a,r)=(l=E ∧ is_list r)`; characterize list form as no legal right rotation applicable at any position (p.68). | G. This characterization needs a notion of legal position/rotation, not arbitrary HOL completion. |
| C05-045 | `rlen E=0`, `rlen N(l,a,r)=rlen r+1`; prove `rlen t<=size t` (pp.68,70; `rlen_le_size`). | G/P. No BST or order assumption. |
| C05-046 | `list_of` recurrence (p.68): a node with nonempty left child right-rotates at the root and recurses; `N(E,a,A)` retains its root and recurses on `A`; empty remains empty. | G. General recursion changes shape while preserving size. |
| C05-047 | Terminate C05-046 with natural measure `2*size t-rlen t`. Prove its strict decrease in both branches; `size-rlen` fails to decrease in the right-child branch (p.68). | G/P. The failure is an exact equality of the smaller proposed measure on `A` and `N(E,a,A)`, not evidence of nontermination. |
| C05-048 | `is_list(list_of t)` and `inorder(list_of t)=inorder t` (p.68; `is_list_rot`, `inorder_rot`). | G. |
| C05-049 | Positions are lists of L/R. Define `apply_at`, and sequential `apply_ats` where the first position is evaluated against the current tree, followed by the remaining positions (p.69). | G. Handle invalid positions explicitly; the whole schedule is state-dependent, so legality is not just validity of each position in the initial tree. |
| C05-050 | `rotR_poss` recurrence (p.69): in the root-rotation case prepend the empty path and continue on the rotated tree; in `N(E,a,A)` prefix R to every position for `A`; empty gives no positions. | G. Preserve schedule order. |
| C05-051 | Terminate C05-050 with `2*size-rlen`, and prove every emitted rotation is legal when executed in order. | G. The source has a measure proof; explicit schedule legality is necessary to make its partial operations meaningful in Lean. |
| C05-052 | Sequential action law (p.70): applying `ps1++ps2` means apply `ps1` and then `ps2`. | P/G: `apply_ats_append`; use the corresponding bind law if the public interpreter returns `Option`. |
| C05-053 | (5.11), p.70: applying paths all prefixed R to `N(l,a,r)` yields `N(l,a,apply_ats f ps r)` on valid executions (or the corresponding lifted equality). | P/G: `apply_ats_map_R`. Generic transformation f need not be a rotation. |
| C05-054 | (5.9): applying `rotR_poss t` yields list form. | G: `is_list_rotRs`. |
| C05-055 | (5.10): the same execution preserves inorder. | G: `inorder_rotRs_poss`. |
| C05-056 | (5.12): `length(rotR_poss t)=size t-rlen t`, exact for every tree including empty. | G: `length_rotRs_poss`. This counts schedule entries, all of which are actual rotations by C05-051. |
| C05-057 | `size t-rlen t <= size t-1` in natural subtraction; for nonempty trees with `rlen t=1`, the schedule uses exactly `size t-1` rotations (p.70; `size_rlen_better_ub`). | G/P. The empty tree uses zero. Lower-bound optimality among arbitrary legal schedules is separately C05-065. |
| C05-058 | (5.13): left-rotate at the reversed `rotR_poss t` schedule after right-listifying t to recover t. Prove reverse execution legal (p.70; `rot_id`). | G. This is an actual inverse trace, not just equality of inorder observations. |
| C05-059 | (5.14): two list-form trees with equal inorder are equal (p.70; `is_list_inorder_same`). | G/P. No requirement that labels be distinct. |
| C05-060 | If `inorder t1=inorder t2`, listify t1 by its own schedule and undo t2's listification using reverse left rotations; the result is t2 (p.71; `tree_to_tree_rotations`). | G. Equal node count alone is insufficient for differently labelled trees. |
| C05-061 | The constructed tree-to-tree schedule has at most `2*n-2` rotations for common positive node count n (pp.67–71). State an empty-safe natural-subtraction version or separate n=0 case. | G/P: follows from the two exact counts and equal inorder lengths. It is a rotation bound, not an allocation/time bound. |
| C05-062 | Exercise 5.5 (p.71): define `count_rots` by the same recursive branches as `list_of`, charging 1 only for an actual rotation and 0 for descending the list-form root; prove `count_rots t=size t-rlen t`. | G. Do not simply define it as the right-hand arithmetic expression or as the length of an unrelated schedule; correspondence to `list_of` is the point. |
| C05-063 | Exercise 5.6 (p.71): prove existence of positions that produce list form and preserve inorder **by induction without defining or using `rotR_poss` or a comparable schedule-computing function**. | G. A relational/existential induction proof can share legal rotation facts. Calling C05-050 and wrapping its result in an existential does not satisfy this exercise. |
| C05-064 | Exercise 5.7, first question: provide a legal schedule to list form longer than `rotR_poss`. One witness is `t=N(N(N(E,1,E),2,E),3,E)` and paths `[[L],[],[R]]`, length 3; the generated schedule has length 2 (p.71). | G. An independent small evaluation confirmed all three steps legal and the final chain `[1,2,3]`; Lean witness remains required. |
| C05-065 | Exercise 5.7, second question: no legal sequence of right rotations reaches list form with fewer than `size t-rlen t` steps. Prove each right rotation raises the whole tree's `rlen` by at most 1, preserves size, and list form has `rlen=size`. | G. Off-spine rotations may raise whole-tree rlen by 0. The bound is about valid rotations, not arbitrary evaluations of source underspecified cases. C05-056 attains it. |

## 5.6 Interval trees: pp. 71–75

The endpoint carrier needs a linear order for intervals and overlap. The cached
empty-tree maximum additionally needs a bottom element. Keep `OrderBot` local
to that representation; neither nonempty interval construction nor overlap
semantics requires it. An optional `WithBot` cache adaptation needs a checked
source correspondence, not a silent new model. Intervals are closed, may be
singletons, and may overlap each other. Insertion/deletion are operations on
whole interval values, not geometric union, clipping, or point removal.

| ID | Exact obligation / source location | Reuse or gap |
|---|---|---|
| C05-066 | Augmented BST membership compares only the logical label in `(a,annotation)` and ignores the annotation (p.71). Prove membership iff in erased inorder / erased tree set under the strict BST invariant. | P/X: Chapter 4 erasure plus `Isin2.isin_set_inorder`, `isin_set_tree`. No cache validity premise is needed for equality-key membership. |
| C05-067 | Represent a nonempty closed interval by low/high with `low<=high`, endpoint extensionality, and the **lexicographic** order low first, high second (p.72; `ivl_is_interval`, `ivl_inj`, `ivl_less`, `ivl_less_eq`, order instance). | P: `NonemptyInterval` data can be reused with a distinct lawful comparator/order wrapper. Both equal-low/different-high intervals must be ordered correctly. |
| C05-068 | `overlap x y ↔ low y<=high x ∧ low x<=high y`; prove it iff the two closed interval sets have nonempty intersection (p.72's reader challenge). Derive symmetry. | P/G: basic `Set.Icc` laws; this mathematical challenge remains a Lean obligation even though it is unnumbered. Nonempty intervals are essential. |
| C05-069 | `has_overlap S y ↔ ∃x∈S, overlap x y` (p.72). | R/P: independent abstract observation; do not bake a tree representation into it. |
| C05-070 | Augmented carrier `(interval α × α)` in a binary tree; `max_hi E=bot`, nonempty `max_hi` reads the root cache; `max3 a l r=max (high a) (max (max_hi l) (max_hi r))` (pp.72–73). | G/P: Chapter 4 augmentation. Constant-time access requires that cached field, not recomputing the maximum by traversal. |
| C05-071 | `inv_max_hi` means every node's cache equals `max3` and both children recursively satisfy it; empty is valid (p.73). | G. This invariant is independent of BST order. |
| C05-072 | Lemma 5.1: valid cache and `a∈set_tree t` imply `high a<=max_hi t` (p.73; `max_hi_is_max`). | G/P. No BST premise. |
| C05-073 | Lemma 5.2: valid cache and nonempty t imply some stored interval attains `max_hi t` (p.73; `max_hi_exists`). | G/P. Merely an upper bound is not enough for the one-branch overlap-search proof. |
| C05-074 | Smart constructor `node l a r=N(l,(a,max3 a l r),r)` and its erasure/cache laws (p.73). | G/P. Root recomputation alone does not repair invalid descendant caches. |
| C05-075 | Interval insertion uses the BST recurrence with smart reconstruction in LT/GT; singleton cache is `high x`; EQ returns the original annotated node (p.73). | G. This distinction matters on invalid cached inputs; do not claim insertion repairs arbitrary corrupt caches. |
| C05-076 | Interval `split_min` and deletion use the p.61 algorithms but smart-rebuild all changed nodes (pp.73–74). Preserve the explicit nonempty domain of `split_min`. | G/P. Erased inorder split-min identity is independent of cache/BST validity. |
| C05-077 | Under strict sorted erased inorder, interval insert/delete refine `ins_list`/`del_list` exactly (p.74; `inorder_insert`, `inorder_delete`). | G/P: reuse the list proof framework; these value laws do not require valid caches. |
| C05-078 | Valid caches are preserved by insert, by nonempty split-min's residual tree, and by delete (p.74; `inv_max_hi_insert`, `inv_max_hi_split_min`, `inv_max_hi_delete`). | G. These structural cache laws do not require BST ordering. |
| C05-079 | `invar=inv_max_hi ∧ S∘inorder`; derive empty/set-membership/insert/delete semantics and invariant preservation, and instantiate an interval-set contract with overlap observation (p.74; companion `Interval_Set`, interpretation `S`). | G/X. Do not check only the four displayed update corollaries while omitting the underlying empty and equality-membership laws. |
| C05-080 | `search E x=False`; node first tests overlap with its interval, then searches left iff left is nonempty and `low x<=max_hi left`, otherwise right (pp.74–75). | G. This searches one branch, not both. Correctness relies on cache **attainment** and ordered low endpoints. |
| C05-081 | Left-branch pruning lemma (p.75 proof): if the branch condition holds yet the left subtree has no overlap, an attained-max witness implies every right-subtree low exceeds `high x`; hence the right has no overlap. | G/P. Keep left nonemptiness, cache validity, and the low-endpoint monotonicity induced by the lexicographic BST order visible. |
| C05-082 | Right-branch pruning lemma: empty left has no overlap; otherwise `max_hi left<low x` and C05-072 exclude overlap with every left interval (p.75 proof). | G/P. |
| C05-083 | Theorem 5.3: `inv_max_hi t ∧ S(inorder t)` implies `search t x ↔ has_overlap(set_tree t) x` (p.75; `search_correct`). | G. Includes empty tree, boundary intersection, singleton intervals, and overlapping stored intervals. |
| C05-084 | Exercise 5.8 (p.75): define point membership `low iv<=x ∧ x<=high iv`; implement a separate recursive `search1` **without using interval `search`**; prove under cache validity and BST that `search1 t x` iff some stored interval contains x. | G/P. A correctness relation to searching singleton `[x,x]` can be proved afterward, but defining search1 by that call alone does not satisfy the exercise. |

## 5.6.6 Balanced augmentation and sweep-line application: p. 76

This page contains an unnumbered exercise and an algorithm with a correctness
claim and asymptotic bound. They are retained as obligations. Because balancing
is taught later, the state must say **waiting for a named cross-chapter
dependency**, not mark all Chapter 5 mathematics complete after only the
unbalanced interval tree. A generic conditional theorem can be proved first;
the concrete balanced instance must eventually discharge its hypotheses.

| ID | Exact obligation / source location | Reuse or gap |
|---|---|---|
| C05-085 | Unnumbered exercise: augment a balanced binary search tree, e.g. the red-black tree named by the text, with endpoint maxima while retaining ordered-set semantics, balancing invariants, and interval-overlap search correctness. | G/X. A concrete selected balance scheme plus cache-aware rotation/update proofs is a legitimate documented solution to the open-ended exercise. A generic theorem can share the required low-order/cache laws; merely saying the augmentation is possible is not formal coverage. |
| C05-086 | Define nonempty closed axis-aligned rectangles and intersection as a common point, including boundaries. For a finite input, generate an insertion at its lower y and deletion at its upper y, both carrying its x interval (p.76). | G/P. For list input use distinct occurrence identifiers so duplicate rectangle values remain different objects; or explicitly specify a finite set of rectangles and prove the adapter. AFP uses indices. |
| C05-087 | Sort events by increasing y with **every insertion before every deletion at equal y**; prove exactly two events per input occurrence, event identity/uniqueness, and the insertion-before-own-deletion law, including zero-height rectangles (p.76). | P/G: existing stable sorter supplies sortedness/permutation, but the event comparator must encode this tie rule. Ordinary sort on y alone is insufficient without a carefully proved initial/stable ordering convention. |
| C05-088 | Starting from empty active intervals, process events: on insertion query overlap before inserting; return true immediately if found; otherwise insert and continue; on deletion remove exactly that rectangle's interval; return false at exhaustion (p.76). Prove termination and the active-set invariant for each processed prefix. | G. AFP `apply_ops_k`, `xints_of`, `apply_ops_k_next1/2`, `apply_ops_k_next_is_correct` provide source proof structure. Share one precomputed sorted event list in the implementation used for the time bound. |
| C05-089 | Prove soundness and completeness: the sweep returns true iff there are distinct input rectangle occurrences whose closed regions intersect (p.76). | G: AFP `has_overlap_at_k_equiv`, `has_overlap_at_k_equiv2`, `has_overlap_equiv`, `rect_inter_correct`. Its indexed-interval semantics need a checked bridge to the chapter's simpler interval payload. Boundary cases must be included. |
| C05-090 | Prove the p.76 conditional `O(n log n)` bound using a sorter with a checked worst-case `O(n log n)` cost and a balanced interval representation whose insert/delete/overlap query cost is `O(log(n+1))` while active size is at most n. Account for event creation, 2n events, sorting, state updates, queries, and early termination. | G/X. Use `n*log(n+1)` or eventual asymptotics with n=0/1 handled. No such bound follows from the unbalanced tree, from the AFP functional result alone, or from semantic equality of alternative implementations. |

### Sweep-line adapter details that must survive recovery

The AFP interval payload is `IdxInterval(interval, Nat)` and is ordered first
by the interval, then by the identifier. The abstract query ignores the index.
Its `has_rect_overlap` quantifies distinct **indices**, so two identical
rectangle records can be a positive example. The book's simple interval-set
implementation deduplicates equal whole intervals. A future implementation may
either generalize the augmented BST payload with a lawful low-endpoint
projection, retaining IDs, or prove a suitable early-exit no-collision invariant
for the simpler representation. An arbitrary set conversion of the input list
is not a valid duplicate-preserving adapter.

The functional AFP `rect_inter` equation mentions `all_ops rects` inside each
recursive call. Its semantics can be useful without granting a time bound to a
literal implementation that repeatedly sorts the same list. The book's sweep
sketch naturally allows a single sorted event list. An explicit correspondence
and separately instrumented cost should establish the intended implementation.

Boundary witness for the tie rule: rectangles `[0,1]×[0,1]` and
`[0,1]×[1,2]` share an edge. Deleting the first before inserting the second at
y=1 can miss the intersection. The insertion-first rule must be formal, not a
comment about a library sort's accidental stability.

## Other mathematical statements and chapter-note boundaries

The main construction's exact source premise is equal inorder. The chapter
notes discuss the corresponding **unlabelled shape** rotation distance for
trees with the same node count, where that condition is automatic after
forgetting labels. These statements should not be conflated.

| ID | Statement / source location | Coverage disposition |
|---|---|---|
| C05-091 | Rotation distance is the minimum number of legal left/right rotations between two shapes of common size n, and is at most `2*n-2` for n>0 (p.76, attributed to Culík II and Wood 1982). | G/P. Define the finite-path distance or an equivalent minimum certificate and derive the bound from C05-061; no need to assume a separate oracle for minimum distance. |
| C05-092 | The cited exact maximum distance is `2*n-6` for n>=11 (p.76, attributed to Sleator et al. 1986 and Pournin 2014). | G, external proof dependency. This is a precise mathematical claim in the chapter notes, not a consequence of the elementary `2*n-2` construction. A whole-book completion record must explicitly account for it; no waiver is inferred merely from its appearance in notes. The cited papers and their exact tree-size conventions still need independent source inspection before implementation. |
| C05-093 | Rotation-distance decision has polynomially checkable witnesses (p.76's NP membership statement). | G/analysis boundary. State the decision problem and size encoding explicitly; the linear-length existence bound plus polynomial verification of legal rotations is a natural formal route. The prose about whether computing exact distance is NP-complete/open is historical research-status discussion as of the pinned edition, not an axiom or a timeless theorem. |
| C05-094 | Illustrative p.67 comparison: under a uniform query among the three present keys, the shown balanced tree has expected visited-node count `5/3`, while the increasing chain has `2`. | G/P, small explicit mathematical example if retaining the prose claim. State the finite query distribution and visit-count convention; do not read it as a bound for arbitrary absent-key or nonuniform queries. |

The notes' references to other formalizations, algorithm histories, and proof
automation experience are provenance/discussion. They do not require porting
all implementations in every cited paper. Conversely, a concrete mathematical
conclusion explicitly stated in the chapter, such as C05-092, should not be
silently erased from the coverage ledger because its proof is external.

## Source defects, counterexamples, and domain pitfalls

1. **Printed type error, p.65.** The motivating insertion calculation ends in
   `ins_list x t`, where t is a tree. The intended final term is
   `ins_list x (inorder t)`, as confirmed by the displayed target immediately
   above and companion `inorder_insert`. This is visible in the rendered PDF,
   not introduced by text extraction. Retain the correction in the source map;
   no countermodel to an ill-typed expression is required.
2. **Printed argument-order typo, Exercise 5.8, p.75.** One prose occurrence
   says `search1 x t` even though the declared type and final theorem use
   `search1 t x`. Use the typed specification and record the correction.
3. **Refuted companion lemma is not a theorem.** `Tree_Rotations.thy` contains
   an attempted assertion that every right-rotation schedule ending in list
   form is no longer than the generated one. It invokes
   `quickcheck[expect=counterexample]` and ends in `oops`. C05-064 gives a small
   legal counterexample; C05-065 gives the correct opposite minimality result.
   Do not port an aborted declaration as an assumption or coverage witness.
4. **Right-spine growth qualification.** Each rotation in the chosen
   top-down/right-spine strategy increases the whole tree's right-spine length
   by one. A right rotation elsewhere can leave that length unchanged: the
   first `[L]` step of C05-064 does exactly that. The valid general lower-bound
   fact is increase **at most** one, which supports the exercise's optimality
   answer. This is a context qualification of the p.70 explanation.
5. **Strict versus nonstrict order is mathematically material.** A list
   `[1,1]` is nondecreasing but not strictly sorted, and deleting one occurrence
   still leaves 1 present. Do not use Chapter 2's sortedness as the only
   hypothesis of C05-038 or the BST/list refinement without a distinctness
   bridge. Chapter 4 also records the resulting list-to-BST counterexample.
6. **Partial HOL operations.** `split_min E`, rotating a shape without the
   required child, or descending beyond a leaf are not specified by the source
   equations. In particular, arbitrary schedules must not be accepted as legal
   proof objects merely because HOL denotes some value for every application.
   Use the explicit domain/failure policy in `DECISIONS.md` and prove generated
   traces stay valid.
7. **Incorrect cache weakening is unsound.** The search proof needs both the
   upper-bound law and an attained maximum. An inflated cache can make search
   commit to an empty-of-matches left branch while the right contains a match.
   Concrete future counterexample: left interval `[0,0]` cached as 100, root
   `[1,1]`, right `[2,2]`, query `[2,2]`. All endpoint upper-bound inequalities
   and strict interval BST order hold, but root non-overlap plus the inflated
   left cache sends search left and returns false (take root cache 100 and
   right-leaf cache 2 to specify the entire annotated tree). Proper cache equality rules
   out this tree. Preserve such a checked boundary witness if exposing a
   weakened cache contract.
8. **Endpoint-order mismatch in reuse.** Mathlib interval containment is not
   lexicographic endpoint order; `[0,10]` and `[1,2]` are oppositely oriented by
   containment and by lower-endpoint comparison. A default-instance shortcut
   would invalidate the search-order argument.
9. **Balanced complexity is conditional.** A chain of n increasing singleton
   intervals can require n node visits to find its last member. The chapter's
   unbalanced realization is not logarithmic. The exact counterfamily and a
   counted visit recurrence are useful checked boundaries for C05-090.

The independent Python evaluations mentioned here establish only small example
sanity checks; none is a Lean certificate. All genuine false-statement
counterexamples selected for the formal source-error record must be checked
alongside the corrected statements during implementation.

## Completion map and handoff

All eight numbered exercises have explicit rows: 5.1 C05-017; 5.2
C05-018–020; 5.3 C05-021; 5.4 C05-022–024; 5.5 C05-062; 5.6 C05-063; 5.7
C05-064–065; 5.8 C05-084. The unnumbered interval-overlap challenge and
balanced augmentation exercise are C05-068 and C05-085. The application and
its time claim are C05-086–090.

| Named or numbered result | Inventory witnesses |
|---|---|
| Figure 5.1's four refinement clauses | C05-028 |
| (5.1), (5.2), (5.3), (5.4) | C05-029, C05-030, C05-031, C05-032 |
| (5.5), (5.6), (5.7), (5.8) | C05-033, C05-034, C05-035, C05-036 |
| (5.9), (5.10), (5.11), (5.12) | C05-054, C05-055, C05-053, C05-056 |
| (5.13), (5.14) | C05-058, C05-059 |
| Lemma 5.1, Lemma 5.2, Theorem 5.3 | C05-072, C05-073, C05-083 |

Before eventual chapter acceptance, attach checked declaration names for all
applicable rows, explicit failure/domain bridges, source corrections and
counterexamples, concrete exercise solutions, representation clients, and
review/validation evidence. Keep cross-chapter dependencies visible until
actually discharged; reading the later source or writing a conditional theorem
is not a concrete balanced implementation. Source inventory is complete enough
to recover the chapter's mathematical agenda, but all substantive new Lean
coverage remains queued.

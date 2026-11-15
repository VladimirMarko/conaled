# Completeness summaries and maximal complete subtrees

This unit addresses FDSA Chapter 4's executable completeness checker and
Exercises 4.7, 4.8 and 4.10. Its source scope is the retained July 27, 2026
[chapter ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md),
rows C04-031, C04-038–041, C04-059–060 and C04-074. This is a new Lean development
against that recorded source analysis, not a claim of another manuscript read.

The existing `BinaryTree`, `Trees.fold`, structural `Subtree`, `Complete`,
`AlmostComplete` and generic `Trees.Cached` remain the shared owners. Here
complete means perfect, including the empty tree. Almost complete means that
external leaves occur on at most two adjacent levels; no left-packing condition
is imposed. The source maximum-cache exercise is a separate obligation.

## One executable Boolean and height summary

`Applications.Trees.Completeness` computes a `Bool × Nat` by one ordinary fold.
The empty summary is `(true, 0)`. At a node with child summaries `(cl, hl)` and
`(cr, hr)`, it computes

```
(cl && cr && (hl == hr), max hl hr + 1).
```

The equality test is on natural heights. There is no equality decision, order
or inhabitance requirement on labels. `check` is the flag projection of this
same summary, not another recursive checker.

The specifications are independent of the computation:

- `summary_height` identifies the second projection with `BinaryTree.height`,
  using the existing `fold_fusion` and `fold_height` laws.
- `summary_complete` reflects the first projection into the already existing
  structural `Trees.Complete` predicate.

The predicate is not defined by the algorithm's answer. Boolean computation and
Prop-valued correctness remain separate, and the executable definitions do not
use classical decidability of a proposition about the input tree.

## Exercise 4.10: a specialization of the generic cache

`Applications.Trees.CompletenessCache` specializes the existing product-labelled
tree cache to Boolean/height annotations, using the same empty value and node
algebra. The source `ch`, `nodeCh` and `invarCh` are the local reader, smart
constructor and all-node validity invariant of this specialization.

The constructor law uses `Trees.Cached.smartNode_valid_iff`: the new node is valid
exactly when both supplied children are valid. The reader law uses
`Trees.Cached.read_eq_fold`, then the two independent summary theorems. Thus a
valid cached tree's flag reflects completeness of its erased key tree, and its
height component is that tree's actual height. Existing erasure and map laws
also identify the annotated and unannotated tree shapes.

Reading an annotation and building a smart node inspect local summaries. The
generic bottom-up annotation operation is a separate full-tree computation.
Recomputing the root annotation cannot repair an invalid descendant. The checked
cache uses retain that boundary as well as complete, incomplete and empty cases.

`Examples.TreeCompleteness.localNodeRun` executes the existing
`Resources.TreeCache.nodeRun` with an explicit callback charge. Its value is
the actual `nodeCh` result, its charge is exactly the callback charge plus three
local-access charges, and valid children give a valid result. The concrete
charge-one client returns the expected annotated three-node tree at charge four.
This is the declared source model, not a machine-time claim about natural
arithmetic or comparisons.

## Exercise 4.7: one fold selecting a maximal complete subtree

`Applications.Trees.MaximalCompleteSubtree` carries four pieces of reachable
fold state: the reconstructed original subtree, its shared Boolean/height
summary, a selected complete descendant, and the selected descendant's height.
Its concrete record is `State`; `summary` is the fold and `select` exposes the
selected tree. `summary_correct` proves the reachable-state invariant and
`correct` presents structural containment, completeness and maximality without
the implementation's stored-height field.

At a node it reconstructs the current original subtree from the two supplied
child originals and combines their shape summaries once. If the resulting flag
is true, it selects that entire current tree. Otherwise it selects the child
candidate with greater stored height, resolving equality to the left.

The executable algebra calls neither `Complete`, the whole-tree checker nor
`subtrees`. It does not traverse a child again or compare trees or labels. This
meets the exercise's stronger no-tree-equality bonus at arbitrary label types.
The stored tree is an ordinary `BinaryTree`; the summary record is computation
state, not a replacement tree representation or recursion framework.

The original-tree and shared-summary projections use fold fusion. Correctness
of selection instead applies to the actual reachable fold state. If `s` is the
selected tree for input `t`, it proves all of the following:

```
Subtree s t
Complete s
stored selected height = s.height
∀ u, Subtree u t → Complete u → u.height ≤ s.height.
```

The complete-parent case uses the general `Subtree.height_le` lemma in the
existing relation owner. In the incomplete-parent case, `subtree_node_iff`
separates the impossible complete-parent candidate from the two child cases;
their induction hypotheses and stored-height comparison establish maximality.
There is no assumption that arbitrary user-supplied summary fields are correct.
The result includes nil and the parent itself, and does not assert uniqueness
when several complete descendants have the same height.

Checked applications include a whole complete input, an incomplete input whose
best child candidate is strictly taller, an empty-label nil tree, and an
observable left tie. In the tie case, root 0 has left child
`node 1 (node 2 nil nil) nil` and right child `node 3 nil nil`; the selected
singleton is rooted at 2. The distinct labels make the branch choice observable.
Structural containment and a single input fold do not assert physical sharing,
allocation counts or a machine-time bound.

## Exercise 4.8: the exact constructor law

`Trees.almostComplete_node_iff` extends the existing Shape owner with

```
AlmostComplete (node a l r) ↔
  AlmostComplete l ∧ AlmostComplete r ∧
    (l.height = r.height ∨
     (l.height = r.height + 1 ∧ Complete r) ∨
     (r.height = l.height + 1 ∧ Complete l)).
```

The right side uses only child predicates, heights, arithmetic and logical
operations. The proof may use minimum height internally: the parent's cross
bounds force the shorter child's minimum height to equal its height. The
existing completeness equivalence then supplies precisely the missing premise.

`Examples.TreeShape` connects the law to both-empty and one-empty boundaries,
equal-height but incomplete children, and the existing `almostFour` example.
It also retains `localBalanceCounter`, without introducing another copy of that
seven-node tree. Both its children are almost complete and their heights differ
by one, but its shorter child is incomplete; the parent is not almost complete.
The earlier sufficient adjacent-leaf-count criterion for balancing remains a
different, useful theorem.

## Validation and remaining coverage

The public application aggregate reaches the two new example modules. Focused
validation includes those examples and affected structural, shape, cache,
balancing and ordered-observation clients. The focused axiom audit enumerates
every declaration in all eight changed or new formal modules, including private
and generated declarations; it does not replace the whole-library audit.

Exact candidate identities, source preservation, statement assessments,
independent Standards/Spec outcomes and final comparison are recorded in the
local CTB checkpoint evidence. Maximum caches and the final 76-row chapter
qualification remain separate work. Receiving whole-library build, exhaustive
audit and final acceptance retain their separate gates.

# Structural observations and weighted paths on binary trees

CTB-72 receives the complete four-module donor tree at
`af03b76c478bf1b71b2cbe38fb05ca6a69ad91b1`, including its earlier basic-observation
pair, against pinned master `c214fb0720ffc998951255a7e4b5f2e80a299186`.
It also connects structural descendants to the existing shape predicates.
The current local CTB checkpoint owns exact candidates, validation inputs and
outcomes, independent reviews and final source comparison. Focused compilation
and the focused declaration audit pass; receiving whole-library acceptance and
the full Chapter 4 ledger remain separate, pending gates.

## Source correspondence

The source is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, July 27, 2026 edition, Chapter 4. Its pinned PDF SHA256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The retained [Chapter 4 obligation ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md)
records the manuscript and companion-theory identities and source notices.
This recovery uses that preserved analysis; it did not reacquire or independently
reread the PDF. Earlier G/P labels are historical capability assessments.

| Source obligation | Current connection |
| --- | --- |
| C04-002 | `Trees.setTree`, with independent structural empty/node equations. |
| C04-005 | `Trees.preorder`, visiting root, left and right in that order. |
| C04-014 | `Trees.Subtree`, its nil/node characterizations and transitivity, plus `subtrees`, exact set recurrences and empty/self membership. |
| Membership and preorder portions of C04-015 | Both traversal-to-set membership bridges and `preorder_length`; existing `inorder_length` remains the canonical inorder length theorem. |
| Exercise 4.3, C04-021–022 | `sumTree`, `wpld`, `wpl0`, independent `wpl`, the universally quantified offset identity and its depth-zero specialization. |
| General-subtree portion of C04-046 | `complete_of_subtree` and `almostComplete_of_subtree` in the existing Shape owner. |

Preorder label transport is a useful additional connection to the current map
interface. Enumeration, level traversal, reconstruction, rose mirroring,
maximal complete subtrees, Boolean checking, almost-complete constructor laws,
balancing and remaining cache exercises keep their own chapter obligations.

## Independent observations through the existing fold

`Applications.Trees.BasicObservations` uses the existing `BinaryTree` and
`Trees.fold`. The label-set algebra combines the independent child sets by
`left ∪ {root} ∪ right`; it is not defined as membership in a traversal. No
decidable label equality is needed. The preorder algebra combines the ordered
child lists by `root :: (left ++ right)` and retains every occurrence.

The original constructor equations remain definitional equalities. Induction
then proves that membership in either inorder or preorder agrees with the
independent set observation, and that preorder length is canonical node count.
Arbitrary relabelling commutes with preorder across independent universes;
injectivity is not assumed. A constant map of the three-node sample still
returns three labels, even though a set observation forgets their repetitions.

The worked sample is a root 9 with children 3 and 7. Its preorder is `[9,3,7]`,
inorder `[3,9,7]`, set `{3,9,7}` and node count three. A membership application
uses the preorder bridge to establish the presence of 7; another uses the
inorder bridge to reject 8. These are applications of the correspondence laws,
not substitutes for them.

## Structural descendants and shape inheritance

`Subtree s t` means that `s` is a whole rooted descendant of `t`; the smaller
tree is the first argument. Its constructors are reflexivity and inclusion
through either child. It includes the original tree and every empty leaf,
and `Subtree.trans` composes nested containment without comparing labels or
trees. The set interface is defined from this relation and proves exactly

```text
subtrees(nil) = {nil}
subtrees(node a l r) = {node a l r} ∪ subtrees(l) ∪ subtrees(r).
```

The independent repeated-label example has one two-node tree leaning left and
one leaning right. Both traversals are `[5,5]` and both label sets are `{5}`,
yet the trees differ and the left tree is not a structural subtree of the
right. Thus set equality and traversal equality do not supply structural
containment. No physical-sharing or allocation interpretation is asserted.

The existing `Applications.Trees.Shape` now imports the basic structural owner.
`complete_of_subtree` derives completeness of an arbitrary descendant using
the current `complete_node` law. `almostComplete_of_subtree` derives the
corresponding weaker invariant through `almostComplete_children`. Both proofs
induct on structural containment; neither adds a second shape predicate,
carrier or numerical criterion. The dependency points from Shape to basic
observations, with no cycle.

The new checked applications use a descendant two edges below the root.
`completeEnvelope` has the saved sample as both children and is complete.
`almostEnvelope` has that sample on the left and a singleton on the right;
its external leaves occupy depths two and three. It is almost complete and
provably not complete, so the weaker inheritance result is exercised on a
parent outside the stronger domain. Both descendant results consume the public
inheritance laws. The empty-descendant case uses `nil_subtree` with both laws.
Existing ShapeLog and TreeShape clients also compile after this extension.

## Two independent weighted-path meanings

Natural weights label every internal node. `sumTree` is the ordinary fold
adding left weight, root weight and right weight. `wpld d` uses the same fold
at the function type `Nat → Nat`: each child summary is applied to incoming
depth `d+1`, and the root contributes `(d+1)*weight`. Its public node law is
the source recurrence for every incoming depth.

`wpl0` specializes this operation to depth zero. The independent `wpl`
definition retains the source's separate recurrence: at a node it sums that
whole subtree's weight, the left child's `wpl`, and the right child's `wpl`.
It is not defined using `wpld` or the offset formula. In particular, its
subtree-weight observation remains explicit; no runtime improvement is
inferred from equal mathematical values.

The generalized induction invariant is

\[
\operatorname{wpld}(d,t)
  = d\,\operatorname{sumTree}(t)+\operatorname{wpl}(t).
\]

The induction is generalized over incoming depth, so it covers both actual
recursive calls at `d+1`. The node equations expose the independent meanings
before natural arithmetic is collected. At zero depth it yields
`wpl0 t = wpl t` for every natural-weight tree. Empty trees and zero weights
need no special assumptions.

This is the node depth-plus-one convention. The existing Huffman owner uses
labelled leaves and leaf depth, so a root leaf has depth zero. Its offset
argument is related, but its carrier and root charge differ. No interchange
between these conventions, alternate tree framework or runtime theorem is
silently introduced here.

## Connected weighted cases and boundaries

| Input | Total weight | Path value at depth zero | Value at incoming depth two |
| --- | ---: | ---: | ---: |
| Root 3 with children 5 and 7 | 15 | `3 + 2*5 + 2*7 = 27` | 57 |
| Left chain with weights 3, 5 and 7 | 15 | `3 + 2*5 + 3*7 = 34` | 64 |

The symbolic-depth sample and both depth-two results consume the public offset
theorem. The inequality between the two depth-zero values proves that equal
total weight does not determine path value. A singleton of arbitrary weight
has exactly that weight at depth zero; the concrete weight-seven case rejects
accidentally using a zero root charge. A zero-weight root above a weight-seven
child gives 14, since the root still raises the child's depth. Nil gives zero
sum and zero path value at every depth.

The original 70 public named declarations remain, with unchanged mathematical
headers and all original cases. Four matching independent observations now
use the shared fold; the source recurrence laws are retained and checked.
The added shape inheritance and nested cases express the new cross-module
connection. Statement inspection checks arbitrary labels, relation direction,
invariant transfer from parent to descendant, independent source meanings,
universal incoming depth and the depth-plus-one root convention. The focused
audit includes private/generated declarations in all four recovered modules
and the changed Shape module. It does not replace the receiving whole-library
build, exhaustive project audit or final acceptance.

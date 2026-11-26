# Canonical tree observations and ordered-set contracts

CTB-73 connects the existing binary-tree observations and ordered-search owners
against pinned master `c214fb0720ffc998951255a7e4b5f2e80a299186`. The current
CTB checkpoint records exact baseline/candidate inputs, focused validation,
independent source reviews and final comparison. Whole-library guarded build,
exhaustive project audit and receiving acceptance remain separate pending gates.

## Source scope and preservation

This unit contributes to FDSA Chapter 4 (CTB-23) and cross-book coherence
(CTB-68). The retained [Chapter 4 obligation ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md)
identifies FDSA-4-58's ordered-input prerequisite: the generic balancer requires
no label order, but its strict BST interpretation requires strictly increasing
input. Nondecreasing input alone allows repeated keys. This unit supplies the
observation characterization needed for that interpretation; it does not
implement the balancer, its worked figure, height or cost laws, or close that
source row or a chapter. The source assessment uses the retained ledger; it
does not claim a new reading of the textbook PDF or companion theory.

`Search.OrderedTree.entries` now delegates to the canonical `Trees.inorder`.
Its public name and type remain, its nil/node equations are still definitional,
and all old results are retained. The old direct-recursion proofs use the
public equations. Independent `Contains`, `All`, `OrderedBy` and `Ordered`
meanings remain unchanged. Baseline/candidate membership and insertion,
shared-tree algorithms, and their comparison or allocation contracts are
unchanged. No new tree carrier or alternative traversal is introduced.

The existing three Contents results now require `Preorder` instead of
`LinearOrder`: `ordered_entries_pairwise`, `ordered_entries_nodup` and
`finite_contents`. This is an explicit generalization. The forward proof uses
transitivity and strictness; the old linearly ordered clients remain instances
of the new domain. The actual search/insertion algorithms retain LinearOrder.

## Independent meanings and exact hypotheses

| Connection | Domain and boundary |
| --- | --- |
| `contains_iff_mem_setTree` | Every tree and label, with no ordering, decidable equality or inhabited-label premise. It connects the structural Contains predicate to the independent structural set. |
| `all_iff_mem_setTree` | Arbitrary predicates and raw trees; agreement does not imply search validity. |
| `ordered_of_inorder_pairwise` | Only `LT` is needed: pairwise order supplies every root/descendant comparison. |
| `ordered_iff_inorder_pairwise` | The implication from `Ordered` to pairwise inorder uses transitivity supplied by `Preorder`. Pairwise order is strict, not merely nondecreasing. |
| `orderedBy_of_inorder_pairwise`, `orderedBy_iff_inorder_pairwise` | The key type has the corresponding LT/Preorder assumption. The payload has no order, equality-decision or inhabitance assumption; key injectivity is not required. |

The keyed results reuse the existing `orderedBy_iff_map` bridge and canonical
`Trees.inorder_map`. The definitions are not replaced with their intended
conclusions. The converse is a structural proof; the forward implication uses
the current Contents proof. A checked nontransitive relation has low < middle
and middle < high but not low < high. Its three-node tree passes the independent
Ordered predicate while its inorder fails pairwise order, exposing why the
forward implication cannot discard transitivity.

## Existing set laws and relational composition

`AbstractSet.Laws.congr_observe` fixes operations and validity, changing only
the observer. Its premise is pointwise observer equivalence on Valid states.
The proof uses the original `empty_valid` and `insert_valid` facts precisely
where those observations are needed. It imposes no global observer equality.

`baseline_set_laws` and `candidate_set_laws` apply that theorem to the already proved
tree realizations. Thus the same operations and Ordered invariant satisfy the
independent FDSA `Trees.setTree` specification without duplicating the five
fields of AbstractSet.Laws. Existing Contains-based clients still work directly.

The checked `mixedInsertSquare` composes baseline insertion of x with candidate
insertion of y through the existing `Laws.insertSquare` and `Relational.compose`.
Its preservation proof yields Ordered validity and the precise observation
`z = y ∨ z = x ∨ z ∈ setTree t` for the actual composed program. The generic
insertion-word observation law proves equal sets for both implementations for
every list. The word `[3,1,3,2]` then consumes the existing member and validity
laws, including repeated insertion and actual membership of 2.

These results transport set meaning. The existing sample still uses four
baseline comparisons and three candidate comparisons when searching for absent
4. The connected case retains those actual counts alongside membership
agreement. No equality of measured costs or physical-sharing result follows
from the observer change.

## Connected cases and validity boundary

The examples retain the existing bad-descendant tree: a descendant 12 occurs
in the left subtree of root 10. It is not Ordered, yet its raw Contains/setTree
and All/setTree correspondences still hold. The empty tree over `Empty` checks
the absence of an inhabited-label assumption. Arbitrary keyed payloads and
function-valued payloads demonstrate the key-only order contract. A two-node
tree with repeated key 2 has nondecreasing inorder but fails the strict BST
predicate.

The observer-congruence example is a lawful singleton-element set with carrier
`Option Bool`. Empty is `some false`; insertion returns `some true`; membership
reads the stored Boolean. Exactly the Some states are valid. The original
observer is equality to `some true`, and the second is inequality to
`some false`. Their equivalence is proved on every valid state, and all five
original set laws are proved before transport. They differ at invalid `none`,
where the transported member contract without a validity premise is false.
Repeated insertion into the valid empty state consumes the transported laws.
This checks a meaningful boundary rather than assuming the desired set laws.

Focused validation covers the new example and existing ordered-tree,
ordered-map and shared-tree clients affected by the canonical redirect.
The focused audit enumerates all owned declarations, including generated and
private names, in AbstractSet, OrderedTree.Basic, Contents, Observations and
the new example. Selected elaborated statements are inspected for their
domains, relation assumptions, quantifiers and exact observations. Counts of
declarations are audit evidence, not estimates of chapter coverage.

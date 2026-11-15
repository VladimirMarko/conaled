# Shared ordered-tree observations: case preflight

Recorded 2026-11-02. This is bounded source-only preparation for a possible
cross-cutting tree interface. It does not activate a chapter, freeze a new
implementation scope, compile a theorem, or accept any saved draft. Chapter 1
remains the active chapter, with its sole full guarded run unchanged at
`07e480f6ec9958d4975bb90151005b84f2907614` in session 83124.

## Inspected interfaces and source

The root read the current saved `Applications/Trees/Observations.lean`,
`Rotations.lean`, and `Cached.lean` completely in the XT06 checkout. Their
shared carrier is Mathlib `BinaryTree`, whose constructor order is
`.node label left right`. `Trees.inorder` retains every label occurrence and
its left-root-right order. `Trees.Cached.erase` is `BinaryTree.map Prod.fst`;
cache validity is a separate recursively checked property. Successful root
rotations already have exact inorder equalities and explicit `Option` domains.
These are unaccepted draft dependencies, not newly validated library results.

Primary evidence read for the independent expectations is the pinned July 27,
2026 manuscript, Chapter 5 pp. 59–66 and Chapter 6 pp. 77–83, the Chapter 4
inventory's p. 54 correction, and the exact companion declarations in
`Tree.thy` (definitions at 90–96, comparison results at 436–451) and complete
`Sorted_Less.thy`. Chapter 5 is Binary Search Trees; Chapter 6 supplies the ADT
and key/payload map contracts. The book's Chapter 5 sortedness is strict `<`,
whereas Chapter 2's nondecreasing sorting convention is `≤`.

The companion defines a structural invariant for an arbitrary relation but
specializes its inorder equivalence to `<` and `≤`. Its all-pairs sortedness
and the manuscript's adjacent-element presentation agree through transitivity.
The source/API contributors independently identified the same missing
cross-subtree comparison in an arbitrary-relation generalization.

The manuscript PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
Selected ordinary byte identities read at this preflight:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `book-source/Tree.thy` | 17,104 | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/Sorted_Less.thy` | 2,133 | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` |
| `book-source/Tree_Set.thy` | 3,801 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` |
| `book-source/Tree_Map.thy` | 2,028 | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` |
| XT06 `Applications/Trees/Observations.lean` | 4,119 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| XT06 `Applications/Trees/Rotations.lean` | 7,436 | `d9a9aef015fbe2c3ffcc638ea8b963784adaec4d88d9b500b5a5f148264407b3` |
| XT06 `Applications/Trees/Cached.lean` | 5,668 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |

## Proposed observations, before choosing declaration names

Use `B R t` below only as mathematical notation for the proposed structural
predicate: empty is true; a node requires `B R` for each child, every left
label related by R to the root, and the root related by R to every right
label. The label quantification can use membership in the existing inorder
list without introducing a new carrier, finite-set enumeration, equality
decision, or inhabitance assumption. This is a real recursive invariant,
not merely a new name for pairwise inorder order.

The expected main bridge is `B R t ↔ List.Pairwise R (inorder t)` under
transitivity. The pairwise-to-structural direction needs no transitivity;
the other direction uses it for a left label, root, and right label. An
exact node decomposition for pairwise inorder order must include the
left-to-right comparisons if it has no transitivity premise.

For a key function `key : α → κ`, use the relation
`fun a b => key a < key b`. Payloads require no order or equality instance.
A preorder on keys suffices for strict-order transitivity and irreflexivity.
The separate converse from nondecreasing keys plus distinct keys needs
antisymmetry; a partial order suffices. The relevant distinctness is of the
**mapped key list**, not merely of full payloads.

## 1. A satisfiable ordered tree and actual rotations

The printed p. 59 tree has root 6; its left child is 3 with leaves 2 and 5;
its right child is 9 with left leaf 8 and empty right child. Its independently
specified inorder list is `[2,3,5,6,8,9]`. Every adjacent strict comparison
holds, and transitivity supplies every pairwise comparison. It therefore
satisfies the direct subtree-bound invariant as well.

A legal left rotation at its root returns a tree rooted at 9, whose left
child is rooted at 6, with the old 3-tree and leaf 8 as children; its right
child is empty. Its inorder list is again exactly `[2,3,5,6,8,9]`.

The retained case should establish the actual `rotateLeft?` result, consume
the public ordered-rotation theorem on that success, and connect the reverse
rotation through the existing inverse law. Merely recomputing both lists
independently would miss the requested preservation connection. A general
three-label specialization with premises `a < b` and `b < c` is also useful
for demonstrating how clients discharge subtree bounds without hard-coding
the printed labels.

The printed tree has height 3; this left rotation has height 4. Thus even a
strictly ordered, legal rotation need not preserve height. The existing XT06
height-changing examples may suffice for that independent boundary; no new
balance or height guarantee belongs to this interface.

## 2. Transitivity is substantive

Let `R a b` mean `b = a + 1` on natural labels, and let `t` have root 1,
left leaf 0, and right leaf 2. Its direct structural invariant holds:
the only root bounds are `R 0 1` and `R 1 2`, and each leaf is vacuously
valid. Its inorder list is `[0,1,2]`, which is not pairwise R because
`R 0 2` is false. R is not transitive, witnessed by the same triple.

The actual legal left rotation produces root 2 with left child 1, whose
left child is 0. This result fails the structural invariant because 0 is
a left descendant of 2 but `R 0 2` is false. Its inorder list is nevertheless
unchanged. This single compact family witnesses both invalid generalizations:

- Arbitrary structural subtree ordering does not imply pairwise inorder R.
- Exact inorder preservation does not by itself preserve arbitrary structural
  R-ordering without the bridge's hypotheses.

The future checked negative cases should use the actual structural predicate
and actual rotation result, not separately invented Boolean summaries. They
must preserve the expected counterexample when proof elaboration is repaired.

## 3. Strictness, repeated keys, and empty domains

A two-node tree containing 1 twice has nondecreasing inorder `[1,1]` but
fails strict BST ordering. This provides the invariant-level boundary behind
Chapter 4's p. 54 correction. It does not implement or validate the book's
balancing algorithm; its exact duplicate-output example remains a later
obligation of that algorithm.

For maps, full payload distinctness is insufficient. A root labelled `(1,10)`
with right child `(1,20)` has two unequal full pairs, but the key inorder is
`[1,1]`, so strict ordering by `Prod.fst` fails. Both full pairs can even be
increasing for the explicit lexicographic relation
`p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)`. No default product-order instance
should be relied on to express that comparison. This is the relevant
Chapter 6 boundary; a map implementation may not order by the semantic value
or reinterpret that value as a recomputable cache annotation.

The strict-key result should provide distinctness of the mapped key list,
and payload distinctness may follow from that. A generic relation's no-repeat
consequence additionally needs irreflexivity; transitivity alone permits the
universal relation and repeated labels.

Retain empty-tree and singleton cases. In particular, the empty tree over
`Empty` is admissible for any relation on that type, without an invented
label or `Inhabited` instance. A valid singleton need not have a legal root
rotation: both rotation functions return `none`. Success-conditioned laws
should not be misread as existence of a rotation on every ordered tree.

## 4. Relabeling and key-preserving payload changes

The exact pullback statement under `BinaryTree.map f` can hold for arbitrary
relations and arbitrary maps: the source relation simply becomes
`fun a b => S (f a) (f b)`. No injectivity or transitivity is needed for
that syntactic structural correspondence.

For a preservation claim with fixed semantic relations, retain the actual
relation-preservation hypothesis. Key-preserving payload changes are a useful
specialization: for `key' (f a) = key a`, strict key order is preserved.
The concrete map `(k,b) ↦ (k,())` from `Nat × Bool` to `Nat × Unit` is globally
noninjective but preserves keys. Apply it to a tree with three distinct keys;
the result remains strictly ordered and has exactly the expected mapped
inorder observations. This consumes the public transport law and does not
require any order on the payload's second component.

By contrast, the constant map on the labels of a valid two-node natural BST
collapses both keys and destroys strict ordering. The existing unconditional
`inorder_map` and rotation/map commutation still hold; they do not establish
order preservation. A strictly monotone key change is sufficient, but should
not be demanded for a merely key-preserving payload map.

## 5. Cache erasure keeps validity separate

An annotated tree with first components 1,2,3 in inorder and all stored
size tags zero is strictly ordered after `Cached.erase` but is not a valid
size cache. Conversely, bottom-up `Cached.annotate` can make every size tag
valid on a duplicate-labelled tree, whose erased labels still fail strict
ordering. These are independent predicates.

If this unit supplies an erasure or smart-rotation ordering adapter, it should
use the actual erasure/value equalities and require only the ordering needed
for that semantic conclusion. Cache validity is required for cached-value
claims, not for the erased ordering observation. Existing XT06 validity laws
retain their separate actual-fringe hypotheses. No node callback, measured
execution, tariff, recomputation cost, or balance proof is introduced here.

## Narrow scope and connection checklist

This preflight supports only a reusable structural/inorder order interface,
its precise mapping laws, and actual root-rotation consumers. It suggests a
core `Ordered.lean` importing ordinary observations and a small separate
`OrderedRotations.lean` importing the root-rotation interface. These are
proposed paths, not existing declarations or fixed implementation choices.

The strongest direct source connections are C05-001 and the invariant portion
of C05-025, with key-projected specialization for the Chapter 6 ordered-map
domain. The adjacent/all-pairs correspondence, strict-versus-weak correction,
and its exact assumptions should be documented. Whole-row completion must
wait for the actual frozen scope and accepted witnesses; this note assigns no
coverage credit.

The all-node-triples characterization in Exercise 5.1, all lookup/insert/delete
and split-min algorithms, both direct and list-refinement correctness routes,
set/map ADT realization, balancing, positioned rotations, costs, and every
later chapter obligation remain queued. No source predicate is an algorithm
implementation, and an invariant theorem alone does not implement an ADT.

The eventual statement review should inspect the actual inferred types,
quantifiers, relation hypotheses, full-key versus payload observations, and
successful-rotation premise. Source assertions should be proved through these
public connections with their hypotheses established, while the negative
cases retain the independently justified expectations above. All current
expectations are mathematical/source readings; none has been elaborated in
Lean by this preflight.

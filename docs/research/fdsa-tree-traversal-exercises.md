# Enumeration, levels, reconstruction and rose mirroring

CTB-74 receives the complete eight-module exercise block from donor
`d02419738a9e16963727b25acf2e18f374dd16de` against pinned master
`c214fb0720ffc998951255a7e4b5f2e80a299186`. The donor commit's own diff contains
only reconstruction; its tree also contains the earlier enumeration, levels
and rose developments. All 97 original public named declarations and every
original example are retained. The shared BasicObservations owner was already
received by CTB-72 and is reused without copying it.

The current CTB checkpoint records exact source identities, focused checks,
statement assessment, independent reviews and final comparison. Receiving
whole-library guarded compilation, exhaustive audit and final acceptance remain
separate pending gates. Declaration counts are preservation evidence, not
chapter-completion percentages.

## Source correspondence and current owners

The source is FDSA, *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, July 27, 2026 manuscript, Chapter 4, Section 4.1 exercises.
The retained [Chapter 4 obligation ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md)
provides the pinned PDF and companion-source identities and exact obligations.
This recovery uses that analysis; it does not claim a new reading of the PDF.

| Source obligation | Current connection and boundary |
| --- | --- |
| Exercise 4.2, C04-019 | Executable `enumTree`, exact `mem_enumTree_iff`, and `set_enumTree` enumerate precisely the trees with the prescribed full inorder. |
| C04-020 | `enumTree_nodup` holds for every input list, including repeated labels. |
| Exercise 4.4, C04-023–024 | Independent indexed `level` and the `Trees.fold` collector `levels`; aligned level merging preserves unmatched tails. |
| C04-025–026 | Exact height/length equality, all-index default-empty lookup, and bounded optional-index correctness. |
| Exercise 4.5, C04-027–028 | Total first-occurrence Option parser and explicit empty-tree-fallback wrapper; both round trips retain the distinct-preorder premise. |
| Exercise 4.6, C04-029–030 | Labelled ordered-list-child `Rose`, recursive child mirroring/reversal, and universal nested mirror involution. |
| Cross-module composition | `reconstruct?_of_mem_enumTree` reconstructs an enumerated tree from its preorder and prescribed inorder when its preorder has no duplicates. |

Enumeration and levels use the existing BinaryTree/inorder/fold owner.
Reconstruction uses the already shared preorder, membership-to-set and length
laws, plus the enumeration headline theorem for its new composition. Rose is
a minimal concrete carrier for the source's labelled ordered children.
The inspected LCA owner instead has an unlabelled singleton/attach carrier with
occurrence-indexed nodes; it is not substituted for this raw source datatype.
No unused translation framework is introduced.

## Executable enumeration and duplicate freedom

`enumTree []` returns the singleton list containing the empty tree. For
`x :: xs`, it first enumerates `xs`, then flat-maps `insertFirst x` across those
trees. `insertFirst` visits the left spine: it first adds a new root with empty
left child, then recursively inserts into the old left child and rebuilds that
root. This fixes the execution and output order without deciding label equality
or selecting a list from a Finset.

`inorder_of_mem_insertFirst` proves that each such insertion prepends exactly x.
The converse predecessor theorem supplies an insertion witness for every tree
whose inorder starts with x. Together they prove the full soundness/completeness
equivalence, and hence equality of the enumerated set with the independent
prescribed-inorder set. Merely matching node counts would not suffice.

`removeFirst` removes the first inorder node, replacing it by its right subtree.
Its inverse law on every insertion result separates lists arising from distinct
predecessors. Local insertion lists have no duplicates, and their disjointness
passes through flatMap to `enumTree_nodup`. Equal input labels never identify
the distinct left-child and right-child shapes.

The exact nil, singleton, pair and five-tree triple enumeration orders are
retained. The repeated-label pair has two distinct shapes and is proved Nodup.
The root-9, children-3/7 sample belongs to the enumeration of `[3,9,7]` and is
excluded from `[9,3,7]` through the public membership theorem. Empty labels
require no inhabitant. The pinned Mathlib `treesOfNumNodesEq` enumerates Unit-
labelled shapes by size as a Finset; this executable prescribed-inorder list
is a different source interface. No enumeration cost or general Catalan-count
claim is made by this unit.

## One tree traversal and independent level observations

`level t k` independently computes labels at a requested depth: nil yields [],
depth zero at a node yields its singleton root, and successor depth appends
the two child queries. In particular, a root query need not collect every level.

`levels` instead specializes the existing ordinary fold with empty summary []
and node algebra `[root] :: mergeLevels left right`. It has no depth argument,
height loop or natural arithmetic. Its public nil/node laws retain the source
recurrence as definitional equations. `mergeLevels` appends corresponding lists
and returns either remaining suffix intact when the other side ends.

The merge length is the maximum of child lengths, so the collector length is
tree height. The independent default-empty lookup law holds for every natural
index; the optional-index theorem gives `some (level t k)` when k is below the
height. Their proofs consume public recurrences and explicit lookup equations,
without defining the indexed observation from the collector.

The asymmetric example has `[[9],[3,7],[8,4,5],[6]]`. The final [6] is the deeper
right child's unmatched level. Index two and the beyond-height query consume
the universal correspondence laws. Repeated labels retain both occurrences;
the empty-label nil case is handled uniformly. One structural tree traversal
alone does not imply linear total list work: aligned append operations retain
their actual unmeasured work, and this unit asserts no total-time bound.

## Total reconstruction and its exact domain

`reconstruct?` requires DecidableEq, splits the inorder list at the first
occurrence of the preorder root, and recursively parses the corresponding
take/drop portions. Its termination measure is preorder length. Both recursive
preorder lists are shorter than the original nonempty one even when inputs
are malformed. Empty mismatches, absent roots and failed child parses return
none. `reconstruct` uses the empty tree as an explicit failure fallback; it
needs no default label.

For a genuine tree with Nodup preorder, the root does not occur in the left
child. The independent traversal-to-set bridges establish this in inorder;
canonical length laws then identify the exact split and child preorder lengths.
Induction yields both the Option round trip and the wrapper round trip.

The five-node sample has preorder `[9,3,5,7,6]` and inorder `[3,5,9,6,7]`.
Its proved distinctness supports both public round-trip applications. Singleton,
empty-label, missing-root, both surplus-input and empty-mismatch cases remain.
The lists `[1,2,3]` and `[3,1,2]` have equal label multisets yet fail to parse;
the universal correctness theorem derives that they cannot be traversals of
any common tree.

The two-node repeated-label left and right shapes share preorder and inorder
`[a,a]`. They are distinct, the preorder is not Nodup, and the actual first-
occurrence parser chooses the right-child shape. It does not recover the left
shape. These facts retain the required distinctness boundary. The parser's
recurrence specifies all inputs, but this unit does not claim an additional
universal successful-parse soundness or failure-characterization theorem.

The new `reconstruct?_of_mem_enumTree` composes `mem_enumTree_iff` with
`reconstruct?_traversals`. It proves reconstruction from the prescribed list
for any enumerated tree whose preorder is Nodup. The five-node sample consumes
this new theorem after its enumeration membership is established. A second
connected case proves that the repeated-label left shape is enumerated, lacks
the premise, and is not recovered. Enumeration's unrestricted label domain
therefore remains distinct from reconstruction's round-trip domain.

## Nested rose mirroring

Every Rose node stores its label and a finite ordered list of Rose children.
`mirror` recursively mirrors each child and reverses that list. Attached child
membership supplies the size decrease for nested recursion; the public node
equation exposes ordinary list map and reversal without attachment witnesses.

The involution proof uses well-founded induction with the explicit motive
`mirror (mirror t) = t`. Its induction hypothesis applies to each actual child,
not only to the root's list. Standard map/reverse composition then restores
the original ordered children. The asymmetric example changes order both at
the root and inside a descendant, while the repeated-child example retains
both occurrences. Both consume the universal involution theorem.

These four exercises leave the other Chapter 4 obligations with their owners:
maximal complete subtrees, executable completeness checking, the almost-complete
constructor characterization, balancing with height/cost contracts, and
remaining cache clients. Source correspondence, focused compilation, source
review and final receiving acceptance remain separately accounted for.

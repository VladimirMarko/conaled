# FDSA Chapter 5: minimum mixed rotation distance

This component addresses canonical FDSA-5-91. Its finite distance is the minimum
number of successful left or right rotations at subtree positions, over all
legal sequential traces between the endpoints. The existing right-normalization
and left-recovery construction proves existence and the elementary upper bound.
The selected route is not used as the definition of distance.

The canonical requirement is FDSA-5-91 in the unchanged
[Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
The source is the rotation-distance discussion in
[Functional Data Structures and Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
following the rotation/listification construction on printed pages 67–71.
This note makes no new visual reading claim. The earlier
[rotation correspondence](fdsa-tree-rotations.md) records the accepted primitive
operations, normalizer, exact schedule and right-only optimality results reused
here. The latter optimality concerns a narrower problem than mixed distance.

## Operations and connected domain

`RotationDirection` distinguishes left and right root rotations; the existing
`Search.SharedTree.Branch` describes child positions. A `RotationMove` contains
one rotation direction and a list of those branches. `applyMove?` uses the
existing partial `applyAt?`, including its traversal and callback failures.
`applyMoves?` is an ordinary `List.foldlM` over the evolving tree. An illegal
root or missing path returns `none`. A failed operation is not an identity edit.

`Mixed.lean` establishes empty, cons and unconditional append equations,
preservation of the full inorder sequence and node count, and successful
recovery by `inverseMoves`. Inversion reverses the actual moves and exchanges
left with right, keeping each path. The generic path inverse theorem justifies
using that path in the reached state. `applyMoves?_directedMoves` embeds the
existing fixed-direction `applyAts?` operation exactly.

`connectionMoves` maps the accepted right schedule for the source and reversed
left schedule for the target into this mixed interpreter. Its correctness is
derived from `connect_equal_inorder`, and its length bound is derived from
`connection_length_le`. Together with preservation, `exists_moves_iff` says that
two labelled trees are connected precisely when their complete inorder lists
are equal. Equal node count alone does not suffice for arbitrary labels.
Repeated labels and unordered raw trees require no extra premise.

## The attained minimum

`distance s t same` takes the equal-inorder proof explicitly. Its definition is
`Nat.find` applied to the proposition that a successful trace of length `n`
exists. The existence proof is the actual connection above. Classical
decidability makes this a noncomputable mathematical minimum; no executable
shortest-path algorithm is claimed.

The public observation consists of three facts:

| Result | Meaning |
| --- | --- |
| `distance_spec` | Some legal trace has exactly the distance as its length. |
| `distance_le_length` | The distance is at most the length of every successful trace. |
| `distance_le_iff` | Distance at most `k` is equivalent to an actual legal trace of length at most `k`. |

Zero distance is equivalent to equality of the endpoints, since a length-zero
witness must be empty. Symmetry reverses a shortest witness. The triangle
inequality concatenates shortest witnesses, executing the second on the first
result. The upper bound compares the minimum with `connectionMoves`. These
arguments do not assume the metric laws or a shortest witness as contract data.

All labelled results are polymorphic in `α : Type u`. They assume no order,
decidable equality or distinctness on labels. The helper
`inorder_eq_of_numNodes_eq` uses only subsingleton labels: equal list lengths and
equality of corresponding elements establish equality of inorder lists.

## Common-size shapes and boundary cases

`Shape n` is the transparent subtype `{t : BinaryTree Unit // t.numNodes = n}`.
It reuses the existing carrier and counts nonempty nodes. The Unit instance of
the subsingleton lemma discharges connectedness, so `Shape.distance s t` is
available for every pair of shapes of common size. It exposes attainment,
every-trace minimality, the threshold equivalence, zero iff equality, symmetry
and the triangle inequality through the labelled API.

`Shape.distance_le_two_mul_sub_two` proves `distance s t ≤ 2*n-2` for every
natural `n`. In particular it proves FDSA-5-91's positive-size bound. Natural
subtraction also gives the separate empty case; `distance_empty` and
`distance_singleton` prove zero for every pair at sizes zero and one. This fixed
size interface is available to a later maximum-distance theorem without
asserting that theorem here.

## Separating clients and remaining boundaries

`Examples/RotationDistance.lean` connects the public operations and minimum
laws to the cases selected before implementation:

| Case | Distinguishing result |
| --- | --- |
| D01 | Empty traces succeed; both directions fail at empty/singleton roots; missing paths fail. |
| D02 | The left and right two-node shapes are distinct and have distance exactly one, using a legal witness and the zero-distance law. |
| D03 | A right/left inverse cycle has length two but its endpoints have distance zero. |
| D04 | On the left chain of size three, a right rotation at the left child is legal initially but fails after the root-right move; two root-right moves succeed. |
| D05 | Empty/singleton distances and two-/three-node applications of the general bound. |
| D06 | Singleton labels zero and one have equal size but admit no connecting trace. |
| D07 | Two-node trees with repeated label seven have inorder `[7,7]` and distance one. |
| D08 | Two root-right moves followed by a left rotation at the right child succeed; the reversed opposite trace recovers the start. Append, failure propagation, symmetry and a triangle bound use the public laws. |
| D09 | A trace of length at most zero exists exactly for equal shapes; the one-step threshold holds for the two-node pair. |

The charged unit is a successful rotation. A move can traverse multiple child
edges; this development gives no bound on traversal, allocation, bit operations
or compiled runtime. The threshold equivalence is an uncosted existence result.
It does not prove FDSA-5-93's encoded polynomial verification claim. FDSA-5-92's
sharp `2*n-6` diameter for `n ≥ 11` also remains mandatory and unproved here.
These boundaries do not replace the remaining canonical book obligations or
the separate receiving integration reviews and acceptance checks.

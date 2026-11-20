# Balanced interval trees from complete annotations

## Source and scope

This construction addresses **C05-085**, the unnumbered balanced-augmentation
exercise in section 5.6.6, printed page 76 of *Functional Data Structures and
Algorithms: A Proof Assistant Approach*, edition 27 July 2026. The canonical
[Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md)
permits a concrete selected balance scheme. Here that scheme is the existing
height-balanced implementation with tolerance one. The book's red-black example
does not require replacing that implementation with a second balancing algorithm.

The official [PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
was authenticated as SHA256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The relevant section supplies the open-ended exercise, rather than a particular
annotated rotation program to reproduce literally. This is a local Lean
construction using conaled's received mathematics. No Isabelle execution or
whole-book reading is claimed. Current qualification and actual validation are
recorded in [CTB-24](../textbooks/CTB.json) and the [coverage ledger](../textbooks/coverage.json).

The maintained implementation owners are:

| Owner | Role |
|---|---|
| `Applications/Trees/HeightBalance/{Basic,Rebalance,Updates,OrderedUpdates,SetRefinement}.lean` | Existing complete-annotation balancing, local updates, validity and ordinary set laws. |
| `Applications/Search/IntervalTree/Balanced.lean` | Concrete height/maximum algebra, proof projection, direct query and full interval-set contract. |
| `Applications/Search/RectangleSweep/Balanced.lean` | Concrete occurrence-sensitive rectangle consumer. |
| `Examples/BalancedIntervalTrees.lean` | Independently selected rotations, updates, weak-premise queries, separating inputs and consumer cases. |

The earlier preparation has been processed into these owners and this paper.
Its cost questions remain in the existing measured-operation and sweep owners
identified below. Completed correspondence does not imply completion of those
different obligations.

The received mathematical preparation was written on 18 November 2026 by
`/root/balanced_interval_preparation` and the subsequent root annotation work.
The earlier red-black comparison came from the receiving integration agent's
paper, SHA256 `c3b03a4ecda6c8f55cccd76707c5f4626ee0bf2d5c071661e209120c68f8e417`.
Its external-provider observations remain attributed observations at that time.
Chapter 9 source inspection retains the reading limits in
[the continuation paper](fdsa-avl-continuation.md).

## Representation and the complete invariant

Keys have type `κ`, endpoints have type `α`, and the two universe levels are
independent. A key is interpreted by `iv : κ → IntervalKey α`; the tree carrier
is `BinaryTree (κ × (Nat × α))`. Each node stores its key, height and greatest
high endpoint. Keys may carry occurrence IDs or other information, and different
keys may denote the same interval.

`Balanced.annotation iv` instantiates `HeightBalance.HeightAnnotation` with

\[
e=(0,\bot),\qquad
c((h_l,m_l),k,(h_r,m_r))=
\bigl(1+\max(h_l,h_r),\;
\max((iv\,k).high,\max(m_l,m_r))\bigr).
\]

Its height observation is the first projection. The two height-algebra laws
follow by definition, so every existing generic complete-annotation theorem
applies to this actual algebra. Algebra construction and ordinary update/set
laws do not need endpoint linearity: their explicit assumptions are `LE`,
`Max` and `Bot` for endpoints, with the key order required by the selected
operations. Semantic greatest-endpoint and overlap correctness use
`LinearOrder α` and `OrderBot α`.

`Balanced.Valid iv t` is the existing `HeightBalance.SetValid` at tolerance one.
It separately requires recursive balance of the **actual shape**, correctness
of **both coordinates at every node**, and strict ordering of the erased key
inorder. Stored heights are not assumed to equal actual heights merely because
they are natural numbers. That equality follows from complete cache validity
through `HeightBalance.ht_eq_height_of_cacheValid`.

The smart constructor recomputes a new root from its children's stored complete
annotations and retains those children. It does not traverse a subtree to repair
an arbitrary malformed descendant. Its exact child-validity equivalence is the
existing `HeightBalance.node_cacheValid_iff`.

## Local balancing and updates

The concrete set operations are exactly
`HeightBalance.deleteOps (Balanced.annotation iv) 1`. This selects the existing
`balL`, `balR`, insertion, `splitMaxOption` and predecessor deletion programs.
Every reconstructed node uses the complete smart constructor. Both nodes of a
single rotation, and all reconstructed nodes of a double rotation, therefore
receive the appropriate new height and maximum.

The inherited cache and `ValidD` theorems prove recursive annotation and balance
preservation. The inherited inorder theorems and strict-order closure prove the
ordinary key semantics independently of those auxiliary facts. Together they
give the seven fields of `Balanced.setLaws`: empty validity and observation,
insertion validity and observation, membership, deletion validity and observation.
The interface does not assume the set laws it is meant to establish.

The literal branch conventions remain those of the selected implementation:
equal-key insertion returns the original node, a tie in heavy-child heights
selects a single rotation, and deletion repairs the side opposite the shrinking
child. `splitMaxOption` returns the remaining tree first and extracted key second.
No update is replaced by a whole-tree rebuilding operation.

The older maximum-only interval tree uses successor deletion; this selected
height-balanced implementation uses a predecessor. Shared set/inorder semantics
are the correct comparison. Equality of their literal output trees, rotation
histories or operation costs is neither needed nor asserted. Similarly, these
product-labelled trees are not identified definitionally with a height-only AVL
datatype. The actual complete-annotation interface supplies the connection.

Unchanged height is insufficient evidence that a maximum is unchanged. For
example, deleting the greatest endpoint in a tree can leave its height fixed.
The concrete updates recompute the whole annotation on reconstructed nodes;
they do not discard the second coordinate after observing no height change.

## Maximum meaning and query correctness

`Balanced.maximumTree` maps a binding `(key,(height,maximum))` to `(key,maximum)`.
It preserves the raw shape, complete keys and stored maxima, including malformed
ones. `erase_maximumTree`, `maxHi_maximumTree`, `maximumTree_eq_nil_iff` and
`maximumTree_node_smart` connect erasure, root reading, nonemptiness and the local
constructor. This is a proof bridge to the already established interval tree.

`cacheValid_maximumTree` proves that complete product-cache validity implies the
existing recursive maximum invariant. Its induction uses only the second
coordinate of each local cache equation. `maxHi_spec` then transports the
existing attained-greatest-endpoint result: for a nonempty maximum-valid tree,
some original key attains the root maximum and every key's high endpoint is
bounded by it. The empty tree's bottom reader alone supplies no witness.

The executable `Balanced.search` operates directly on the product tree:

1. An empty tree returns false.
2. A root interval overlapping the query returns true.
3. Otherwise, an empty left child sends the query right.
4. For a nonempty left child, compare the query low with the stored left maximum
   and recurse into exactly the selected child.

The definition never calls `maximumTree`. `search_eq` proves equality to the
existing interval search on the proof projection **for every raw tree**. Thus
the comparison includes malformed heights/maxima and unordered inputs, rather
than silently changing raw behavior under an invariant assumption.

The public statements retain different useful hypothesis levels:

| Result | Required tree facts |
|---|---|
| `search_sound` | None: a true result yields an original stored key overlapping the query. |
| `maxHi_spec` | Recursive maximum validity and nonemptiness; no height or order requirement. |
| `search_correct` | Recursive maximum validity and pairwise nondecreasing projected lows; no correct heights, balance, strict key order or uniqueness requirement. |
| `search_correct_of_strict` | Maximum validity, strict key inorder, and the implication that key order preserves weak low order. |
| `intervalSetLaws` | The complete balanced set invariant, with that global low-order implication for all keys. |

Weak low order is enough for overlap search. An implementation may therefore
search a maximum-correct tree even when stored heights are wrong, its shape is
unbalanced, or a complete key occurs twice. Such a tree need not be a valid
state for the ordinary set-update laws. Conversely, complete balanced set validity
alone does not imply interval correctness if key order reverses the projected
low endpoints. These statements keep that additional requirement visible.

The full contract is `IntervalSet.Laws (deleteOps iv) (search iv) iv observe (Valid iv)`,
where `observe` is the structural key set after erasure. The overlap field comes
from the direct-query correctness theorem and `hasOverlap_image_iff`. That
image law does not require `iv` to be injective. Existing mixed-history clients
therefore apply to insertion and deletion of distinct keys with equal interval
images.

## Concrete rectangle sweep

`RectangleSweep.balancedSweep` specializes the existing once-sorted event
algorithm to this interval-set instance. Complete keys are
`IntervalKey α ×ₗ Nat`; the natural coordinate identifies an input occurrence.
`keyInterval_low_le_of_lt` supplies the required order compatibility. The theorem
`balancedSweep_eq_true_iff_hasIntersection` uses the existing sweep correctness
result to characterize a common point of **two distinct input occurrences**.

X endpoints require a linear order with bottom for this cache representation.
Y endpoints need only a linear order. In particular, Nat x coordinates and Int
y coordinates are a valid client; this does not provide a bottom-free Int x
implementation. Existing list consumers retain their independent broader scope.

The selected algorithm queries before insertion, sorts every insertion before
every deletion at an equal y coordinate, deletes the exact occurrence key and
stops on the first successful query. Duplicate rectangle values remain distinct
occurrences. The abstract full-prefix update fold is useful to explain deletion,
but states after an earlier successful query are not claimed to be reached by
the short-circuiting scan.

## Independent cases and statement boundaries

The cases originate in the received augmentation preparation, existing generic
height-update examples and independently fixed interval/sweep observations.
Their mathematical expectations were fixed before their connections to the new
public declarations. The companion module checks those connections as well as
literal expected results.

The decisive rotation example inserts `[1,1]`, `[2,2]`, `[3,100]`. The single
rotation produces the middle key at the root, with maxima 1 and 100 in its leaf
children. Leaving 100 at the demoted `[1,1]` leaf makes a query for `[3,3]` go left
and miss the right-hand witness. The bad maximum is still an upper bound; it is
not attained. Correct root maximum, correct heights, balance and sorted keys
therefore do not replace recursive exact-maximum validity.

The double-rotation case uses `[1,100]`, `[2,2]`, `[3,3]`: the promoted middle
root gains maximum 100 and the demoted right leaf has maximum 3. Mirror cases
and deletion ties exercise the other branch choices. In `ll_rotation`, the
promoted `[2,3]` above `[0,1]` and `[4,100]` changes its old maximum 3 to 100.
Deleting 5 from the
fixed five-key tie example retains height 3 while the root maximum falls from
5 to 4. Cases use actual update/validity laws, rather than treating constructor
calculations as proofs of invariant preservation.

Other connected boundaries include distinct higher-universe keys denoting the
same `[2,8]`, deletion retaining another occurrence's boundary hit, a malformed
equal-key insertion that is not repaired, and the difference between an empty
tree and a valid `[0,0]` singleton even though both maximum readers are zero.
The raw empty-left guard is checked separately from ordered-set validity.
Bad-height/good-maximum, unbalanced and repeated-key inputs exercise the weaker
query theorem. Reversed low projection and underestimated or unattained maxima
explain the remaining hypotheses. Rectangle cases cover empty/singleton inputs,
duplicate occurrences, closed-edge contact and separation in either coordinate.

## Alternatives retained from the preparation

An optional maximum provides a different representation when endpoints have no
bottom. Use `none` as the empty summary and join actual highs with `max`; for
nonempty trees the summary must be `some` of an attained greatest endpoint.
Its identity/associativity/commutativity/idempotence laws support a maximum fold,
but that algebra alone does not prove a balanced update or query implementation.
One must define its actual branch conditions and prove its complete-cache and
search bridges. It is not interchangeable with this bottom-valued reader, and
the existing optional-cache projection has different types and purposes.

The earlier red-black route remains an optional alternative. Erasing auxiliary
fields may preserve the underlying red-black shape, but carrying endpoint maxima
requires every reconstructed rotation node to recompute them. A set or map
observer that forgets node annotations cannot establish this requirement.
Off-the-shelf rotations specialized to a different label/cache datatype need an
actual annotation-aware implementation and correspondence proof; a map equality
or unchanged black height is insufficient. The attained-maximum counterexample
above applies independently of the chosen balance scheme. No new red-black
implementation or its measured complexity is claimed here.

### Optional red-black reconstruction calculations

The inspected source-facing red-black ordering predicate is
`BST (decode : κ → Int)`. A global strictly increasing embedding of all
`IntervalKey Nat` into Int is impossible: every key in
`[0,0] < [0,1] < [0,2] < …` lies below `[1,1]`, whereas an increasing integer
sequence gains at least one at every step and cannot remain below one fixed
integer. A finite-input rank adapter would need its own correspondence proof.
The shape/color facts alone do not supply a generic interval-key order.

Raw branch priority also matters. The local matcher tests right-left before
right-right; the overlapping red-red example in
[`Examples/RedBlackTrees.lean`](../../Examples/RedBlackTrees.lean) records the
distinction. The earlier paper reports the directional provider's right balancer
testing right-right before right-left. That provider comparison has not been
newly inspected here. Agreement on valid-tree outcomes does not imply equality
on overlapping raw patterns.

For the cache calculations, let ascending keys be `a=[1,100]`, `b=[2,50]`,
`c=[3,4]`, with empty fringes. Each following input has valid maximum caches
and the indicated temporary red-red defect. The corresponding cache-aware
rewrite should produce **red b/100 with black leaves a/100 and c/4**.

| Branch | Temporary input, with stored maxima | Required recalculation |
|---|---|---|
| LL | Black c/100, left red b/100, its left red a/100 | Demoted c becomes 4. |
| LR | Black c/100, left red a/100, its right red b/50 | Promoted b becomes 100; demoted c becomes 4. |
| RL | Black a/100, right red c/50, its left red b/50 | Promoted b becomes 100; demoted c becomes 4. |
| RR | Black a/100, right red b/50, its right red c/4 | Promoted b becomes 100. |

Black-height-zero fringes realize the temporary local premises; these inputs
are not asserted to satisfy the full public red-black invariant. Root blackening
cannot repair maxima. Repairing only the final root leaves a malformed c child
in the first three cases. Even the no-rotation fallback must recompute: root
`[1,1]` with a new right leaf `[2,100]` must acquire maximum 100. An arbitrary
shape-dependent summary fold is not rotation invariant merely because a smart
constructor recomputes it; maximum meaning uses the lawful maximum algebra.

A colored deletion implementation would also need the following observations:

- Black root `b=[2,3]` with black leaves `a=[1,100]` and `c=[4,5]` has equal
  black heights and valid maxima. Deleting a leaves inorder `[b,c]`, balance
  and maximum 5. Black b with red-right c and black c with red-left b are both
  possible balanced outputs; only a chosen actual deletion program determines
  its exact result.
- Root `[-5,-4]` with leaves `[-8,-6]` and `[-3,-1]`, followed by deletion of
  the right interval, the original root and the last interval, has readers
  `-1,-4,-6,⊥`. Here bottom denotes an adjoined empty summary: for optional Int
  maxima the sequence is `some (-1), some (-4), some (-6), none`. Int itself
  has no least element, and zero is not an empty sentinel. Empty has no attaining
  interval.
- Complete keys `([2,8],0)`, `([2,8],1)`, `([2,8],2)` retain the last key,
  maximum 8 and a point-8 hit after deletion of two keys. Deleting the last
  gives empty and false. The projection to intervals remains noninjective.

These are retained paper calculations for an optional representation, not
newly checked colored-program results. A colored direct query would need a
proof relation to color erasure without executing that whole-tree erasure.
An affine/logarithmic conversion lemma cannot supply the missing measured
deletion program or its operation-height bill.

## Remaining measured work

C05-090 remains open. Its complete preparation is maintained in
[the rectangle-sweep paper](fdsa-rectangle-sweep.md#unqualified-preparation-for-the-measured-sweep).
Chapter 9's operation-cost obligations remain in
[the height-update paper](fdsa-height-updates.md#unqualified-preparation-for-measured-operation-costs).
This completed functional instance supplies concrete programs for that work,
not their measured recurrences or bounds.

Those owners retain the actual event-generation and once-sorted merge-sort
costs, key/endpoint comparison tariffs, cached-height arithmetic, smart-node and
rotation work, predecessor-path deletion, query branch costs, active-size bound,
early termination and the final all-input/logarithmic conversions. In particular,
strict key order is needed to identify node count with observed-set cardinality;
it is false for arbitrary raw trees. A height bound alone does not prove a
measured logarithmic operation bound. Positive empty-state cost also precludes
a literal all-size bound with a zero right side at size zero.

No operation-cost, bit-complexity, allocation, physical-sharing or machine-time
result follows from these functional laws. The unbalanced no-hit quadratic
query family and the whole-tree-rebuilding update separator remain in the sweep
preparation. The existing `Resources.TreeBalance.balRun` has `2*n+1` recursive
calls on its sufficient size-n input before charging inorder traversal; it
cannot stand in for a logarithmic local update. Pure-tree construction, measured
construction, shared-store references and physical-sharing observations remain
distinct. C05-092's exact eventual rotation-diameter bound, C05-093's encoded
polynomial certificate checker, and all other canonical textbook obligations
also remain open.

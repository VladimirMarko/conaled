# Shared root rotations and cached rebuilding

This cross-cutting source draft develops ordinary root rotations on the existing
`BinaryTree`, then composes the existing cached and measured node constructors.
It supports later balancing developments without adding a tree carrier, algebra
record or execution framework. It is uncompiled and unaccepted; its source
statements, clients and provenance remain subject to the complete candidate
validation and independent review workflow.

## Source correspondence

The source is the July 27, 2026 edition of
[Functional Data Structures and Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Chapter 5 introduces inorder-preserving root rotations on printed p.67 and
gives their partial pattern equations on p.70. The corresponding definitions
are `rotL` and `rotR` in pinned
[Tree_Rotations.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Rotations.thy),
SHA-256 `745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea`.
The companion revision is recorded separately from the manuscript edition.

Chapter 9, pp.105 and 108–110, uses height-cache smart constructors for the
same local rearrangements. The single branches of
[AVL_Set_Code.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/AVL_Set_Code.thy)
perform two smart constructions. Chapter 21, pp.245–246, combines ordinary
rotations into splay rearrangements, distinguishing root-only composition
from a rotation inside a child followed by a root rotation. The shared root
facts are useful to those algorithms; their complete branch conditions,
positioned executions, balance proofs and cost analyses remain separate work.

The source constructor order is left child, label, right child. Lean's existing
constructor is `BinaryTree.node label left right`. The primitive left operation
has the matching equation

```lean
Trees.rotateLeft? (.node x A (.node y B C)) =
  some (.node y (.node x A B) C)
```

and the right operation reverses that rearrangement. Missing pivots return
`none`, making the underdefined source domain explicit. No default payload,
payload equality decision, order or finiteness assumption is needed. The
operation includes `BinaryTree Empty`, whose only value is the empty tree.

The existing project fold and cache interfaces are described in
[fdsa-tree-cache.md](fdsa-tree-cache.md). Mathlib's `Ordnode.rotateL` and
`rotateR` use a separate size-cached carrier and weight-balancing decisions;
they are not these ordinary single root transformations.

## Observation contracts

| Operation | Preserved observation | Additional qualification |
| --- | --- | --- |
| Successful ordinary root rotation | The complete ordered inorder list, including repeated labels; node and external-leaf counts | The inverse is conditional on success. Height can change. |
| Rotation after an arbitrary label map | The mapped successful result and the same failure domain | Injectivity is unnecessary, and label universes may differ. |
| Two smart-node reconstructions | Inorder of erased payload labels | Annotations are updated, so their full pair-valued inorder need not be preserved. |
| Rebuilt cached fold | Recursive cache correctness for the new shape | Exactly the three retained fringe caches must be valid. |
| Equality of old and new root summaries | A rotation-invariant fold observation | Requires the local algebra equation; a stored old root also needs its appropriate correctness premise. |
| Two measured node constructions | Actual returned tree and the separately accumulated callback/local work | Equal payload observations do not imply equal work. |

The ordinary inorder law uses list associativity, retaining both order and
multiplicity. Size and leaf-count laws reuse `Trees.inorder_length` and the
existing node/leaf identity. Map compatibility is a derived parametric law of
the source equations, not an additional theorem explicitly printed in the book.

For a generic fold, let a, b and c be the three actual fringe summaries. The
needed local equation is

```text
combine a x (combine b y c) = combine (combine a x b) y c.
```

It needs no equation for the empty summary. A uniform algebra law is a useful
sufficient condition for repeated uses; the local result can retain only the
reached equation. Inorder-derived monoid summaries satisfy the equation by
associativity. The existing `TreeCacheExamples.ordered_summary_fold` connects
`l * measure x * r` with `Sequences.OrderedSummary.summary` in that order,
without commutativity. A word instance exposes order instead of reducing it
to a commutative size calculation.

Height is a counterexample to unqualified fold preservation. The existing
`balancedThree` and `leftThree` are one legal left rotation apart, with the
same three labels and heights two and three. A cache of height must be
recomputed correctly; its previous value is not an invariant of rotation.

## Local cache reconstruction

The supplied fringes already expose a legal rotation shape. The left result
uses precisely

```text
lower  = smartNode z combine A x B
result = smartNode z combine lower y C.
```

The right result first constructs `smartNode z combine B y C`, then uses it
as the right child of `smartNode z combine A x lower`. These are small
ordinary clients of `Trees.Cached.smartNode`. They retain the three fringe
trees and recompute the two changed annotations. They do not erase and
reannotate a whole tree as an execution step.

Two applications of `erase_smartNode` connect each result to the ordinary
rotation. Two applications of `smartNode_valid_iff` establish validity
exactly when all three fringes are valid. This result needs no associativity
and does not rely on the two discarded top annotations. `read_eq_fold` then
identifies the repaired root with the independent fold of the new shape.

Raw rotation of product labels has a different contract: it preserves every
payload/annotation pair, including annotations that become incorrect at
their new positions. For the size-annotated balanced-three-node fixture,
raw rotation places annotations one and three at roots whose sizes are
three and two. Smart rebuilding replaces them with the correct values.
Its pair-valued inorder changes, while erased payload inorder remains
`[1,1,1]`. The existing malformed `corrupt` fringe also remains invalid after
two new roots are built above it; local reconstruction cannot repair a
retained invalid descendant.

## Actual local resource interpretation

The resource program uses existing `Resources.bind` and
`Resources.TreeCache.nodeRun`. Each `nodeRun` performs two root reads, invokes
the supplied measured callback on their values, stores its actual result,
and adds one constructor-entry tick. Its observation is callback work plus
three under the separately named XT01 local-access tariff.

For left rebuilding, set p=`read z A`, q=`read z B`, r=`read z C`,
u=`callback p x q`, and v=`callback u.1 y r`. The composition's work is
`u.2 + v.2 + 6`. For right rebuilding, u=`callback q y r` and
v=`callback p x u.1`. The second callback receives the first callback's
actual returned annotation. Substitution of a pure specification belongs
after the reached-value contract has been established.

The cost identity itself assumes neither cache validity nor callback-value
correctness. The value theorem uses correctness at the two reached calls;
the validity theorem additionally uses the fringe invariants. Independent
reached cost bounds K1 and K2 give `K1+K2+6`. No global callback bound is
required to state that result.

There is no additional outer rotation-entry charge in this composition.
Fringe preparation, failed shape attempts and whole-tree observations in
proof statements are outside this local observation. The count is distinct
from Chapter 5's unit-per-rotation metric, source conventions with zero-cost
nonrecursive helpers, physical allocation and machine arithmetic. A later
algorithm must prove its own bridge to whichever observation it uses.

### Independent expected calculations

The existing zero-cost `sizeRun` and `heightRun` callbacks give work six.
Correct height reads may change; correct size reads retain the node count.

The existing `appendStepRun` executes the real recursive
`ListReversal.appendRun leftSummary (label :: rightSummary)`. For actual
fringe list-cache lengths p, q and r:

| Rebuilding | Calculation | Exact expected work |
| --- | --- | --- |
| Left | Lower work p+4; its actual returned list has length p+q+1; upper work p+q+5 | `2*p+q+9` |
| Right | Lower work q+4; the final constructor still appends A's list, costing p+4 | `p+q+8` |

The intermediate length comes from the actual append value theorem. Validity
is required to identify stored lists with subtree inorders, but the count
equations use the actual stored lists. For singleton fringes the expected
counts are twelve and ten with matching erased ordered values. The right
fringe still contributes to the returned value even though its length is
absent from this left-append tariff.

The existing valid `chainCache n`, with empty middle and right fringes,
gives expected counts `2*n+9` and `n+8`, including the empty-fringe values
nine and eight. This family exceeds every fixed bound as n varies. Two
reconstructed nodes alone therefore do not justify constant work for an
arbitrary cached summary callback.

## Source obligations and statement assessment

The root laws support C05-042/043. Their smart-constructor uses support the
local rearrangements needed in C09-018–026/038, and the ordinary laws support
the component rotations behind C21-005–008. Positioned schedules, their
legal execution and exact counts, listification, rotation distance, full
BST/interval algorithms, AVL/red-black tag and balance logic, double-rotation
selection, and splay correctness/amortized analysis remain in their original
chapter inventories. No whole chapter is accepted by this shared draft.

The claim groups retain the following statement boundaries:

- Payload and summary universes are independent. Structural and cache laws
  do not acquire an order, equality decision, inhabited payload or monoid
  solely from their implementation.
- Failure and successful inverse domains are explicit. Positive-size Empty
  witnesses are neither assumed nor manufactured.
- Inorder preserves exact occurrences. Raw pair-valued labels and erased
  payload observations have distinct contracts when annotations change.
- Generic fold preservation uses the local algebra equation, with a valid
  noncommutative monoid instance and the height counterexample.
- Recursive validity is established from all retained fringes; a correct
  root alone cannot replace it.
- Resource results refer to actual reached callbacks. Value correctness,
  cache validity and cost bounds are separate obligations.
- Constant scalar work and growing append work both use actual existing
  callbacks. No physical runtime or storage-sharing theorem is asserted.

The compact clients retain the generic repeated-label word `[q,r,q,s,p]`,
noninjective label mapping, Empty and missing-pivot boundaries, the existing
height and malformed-cache fixtures, scalar work and actual append families.
Their implementation-side public connections and final source identities
are recorded with the immutable candidate in the local review evidence.
All new modules enter the ordinary public import closure and exhaustive audit.

## Validation status

This source draft is developed from the saved unaccepted XT01 candidate.
Accepted repaired Chapter 1 and accepted XT01, with every correction retained,
remain prerequisites to integration or acceptance. The unit does not add a
dependency to the initial Chapter 2 foundation prefix. Its new source requires
focused compilation, a complete clean candidate's guarded project build and
exhaustive audit, both independent review axes, and immediate candidate-record
verification. Mathematical calculations and source preflights are not results
of those checks.

# FDSA Chapter 5: rotations, listification and exact traces

This component implements canonical obligations C05-042–065. Its raw operations
act on the existing `BinaryTree α` for arbitrary `α : Type u`. A successful
rotation preserves the full inorder sequence, including repetitions. Ordering
is an additional client invariant, and height can change.

The source is the rotation section on printed pages 67–71 of
[Functional Data Structures and Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
and the pinned Isabelle
[Tree_Rotations.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Tree_Rotations.thy).
The companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`; its
4870-byte source has SHA256
`745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea`.
The retained BSD notice applies to the companion. The book reading is of the
relevant extracted text; this component makes no fresh PDF-byte or pixel-reading
claim. The canonical chapter ledger remains
[chapter05-obligations.md](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).

## Owners and existing clients

| Owner | Responsibility and reused interface |
| --- | --- |
| `Applications/Trees/Direction.lean` | Owns the exact existing `Search.SharedTree.Branch` declaration. Its namespace, constructors, eliminators and derived instances retain their names. |
| `Applications/Search/SharedTree/Path.lean` | Imports that pure direction owner. Its existing heap and search-path definitions and proofs are unchanged. |
| `Applications/Trees/Rotations/Basic.lean` | Partial root rotations, list form, right-spine length, semantic invariants and the decreasing measure. Uses the existing tree, inorder, node count and independent set observation. |
| `Applications/Trees/Rotations/Position.lean` | Generic partial subtree edits and actual sequential schedules using standard `List.foldlM`. Generic observation and inverse laws are shared by both rotation directions. |
| `Applications/Trees/Rotations/Existence.lean` | The independent existential induction for Exercise 5.6. Imports only the position layer, without the normalization algorithms. |
| `Applications/Trees/Rotations/Normalize.lean` | Three separate well-founded source recursions, their public equations and their correctness/count correspondence. |
| `Applications/Trees/Rotations/Bounds.lean` | Arbitrary-trace lower bounds, list-form uniqueness, exact recovery, equal-inorder connection, existing enumeration clients and existing chain families. |
| `Applications/Search/OrderedTree/Rotations.lean` | Transports the existing `Ordered`/`OrderedBy` inorder characterizations, with a preorder on labels/keys respectively. |
| `Examples/TreeRotations.lean`, `Examples/OrderedTreeRotations.lean` | Checked cases, public-theorem applications, state-dependent failures, old direction clients and actual Type 1/function-payload consumers. Both are public imports. |

There is one direction type, one tree carrier and one standard list interpreter.
Pure rotations do not import a heap implementation to obtain two direction
constructors. `enumTree`, `leftChain` and `rightChain` remain the accepted earlier
definitions. No new raw enumeration or constant-label chain presentation is
introduced.

## Partial operations and observation contracts

Writing `node label left right`, a right rotation has exactly the domain
`node b (node a A B) C` and returns `some (node a A (node b B C))`. A left
rotation reverses that equation on its matching domain. Unmatched shapes
return `none`. The success iff theorems expose these domains explicitly.
They do not assign an identity step to an illegal shape.

`applyAt? f [] t` calls `f t`, even when `t` is empty. A nonempty path at an
empty tree fails. At a node, the designated child is edited and the other child
and root label are retained. `applyAts?` folds over the evolving tree, so the
legality of a later position is determined after the preceding edits.

The append and right-prefix laws are unconditional `Option.bind`/`Option.map`
equalities for every partial callback. They include callback failure and
traversal failure. The pruning cases exercise both. The generic inorder law
has an explicit premise that the callback preserves inorder on successful
execution; the replacement callback supplies a concrete reason this premise
cannot be dropped. The generic inverse law likewise assumes an actual
opposite-step law and concludes successful recovery at the reversed positions.

`IsList` is true on empty and is `left = nil ∧ IsList right` at a node.
Its decision procedure inspects shape without comparing labels. The all-position
characterization quantifies every path; a blocked root alone does not imply
list form. `rightLength` is zero on empty and one plus the right-child length
at a node. It is bounded by node count and equals node count on list-form trees.

## Three independent recursions and the measure

Let `n = t.numNodes`, `r = rightLength t`, and `μ(t) = 2*n-r` in natural
arithmetic. `measure_rotate` proves strict decrease after the root right
rotation. `measure_descend` proves strict decrease from `node a nil r` to `r`.
Both use the proved spine bound. `deficit_descend` instead gives exact equality
for the smaller proposed expression `numNodes-rightLength` on that descent.

| Input shape | `listOf` | `rightPositions` | `countRots` |
| --- | --- | --- | --- |
| Empty | Empty | Empty schedule | Zero |
| `node a nil r` | Retain `a` and recurse on `r` | Prefix right to each recursive position | Recurse on `r`, with no added charge |
| `node b (node a A B) C` | Recurse on the actually rotated tree | Prepend the root position and recurse on that same rotated tree | Add one to the recursive charge of that rotated tree |

Each function has its own well-founded definition and the same proved
decreasing measure. Their public empty, descent and rotation equations are
proved from those definitions. `listOf` is not defined by flattening and
rebuilding; neither schedule nor counter is defined by the arithmetic formula.

Functional induction proves that `listOf` has list form and preserves inorder,
and that executing `rightPositions t` actually returns `some (listOf t)`.
The latter establishes legality at every reached state. Separate inductions
prove schedule length and recursive charge equal `n-r`; their equality follows.
For every tree this is at most `n-1` with natural subtraction, including empty.
Every tree whose right spine has length one attains `n-1`.

The accepted chain families are instantiated at every label and every size.
For `leftChain a n`, the generated schedule is exactly
`List.replicate (n-1) []`, the charge is `n-1`, and the output is `rightChain a n`.
For `rightChain a n`, the schedule is empty, the charge is zero and the output
is unchanged. The measure is zero for the empty left chain and `2*n-1` for a
nonempty one; on the right chain it is `n`. These are universal theorems,
with the size 0–5 table serving only as additional executable evidence.

## Independent existence, inverse traces and optimality

`exists_right_list` proves Exercise 5.6 using strong induction on the measure.
The empty case chooses empty witnesses. The descent case lifts the induction
witnesses beneath a right edge. The rotation case prepends the legal root step
to the induction witness for the rotated tree. Its owner imports only
`Position`; its proof does not invoke a schedule-generating function or an
algorithm-correctness theorem. The later clients at empty, the left chain and
the seven-node tree instantiate that theorem directly.

`eq_of_isList_of_inorder_eq` establishes list-form uniqueness without a label
equality instance or a distinctness assumption. It does not assert that
inorder determines arbitrary raw tree shape. `applyAts?_undo` retains exactly
the missing trace information: a successful forward execution is undone by
opposite steps in reverse order. `reverse_rightPositions` specializes this to
the emitted schedule and recovers the original tree, including its shape.

For trees with equal inorder, `connect_equal_inorder` performs the first
tree's actual right-rotation schedule, followed by the reversed left-rotation
schedule for the second tree. The complete partial execution returns the
second tree. `connection_length_le` proves an empty-safe upper bound of
`2*n-2` on the sum of the two actual schedule lengths. Existing `enumTree`
membership supplies the equal-inorder premise through its original theorem.

For an arbitrary successful right rotation at a position, the global spine
increases by zero or one. The left-branch case may leave it unchanged; the
right-branch case lifts the induction bound. Inorder preservation gives size
preservation. Induction over any successful right-only schedule bounds the
spine increase by its length. A list-form endpoint has spine equal to size,
so `deficit_le_length` proves every such schedule has at least `n-r` entries.
The generated schedule attains this lower bound.

The companion's lines 113–115 present the opposite universal inequality as
an aborted conjecture with a counterexample command. It is not transported
as a theorem. The checked three-node example has a legal three-step route
to list form, while the generated route has two steps.

## Canonical correspondence

Names without a namespace below belong to `Trees.Rotations`. A row may use
several primitive theorems together; the statements and their actual proof
dependencies remain the unit of assessment.

| Row | Actual formal content | Cases |
| --- | --- | --- |
| C05-042 | `rotateRight?`, `rotateLeft?`, both `_node` equations and both `_eq_some_iff` domains | G01–G03, G09, G17 |
| C05-043 | Both `_inorder`, `_numNodes`, `_setTree`, `_undo`; existing-inorder transport in `Search.OrderedTree` | G02–G03, G09–G10, G17 |
| C05-044 | `IsList`, `instDecidableIsList`, `isList_iff_no_right_rotation` and both implications | G01, G06, G12 |
| C05-045 | `rightLength`, its equations, `rightLength_le_numNodes`, `rightLength_eq_numNodes` | G01–G05, G12–G13 |
| C05-046 | Actual `listOf` definition and its three public equations | G01–G03, G05, G09, G13 |
| C05-047 | `measure`, `measure_rotate`, `measure_descend`, `deficit_descend` and all three termination proofs | G02–G05, G12–G13 |
| C05-048 | `listOf_isList`, `listOf_inorder`, `listOf_eq_self` | G01–G03, G05, G09, G13 |
| C05-049 | Shared `Branch`, `applyAt?`, standard-fold `applyAts?`, exact constructor/nil/cons equations | G04–G08, G16 |
| C05-050 | Actual `rightPositions` definition and its three public equations | G01–G03, G05, G12–G13 |
| C05-051 | `measure_rotate`, `measure_descend`, `apply_rightPositions` with actual successful sequential execution | G03, G05–G06, G12–G13 |
| C05-052 | Unconditional `applyAts?_append` from `List.foldlM_append` | G04, G08, G11 |
| C05-053 | Unconditional `applyAts?_map_right` for arbitrary partial callbacks | G05, G08, G12 |
| C05-054 | `apply_rightPositions` and `listOf_isList` | G01–G05, G09, G13 |
| C05-055 | `apply_rightPositions`, `listOf_inorder`, generic successful observation laws | G02–G05, G09–G10, G17 |
| C05-056 | `rightPositions_length`, the independently recursive `countRots_eq_length` | G01–G05, G12–G13 |
| C05-057 | `countRots_le_pred`, `rightPositions_length_le_pred`, `countRots_eq_pred` and all-size chain laws | G01, G03, G11, G13 |
| C05-058 | Generic `applyAt?_undo`, `applyAts?_undo` and `reverse_rightPositions` | G02–G05, G09, G17 |
| C05-059 | `eq_of_isList_of_inorder_eq`, `listOf_eq_of_inorder_eq` | G09–G11, G13 |
| C05-060 | `connect_equal_inorder`, `connect_enumTree` and actual ordered/enumeration consumers | G10–G11 |
| C05-061 | `connection_length_le`; explicit empty, singleton and tight constructed-route cases | G01, G11 |
| C05-062 | Actual `countRots`, its three equations, `countRots_eq_deficit`, `countRots_eq_length` | G01–G05, G12–G13 |
| C05-063 | Independent `exists_right_list`, whose import/proof boundary excludes every generator | G14 |
| C05-064 | `longer_legal_trace`, `longer_trace_recovers`, `off_spine_trace_steps`, `longer_than_optimum` | G04, G14 |
| C05-065 | `applyAt?_rightLength_bounds`, `applyAts?_rightLength_le`, `deficit_le_length`, `rightPositions_optimal` | G03–G04, G05, G13 |

## Frozen independent cases and concrete consumers

The original paper cases were frozen before the implementation. Their expected
trees, paths and counts come from constructor calculations. Kernel proofs and
native evaluations check those expectations through the public operations;
finite outputs do not replace the universal proofs or statement assessment.

| Group | Retained expectation and checked connection |
| --- | --- |
| G01 | Empty and singleton root failures, list form, zero charge/empty schedule, unchanged output, spine/measure boundaries and zero-cost connections. |
| G02 | Balanced `[1,2,3]` right-rotates to the right chain; height changes 2 to 3, spine 2 to 3, measure 4 to 3, generated schedule `[[]]` and charge 1; left rotation recovers it. |
| G03 | The three-node left chain performs two root rotations. Inorder and size stay `[1,2,3]` and 3, spines are 1,2,3 and measures 5,4,3. Every right-only listification pays at least two. |
| G04 | `[[left],[],[right]]` is a legal three-step route. Its first step leaves the whole spine at 1; subsequent spines are 2 and 3. The reversed opposite trace recovers the left chain. |
| G05 | The seven-node balanced tree emits `[[],[],[right,right],[right,right,right,right]]`; all four constructor steps and their reverse are checked. Spines 3–7 and measures 11–7 give charge 4. |
| G06 | Initial root and left-child legality does not make `[[],[left]]` legal sequentially. Later generated right-right paths fail in the initial tree but succeed in their reached states. Two successive root steps fail on the balanced three-node tree. |
| G07 | A replacement callback runs at empty root and terminal empty child; traversal beyond empty fails. A nested edit changes inorder `[0,1,2,3]` to `[0,9,2,3]`. |
| G08 | Pruning a right child succeeds, then a deeper edit fails. Child execution, lifted execution and split append execution agree on the same failure. |
| G09 | Duplicate `[7,7]` rotates, listifies and recovers. An unordered `[9,1,0]` tree retains raw inorder, size and set; neither is incorrectly certified as a strict ordered tree. |
| G10 | Equal inorder permits different raw shape/height. Equal size/set permits `[1,2]` versus `[2,1]`, which have no all-right or all-left rotation trace. Set equality alone also loses multiplicity. |
| G11 | The constructed balanced-to-left-chain route has length 3 although one left step suffices. The four-node pair has a constructed route of length 6, attaining `2*n-2`, while one right step at the left child suffices. Empty and singleton connections use zero steps. |
| G12 | Descending from a root above the left chain decreases measure 6 to 5 while the smaller deficit remains 2. The root is blocked but its right-child position rotates; the schedule is `[[right],[right]]`. |
| G13 | Universal left/right-chain schedule, count, output and measure formulas, plus the frozen size 0–5 numeric table. |
| G14 | Empty, left-chain and seven-node applications of independent `exists_right_list`, plus a legal existential witness of length 3. Its proof-method requirement is checked separately from these cases. |
| G15 | Optional paper-only path-traversal illustration. No implemented traversal-cost or runtime claim and no extra acceptance gate. |
| G16 | Exact old `Branch` names/constructor elimination and `searchPathBy` queries 0–4 produce `[[L,L],[L],[],[R],[R,R]]`; existing heap clients remain in the validation closure. |
| G17 | Raw `ULift.{1} Nat` labels and keyed `Nat × ULift.{1}(Nat → Nat)` payloads exercise independent universes. Full payloads are preserved; applying their functions at 4 gives 14,24,34. The key projection is explicitly noninjective. |

### Optional path-traversal calculation

The retained G15 paper example separates the number of rotations from the work
of following their positions. Write `E` for an empty tree, `L_s = N(E,s,E)` for
a leaf, and `N(left,label,right)` for a node. Define

```text
Z(0,s)   = L_s
Z(k+1,s) = N(L_s,s+1,Z(k,s+2)).
```

Induction on `k` gives `2*k+1` nodes and right-spine length `k+1`. The first
root rotation of `Z(k+1,s)` exposes two right edges above `Z(k,s+2)`, so the
generated schedule has one empty position followed by the schedule for
`Z(k,s+2)` with two right directions prefixed to every position. Its `k`
rotation positions therefore have lengths `0,2,...,2*(k-1)`. Their total
number of direction entries is `2*(0+...+(k-1)) = k*(k-1)`, including zero
when `k=0`. For `k=0,1,2,3,4`, the totals are `0,0,2,6,12`.

For example, `Z(3,1) = N(L_1,2,N(L_3,4,N(L_5,6,L_7)))` generates
`[[],[right,right],[right,right,right,right]]`: three rotations and six
direction entries. An interpreter that starts at the root for every position
would perform those descents under a separately defined one-unit-per-direction
observation. This is retained paper mathematics, with no Lean traversal-cost
or native-runtime theorem claimed and no additional acceptance gate for
C05-042–065.

## Statement assessment and remaining work

Root success premises are justified by actual constructor cases. Generic edit
premises expose the callback's observation/inverse contract; they do not assume
the schedule's conclusion. The lower bound quantifies arbitrary successful
schedules and uses only their list-form endpoint. The existence result has no
computational-generator premise. Equality throughout is ordinary value equality,
with no claim about allocated cells or physical sharing.

Ordered transport uses the existing preorder-based inorder bridge. The keyed
transport is polymorphic in independent label/key universes, requires order only
on the keys, and has no key-injectivity hypothesis. The function-payload consumer
does not install an order or decidable equality on its payloads. Raw repeated
labels remain admissible for rotations, normalization, enumeration and recovery.

The count unit is successful rotations: an entry can traverse several edges.
No bound on path traversal, allocations, physical sharing or native execution
time follows. Right-only listification optimality does not assert optimality of
the two-phase mixed-direction connection. It does not define the later minimum
rotation distance or prove the exact `2*n-6` diameter for `n ≥ 11`.

After the established validation and checkpoint process, these 24 rows can add
to the preceding 41, yielding 65 of 94 Chapter 5 obligations. Rows C05-066–094,
the interval and sweep components, exact-distance/complexity results, the
separate search tariff, all remaining chapters/appendices and PFDS work remain
required. Receiving integration quality, branch-divergence assessment, the
whole-library build and exhaustive acceptance remain separate pending work.
This source note does not declare the complete chapter or all books finished.

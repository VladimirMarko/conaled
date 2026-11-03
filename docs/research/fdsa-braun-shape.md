# Shared Braun structural facts

## Status and selected boundary

This is the implementation-side source and statement assessment of FDSA-XT09.
The draft contains the common Braun shape invariant used by Chapter 11 arrays
and Chapter 16 priority queues, label-map invariance, uniqueness of erased shape
by size, and the almost-complete bridge. The actual core and connected example
sources were read in full for the declaration maps and scope assessment below.
This source assessment does not assert compilation or final review.

**This unit and its XT01/XT02 prerequisites remain uncompiled and unaccepted.**
Source reading, a local commit and a saved checkpoint are not either independent
final review or candidate validation. Accepted repaired Chapter 1 and the
preceding shared dependencies are prerequisites for integration and acceptance.
Neither Chapter 11 nor Chapter 16 is activated or completed by this unit.

The original source/review base is the saved XT02 draft
`974a97321a8ec174b56104c7e6efaaca881b6639`, with XT01 ancestor
`64c6b777d828ecfe83234fc2aed94600a1f24297`. The full frozen requirements are
retained outside the source diff in the checkpoint's
`fdsa-control/reviews/braun-shape-requirements.md`, SHA-256
`b7d1797e80ca2c732fd29632fea1ee5df0b296329bf1648d8ee714018a8f53f5`.
The original base, full requirements, findings and subsequent integration
history remain part of the review record. The exact initial Chapter 2 prefix
`c80eec92f5458eccfd1c34c8314d666c2a1e3847` is unchanged.

The selected source paths reuse the existing `BinaryTree` and `Trees` domain:
Braun-specific statements belong in `Applications/Trees/Braun.lean`, generic
constructor facts extend `Shape.lean`, and actual Real rounding formulas extend
`ShapeLog.lean`. The previous declarations and proofs are preserved. Connected
uses belong in `Examples/BraunShape.lean`; the public entrypoint imports that
module. This adds no second tree carrier, quotient, balancing hierarchy,
canonical generator, executable checker, resource model or algorithm.

## Source identity and attribution

The reference is *Functional Data Structures and Algorithms: A Proof Assistant
Approach*, version **July 27, 2026**. The
[official manuscript](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`
and 1,742,029 bytes. The relevant passages are Chapter 11 pp. 128–130 and 134,
its Exercises 11.1–11.8 on pp. 146–147, and Chapter 16 pp. 191–193. The
manuscript and extracted reading copies are research inputs, not source files
redistributed by this unit.

The structural Isabelle theories are pinned at mirror revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. The following links and content
identities identify the actual inspected companions. They postdate the
manuscript and are **not** asserted to be its generating revision.

| Inspected source | Relevant statements | SHA-256 |
| --- | --- | --- |
| [Braun_Tree.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Braun_Tree.thy), 6,544 bytes | Predicate/inequalities, lines 12–18; Unit-labelled uniqueness, 20–31; Braun-to-almost-complete, 35–40. The index layer at 47–181 remains separate. | `c6821391fce3c471e20d733d93cee8e7ba6d942edc87d51cf897817efac29db1` |
| [Tree_Real.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Tree_Real.thy), 4,280 bytes | Rounded heights, 29–58; one-larger constructor, 61–82; child symmetry and local symmetric constructor, 84–104; recursive symmetric balance, 106–112. | `e9a87ce2a0f0aee3f7747f9f662848f65bbb94921942611c12cca0d163e526c6` |
| [Tree.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Tree.thy), 17,104 bytes | Carrier, heights, completeness and symmetric size balance, 10–65; height optimality across label types, 333–335. | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| [Array_Braun.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Array_Braun.thy), 26,980 bytes | Actual operations/list observation, 14–30; array wrapper and invariant, 147–166; flexible operations, 171–232. These are later consumers, not new implementations here. | `eea8db081e474392bc75e817c15c42333996f093ef4361c7fc016da388c4ed9f` |

`Braun_Tree`, `Tree_Real` and `Tree` identify Tobias Nipkow as author.
`Array_Braun` credits Nipkow with contributions by Thomas Sewell; the Braun
index converse also credits Sewell. The applicable complete Isabelle notice
is reproduced below. The original notice is 1,673 bytes, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.

The Chapter 16 consumer is retained from the
[dated AFP archive](https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz),
10,112 bytes, SHA-256
`e6f6b1a8f08b001fd08d39adda0fb2f5ef5581e2294273bf54b03fe13497a72b`.
Its `Priority_Queue_Braun.thy` is 10,740 bytes, SHA-256
`2737d31cd0c32ac2d74bf46829faf6e9f740696d2c3b3f3c6cdea075a89e9f6e`.
The [entry](https://isa-afp.org/entries/Priority_Queue_Braun.html) identifies
Tobias Nipkow, September 4, 2014, under the BSD license; the retained
[AFP notice](https://isa-afp.org/LICENSE) has SHA-256
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`.
This unit cites that companion's domains and direct proof route; it does not
port a PQ algorithm or its independent direct height proof. Other archive
variants and the cited papers are not additional implementation milestones.

The existing Lean carrier and numeric interfaces use Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. `Mathlib/Data/Tree/Basic.lean`
credits Mario Carneiro and Wojciech Nawrocki under Apache-2.0; its inspected
identity is 6,679 bytes, SHA-256
`43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d`.
Existing Mathlib operations and XT01/XT02 facts are reused directly.

## Exact carrier and balance meanings

A source node is written with arguments left, label, right. Lean's existing
constructor is `BinaryTree.node a l r`, with the label first. Write `n`, `L`,
`h` and `m` for `numNodes`, `numLeaves`, `height` and `Trees.minHeight`:

```text
n(nil) = 0                 n(node a l r) = n(l) + n(r) + 1
L(nil) = 1                 L(node a l r) = L(l) + L(r)
h(nil) = 0                 h(node a l r) = max(h(l), h(r)) + 1
m(nil) = 0                 m(node a l r) = min(m(l), m(r)) + 1
L(t) = n(t) + 1.
```

These are node-labelled trees with empty external leaves. Their size is
neither `sizeOf`, a cached value, nor the leaf count of the existing nonempty
random-access-tree carrier. The actual Braun invariant is

```text
Braun nil = True
Braun (node a l r) iff
  (n(l) = n(r) or n(l) = n(r) + 1) and Braun l and Braun r.
```

The equivalent node inequalities are `n(r) ≤ n(l) ≤ n(r)+1`, retaining both
recursive child predicates. Labels are never inspected. In a valid Braun node,
empty left forces empty right; empty right may accompany a singleton left.
Those two emptiness conditions are not interchangeable.

Three distinct conditions appear in the source:

| Condition | Mathematical meaning | Boundary retained here |
| --- | --- | --- |
| Braun | Equal child sizes or left one larger, recursively at every node. | Both recursive hypotheses and the direction of the size bias matter. |
| Symmetric size balance | At a node, both `n(l) ≤ n(r)+1` and `n(r) ≤ n(l)+1`; the source also defines a recursive version. | A single truncated Nat subtraction is not an absolute difference. This unit uses the local inequalities and does not define the separate recursive predicate. |
| Almost complete | `h(t) ≤ m(t)+1`: external leaves occur on one or two adjacent levels. | There is no orientation or left-packing condition. The existing source Nat-subtraction equivalence remains in XT02. |

A recursive logical predicate is not a costed executable validity checker.
No size caching or evaluation-cost claim is attached to `Braun`.

## Label transport and exact shape uniqueness

For any supplied `f : α → β`, with independent input/output universes, the
selected structural map statement is

```text
Braun (t.map f) ↔ Braun t.
```

No injectivity, order, equality decision, finiteness or payload inhabitant is
needed. Mapping preserves the same child positions and node counts. Hence
constant relabelling cannot repair a non-Braun shape, and an arbitrary map can
preserve Braun while changing payload observations or destroying heap
order. This is an equivalence of shape predicates, not a stronger claim about
all observations of the tree.

For independently typed `s` and `t`, the uniqueness conclusion is exactly

```text
Braun s → Braun t → s.numNodes = t.numNodes →
  s.map (fun _ => ()) = t.map (fun _ => ()).
```

The equality lives in `BinaryTree Unit`. At two nonempty roots, the equal
parent totals and each pair of Braun inequalities force both corresponding
child counts equal. Recursive shape uniqueness then applies to each child.
The nil/node case is excluded by node count. This does not require enumerating
trees, a canonical tree generator or a new shape relation.

Both Braun premises are substantive. Equality of counts, heights or almost
completeness alone does not identify the shape. The source's Unit-labelled
equality is a specialization of the same intended result. It does not assert
raw equality across payload types, equal inorder lists, array-content equality,
or the existence of a positive-size tree over an arbitrary label type.
`BinaryTree Empty` has its genuine nil case and has no nonempty node.

## Constructor arithmetic and actual rounded formulas

The generic local constructor assumes that **both children are almost
complete** and that their node counts differ by at most one in either direction.
It concludes that `node a l r` is almost complete, for any root label. It does
not require either child to be Braun. Equal-sized malformed children show why
their AC hypotheses cannot be dropped.

For the equal-size case, equal external-leaf counts and the existing exact
AC log/clog formulas identify both child heights and both minimum heights.
The parent's successor equations retain their gap of at most one. The two
one-larger orientations use the corresponding arithmetic and min/max symmetry.

The source's displayed one-larger identities are retained as mathematical
statements. Assume both children AC and `n(l)=n(r)+1`. Put `k=L(r)`. The raw
leaf-count positivity theorem gives `k≥1`, and `L(l)=k+1`. The actual parent
observations are

\[
h(\operatorname{node}(a,l,r))=\operatorname{Nat.clog}(2,k+1)+1,
\qquad
m(\operatorname{node}(a,l,r))=\operatorname{Nat.log}(2,k)+1.
\]

Let `i = Nat.log 2 k`. The source power step changes its strict endpoints:

\[
2^i\le k<2^{i+1}
\quad\Longrightarrow\quad
2^i<k+1\le2^{i+1}.
\]

The existing Nat log/clog bounds therefore give `Nat.clog 2 (k+1)=i+1`.
This is the adjacent-power argument supporting the one-larger constructor;
a statement that only the final AC conclusion holds would omit the selected
intermediate source mathematics.

`ShapeLog` supplies the corresponding **natural-rounded Real** formulas:

\[
h(\operatorname{node}(a,l,r))=
 \left\lceil\log_2((k+1):\mathbb R)\right\rceil_{\mathbb N}+1,
\qquad
m(\operatorname{node}(a,l,r))=
 \left\lfloor\log_2(k:\mathbb R)\right\rfloor_{\mathbb N}+1.
\]

Here the base logarithm is `Real.logb 2`; the arguments are casts of the same
natural `k+1` and `k`. Existing `Real.natCeil_logb_natCast` and
`Real.natFloor_logb_natCast` bridge these formulas to the natural ones. They
are not unrounded Real-height equalities or floating-point approximations.
Real analysis remains in the separate `ShapeLog` layer.

The empty right child is included: `k=1`, a singleton left gives parent
height 2 and minimum height 1. No positive-node premise on the right child
is justified. In particular, the empty external leaf is not discarded to
avoid a logarithm side case.

## Braun height and optimality through the existing shape layer

The recursive Braun predicate supplies both child Braun hypotheses and the
local size condition. Induction using the selected constructor gives
`Braun t → Trees.AlmostComplete t`. Applications then consume the existing
XT02 theorems directly:

\[
m(t)=\operatorname{Nat.log}(2,L(t)),\qquad
h(t)=\operatorname{Nat.clog}(2,L(t)).
\]

Their Real versions use natural floor and ceiling of `Real.logb 2 L(t)`.
The source's `n(t)+1` is exactly `L(t)`, including nil. Nil has `n=0`, `L=1`,
`h=m=0`, and both logarithms of 1 give 0.

`Trees.height_optimal` compares a Braun tree `s`, through its actual AC proof,
with any `t` satisfying `s.numNodes ≤ t.numNodes`. The competitor may use an
unrelated payload type and need not itself be Braun or AC. The conclusion is
`s.height ≤ t.height`. It is a structural optimum, not an operation-count
bound or an optimality claim about an array or priority-queue algorithm.

The separate direct route required by **C11-122 / Exercise 11.1** remains open:
first prove `2^h ≤ 2*n+1` by induction without first establishing AC, then
derive the exact ceiling height. The retained
`Priority_Queue_Braun.thy` lines 22–36 contains an actual direct inductive proof
route, but this unit does not port it. Using the new Braun-to-AC result with
an existing height theorem does not satisfy that exercise's proof instruction.
The universal capacity bound from XT02 remains available for the later direct
route because its own proof does not use AC.

## Connected cases and representation boundaries

The cases retain independently calculated expectations and use public results.
The actual declaration map below records those connections in the draft source.

| Case family | Independent mathematical conclusion |
| --- | --- |
| Nil, singleton and arbitrary `BinaryTree Empty` | Braun applies without a payload default; nil has nodes 0, leaves 1 and both heights 0. Both rounded log1 boundaries are retained. |
| Existing `chain 2` and `rightTwo` | Left-only two nodes are Braun; right-only two nodes are AC but violate Braun bias. Their erased shapes differ despite equal node counts. |
| Existing `balancedThree` / `perfectThree` and `leftThree` | Complete three nodes are Braun; the three-node chain is not. Repeated-label inorder `[1,1,1]` does not determine height or balance. |
| A root over two `leftThree` children | Root child counts agree at 3/3, but height 4 and minimum height 2 refute AC. Both child AC premises are necessary for the local constructor. |
| Five-node B5 / A5 | Both have nodes 5, leaves 6, height 3 and minimum height 2. B5 has left-only two-node children of sizes 2/2 and is Braun. A5 has a complete three-node left child and singleton right child, is AC, and fails the size bound and Braun predicate. Their erased shapes differ. |
| Arbitrary and noninjective label maps | Shape invariance is an iff across independent universes. Different Bool singletons retain equal erased shape while their payload trees and inorder values differ. |
| Actual `Cached.erase` and `annotate` | Shape transport composes with the existing maps without cache validity. Correct size reads use the separate recursive validity or actual annotation theorem. |

The five-node case uses the existing log and optimality laws after an actual
Braun-to-AC connection. It also exhibits the converse failure: optimal height
and even both exact AC height formulas do not characterize Braun.

### Braun is not ordinary breadth-first left packing

For B5, the root has children of sizes 2/2, each with a left singleton. Ordinary
heap-path numbering gives positions `{1,2,3,4,6}`. The source Braun index
recurrence instead gives `{1,2,3,4,5}`. A5, with children 3/1, has those two
index sets reversed. This is a distinction between path conventions, not an
error in the Braun invariant.

The source recurrence is `I(nil)=∅` and
`I(node a l r)={1} ∪ {2*i | i∈I(l)} ∪ {2*i+1 | i∈I(r)}`. It reads low path
bits first. A left-right path has source index 6 and ordinary heap-path index 5;
a right-left path has source index 5 and ordinary heap-path index 6. These
finite calculations do not prove the full general index characterization or
its converse.

The array observation is also separate: `Array_Braun.thy` defines root followed
by a splice of the two child lists, rather than inorder. With B5 labels root
`a`, children `b,c`, and their left children `d,e`, the array list is
`[a,b,c,d,e]` and inorder is `[d,b,a,e,c]`. For a complete seven-node tree
labelled by the source indices, the array list is `[1,2,3,4,5,6,7]`, ordinary
BFS is `[1,2,3,4,6,5,7]` and inorder is `[4,2,6,1,5,3,7]`.
These documented source boundaries select no indexing or traversal algorithm
for this unit. Erased-shape uniqueness is not array-observation injectivity.

### Cache validity is a different predicate

`Trees.Cached.erase` is the actual label map `Prod.fst`. Its shape connection
requires no `Cached.Valid`. Composing with `erase_annotate` transports Braun
to the actual result of annotation for any supplied fold algebra. No new
annotation representation or homomorphism assumption is needed.

For the size algebra, `annotate_valid` establishes all-node cache correctness;
`read_annotate` and `fold_numNodes` connect the actual returned root cache to
node count. For an arbitrary previously annotated tree, `read_eq_fold` instead
retains its real recursive `Cached.Valid` premise. A shape fact cannot replace
that premise.

The existing `sizeSample` is correctly cached but has root child sizes 1/2,
so its shape is not Braun. The existing `corrupt.left` is a Braun singleton
with a stored size 2, so its size cache is invalid. These expose both directions
of the distinction using actual retained values. The source array wrapper
stores one global length with a tree and requires `Braun t ∧ length=n(t)`;
it is not being replaced by XT01's per-node cache representation.

### Heap validity, rebuilding and running time remain algorithm-specific

Chapter 16 validity is `Braun t ∧ heap t`. A root 1 with left child 0 has Braun
shape and fails min-heap order; a root 0 with right child 1 is a min-heap and
fails Braun. Arbitrary label-map invariance of Braun therefore does not imply
heap preservation. The source root-minimum claim still needs heap order and
nonemptiness.

The PQ's actual `del_left` extracts from the left and rebuilds with the old
right subtree on the **left** and the extracted remainder on the **right**.
Ordinary BST `split_min` rebuilds those children in their original positions.
For the retained all-1 complete three-node shape, ordinary extraction leaves
a right-only two-node residual; the Braun operation leaves a left-only residual.
Both residuals have the same inorder `[1,1]` and count 2, but only the latter
is Braun. With distinct root/right labels even their inorder lists differ.
This is not an implementation or proof bridge from XT08, and no XT08 dependency
is introduced here.

Structural height may enter a cost proof only after the actual algorithm and
its tariff have been related to that height. The retained PQ source has
separate insertion, nonempty `del_left`, sift and deletion bounds; its generated
`del_min` trivial branches have zero charge while `del_left` has a nonempty
base charge and no empty source equation. The basic array lookup/update and
later specialized constructor time functions have their own source domains
and conventions. This unit introduces no cost observation and transfers no
whole-fold, cache-access, ordinary-extraction or machine-runtime cost to them.

## Actual declaration and public-case map

The following names are present in the actual source. All core declarations
are in namespace `Trees`; the connected examples are in `BraunShapeExamples`.
Their source-level connections remain subject to elaboration and all later
gates. Existing XT01/XT02 results are identified separately from new statements.

| File / role | Actual declarations | Source meaning and domains |
| --- | --- | --- |
| `Applications/Trees/Braun.lean`: predicate | `Braun`, `braun_nil`, `braun_node`, `braun_node_iff` | Exact recursive predicate and oriented inequality form. Both child predicates remain; no payload capability or runtime checker is introduced. |
| Arbitrary label transport | `braun_map label t` | Preserves and reflects Braun across independent universes, without injectivity. |
| Erased-shape uniqueness | `braun_shape_eq s t hs ht hsize` | Equality in `BinaryTree Unit`, from both actual Braun proofs and equal node counts. |
| Source Unit specialization | `braun_eq_of_numNodes_eq s t hs ht hsize` | Raw equality is concluded only for Unit-labelled trees. This consumes erased-shape uniqueness. |
| Shared height premise | `braun_almostComplete t ht` | Recursion on the actual predicate, using the local symmetric constructor. Existing log/optimum facts are then consumed directly. |
| Additions to `Applications/Trees/Shape.lean` | `height_node_eq_clog_of_numNodes_succ`, `minHeight_node_eq_log_of_numNodes_succ` | Each takes `a l r hl hr hsize`; the two AC hypotheses and left-one-larger count equation give the actual parent identities. |
| General local constructor | `almostComplete_node_of_numNodes_balance a l r hl hr hlr hrl` | Both AC children and both explicit count inequalities; equal, left-one-larger and right-one-larger cases. No recursive symmetric predicate is defined. |
| Additions to `Applications/Trees/ShapeLog.lean` | `height_node_eq_ceil_logb_of_numNodes_succ`, `minHeight_node_eq_floor_logb_of_numNodes_succ` | Same one-larger arguments, with actual Nat-to-Real casts and the existing natural-rounding bridges. |
| Unchanged XT02 conclusions | `minHeight_eq_log_numLeaves`, `height_eq_clog_numLeaves`, `minHeight_eq_floor_logb_numLeaves`, `height_eq_ceil_logb_numLeaves`, `height_optimal` | Applications after a supplied `AlmostComplete` proof. No duplicate Braun-specific logarithm hierarchy is added. |
| Unchanged observation/cache interfaces | `numNodes_map`, `height_map`, `inorder_map` (XT01); `minHeight_map` (XT02); `Cached.erase`, `erase_annotate`, `annotate_valid`, `read_annotate`, `read_eq_fold`, `fold_numNodes` | Actual shape/label and cache connections, preserving each theorem's own premises. |

The adjacent-power proof is retained in the private arithmetic support in
`Shape.lean`: its lower strict inequality is about `k+1`, not `k`, and its
upper weak inequality is likewise about `k+1`. The local constructor uses
positive external-leaf count. The separate Real results rewrite through the
pinned floor/ceiling bridge; they do not merely cite the natural formulas in
prose.

| Actual example group | Public-law connection and retained conclusion |
| --- | --- |
| `singleton_braun`, `single_braun`, `chainTwo_braun`, `perfectThree_braun`, `balancedThree_braun` | Instantiate `braun_node` / `braun_node_iff` with the real child proofs. They retain a generic singleton label and both permitted size cases. |
| `rightTwo_not_braun`, `leftThree_not_braun`, `sample_not_braun`, `repeated_payload_boundary` | Use the actual inequality form and existing repeated-label inorder observation to distinguish shape, bias and semantic occurrences. |
| `rightTwo_symmetric_constructor` | Applies the new local constructor to the mirrored orientation, while retaining the proof that this tree is not Braun. |
| `chainTwo_source_heights` | Calls all four new Nat/Real parent-identity theorems with a nil right child, producing maximum height 2 and minimum height 1. |
| `empty_braun_observations`, `empty_braun_rounding` | Use the actual `BinaryTree Empty` result, Braun-to-AC and unchanged Nat/Real log laws. Node0/leaf1 and both log1 boundaries are preserved. |
| `badEqualChildren_shape`, `leftThree_not_almostComplete`, `badEqualChildren_not_braun` | Independent height/min-height calculations refute root-only balance; the Braun failure also consumes `braun_almostComplete`. |
| `braunFive_shape`, `braunFive_braun`, `braunFive_almostComplete` | Connect the independently calculated B5 measurements to the actual new predicate and bridge. |
| `almostFive_shape`, `almostFive_almostComplete`, `almostFive_local_size_failure`, `almostFive_not_braun`, `erased_five_shapes_ne` | Retain the A5 converse/uniqueness boundary: same counts and both heights, AC true, size condition and Braun false, erased shapes different. |
| `braunFive_rounding`, `braunFive_height_nodes`, `braunFive_optimal` | Derive log2(6) floor2/ceiling3, the node-count-plus-one formula, and the optimum against any independently typed competitor with at least five nodes. |
| `mapped_observations`, `mapped_braun_optimum`, `equal_size_braun_observations` | Compose actual map/shape/erasure laws and the general height optimum across independent payload universes; erased equality also identifies both heights. |
| `collapsed_balanced_shape`, `constant_sample_not_braun`, `bool_singleton_boundary` | An actual noninjective Nat-to-Unit map invokes both `braun_map` and Unit uniqueness; constant mapping cannot repair the non-Braun sample; different Bool payloads remain observably different. |
| `braun_erase_iff`, `braun_annotate_iff` | Apply the actual `Prod.fst` map and `erase_annotate` to arbitrary annotated trees and supplied fold algebras, without a cache-validity premise for shape. |
| `annotated_size_contract`, `cached_shape_and_size`, `sizeBraunFive_contract` | Combine Braun transport with the actual annotation validity/read equations. An arbitrary existing cache keeps its `Valid` premise; the concrete size annotation erases to B5 and reads 5. |
| `valid_cache_nonBraun`, `braun_invalid_cache` | Existing `sizeSample` and `corrupt.left` demonstrate both independence directions between recursive cache validity and Braun shape. |

The core Unit specialization and the concrete collapsed shape are both actual
uses of the generic erased equality. The map/optimum clients use three
independent payload types rather than requiring a shared carrier. The cache
clients consume actual constructed annotation values and the supplied existing
cache validity; they do not replace an implementation by a desired observation.

## Coverage and retained obligations

| Original source obligation | Selected contribution |
| --- | --- |
| C11-008; C16-001 shape component | The exact recursive Braun predicate, node equations and equivalent size inequalities. |
| C11-014 | The actual one-larger AC constructor, within the more general local symmetric constructor with AC children. |
| C11-015 | The parent Nat log/clog identities, adjacent-power interval and actual natural-rounded Real correspondence. |
| C11-016 | Braun-to-almost-complete using the recursive child hypotheses. |
| C11-017; C16-042 height input | Applications of the unchanged exact rounded-height and cross-type height-optimality theorems after the Braun bridge. No operation-time conclusion is included. |
| C11-019 | Equal-size uniqueness of Unit-erased shapes, with both Braun premises and arbitrary payload types. |

This table records source correspondence, not chapter-row acceptance. The
previous XT02 note deliberately left Braun/weight-balance bridges for later
work. Its text and original scope remain unchanged; XT09 explicitly supplies
only the selected follow-up above.

C11-018's full recursive symmetric-balance predicate and global AC result
remain mandatory later work. The local symmetric constructor does not by
itself discharge that separate source statement. C11-122 retains the direct
Exercise 11.1 route without AC. Exercises 11.2–11.8 retain their own left-spine,
child-height, actual `Balance.bal`, index/update, deletion, initialization and
cost requirements.

The full index positivity/cardinality/contiguity theorem and its converse,
array-order observation and injectivity, wrapper/cache contracts, basic and
flexible operations, source constructors, conversions and their running times
remain in Chapter 11. Heap order, partial domains, actual insertion, swapping
extraction, sift, minimum deletion and every source tariff/cost proof remain
in Chapter 16. All 135 Chapter 11 rows, all 48 Chapter 16 rows, Appendix B and
all other original book and appendix obligations remain required. No particular
extra general framework or canonical generator is required merely by this exclusion list.

## Statement and validation assessment

The complete actual Braun, Shape, ShapeLog and BraunShape example sources were
read, including the generic observation/cache interfaces consumed above.
The source-level assessment found no concrete mathematical or source-coverage
mismatch in the selected scope. It checked the following consequential points:

- The actual definition carries both recursive Braun premises and the left-size
  bias. The local constructor instead has both AC child hypotheses and the two
  symmetric inequalities; these contracts are not interchanged.
- The map statement is an iff over arbitrary supplied functions. Erased-shape
  uniqueness has two independently typed inputs, two actual Braun proofs and
  equal node counts, with Unit as the common output. No labelled equality or
  positive-size existence is inferred.
- The actual one-larger identities use `r.numLeaves+1` for the maximum-height
  ceiling and `r.numLeaves` for the minimum-height floor. Positivity includes
  nil's external leaf. The adjacent power inequalities change strict endpoints
  correctly; the Real casts describe those same natural arguments.
- The Empty, singleton, mirrored, malformed-child and five-node cases have the
  intended nonvacuous domains. The optimum competitor is neither assumed Braun
  nor constrained to the same payload universe.
- The connected cases invoke the public core and existing shape/cache results.
  Numeral reductions establish independently calculated hypotheses or readings;
  they do not replace the required public-law connection. Cache-reader results
  retain actual recursive validity or consume the actual annotation theorem.
- C11-018 and Exercise 11.1's direct route remain separate required work. The
  written source adds no index operation, PQ/array algorithm or cost theorem.

This is implementation-side source assessment, not either independent final
review axis. No elaborated type, compiler warning policy, complete candidate
check, integrity pass or proof audit has been validated by this readback.

Later acceptance requires the matching focused and complete guarded candidate
validation, both integrity phases, all local modules and exhaustive transitive
axiom audit, both independent Standards and Spec axes, and immediate matching
candidate verification. Frozen requirements and original review bases survive
integration and corrections. The local review record owns those outcomes;
this narrative does not infer them from source presence.

## Applicable Isabelle notice

The structural source adaptation retains the complete following notice from
the pinned Isabelle distribution. The AFP source above is separately attributed
as contextual evidence for later obligations; no algorithm or direct-proof
adaptation from that archive is included in this unit.

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

# Shared tree rotations — independent mathematical case preflight

Recorded 2026-11-02 by the delegated case reader. This is a bounded mathematical
and source/API assessment, not implementation, compilation, a final review axis,
or acceptance. The parent subsequently authorized this report as the sole new
write. No existing file, source, requirement, Git ref, cache or running gate was
changed. No compiler, checker or project hash helper was run.

## Inputs and scope

The supplied saved reference is XT01 candidate
`64c6b777d828ecfe83234fc2aed94600a1f24297` in `conaled-tree-cache`.
This reader inspected its actual tree, cache, measured-constructor and example
files. It read AGENTS, architectural/domain guidance, the glossary, ADRs 0001
and 0010, the example-driven skill and worked example, and the complete XT01
frozen requirements. The saved XT02/XT05 material was consulted only for scope;
no result from either is needed by the calculations below. XT01 itself remains
unaccepted and uncompiled in the recorded project state.

The exact source-book locations and chapter-specific rotation contracts belong
to the separate source assessment. This report does not assert that its proposed
local tariff is a printed book theorem. Its recommendation is a small operation
and observation component on the existing carrier, without a new tree algebra,
container framework, syntax layer, BST predicate or balancing algorithm.

For formulas below, `N(x,A,B)` abbreviates the existing `BinaryTree.node x A B`
and `Z` denotes its existing `nil`; these are prose abbreviations, not proposed
new Lean definitions or a competing carrier. Consider the matching shapes

```text
L = N(x, A, N(y, B, C))
R = N(y, N(x, A, B), C).
```

A left rotation maps L to R; a right rotation maps R to L. The fringe trees
A, B and C and payloads x and y are arbitrary. Their payload type needs no
order, decidable equality, inhabitant or finiteness assumption.

## 1. Exact existing interfaces and reusable cases

Paths in this table are relative to `conaled-tree-cache`; the numbers identify
declaration starts in the inspected source, not proof-validation evidence.

| Path | Existing declarations and start lines | Use |
| --- | --- | --- |
| `.lake/packages/mathlib/Mathlib/Data/Tree/Basic.lean` | `BinaryTree`, `BinaryTree.map`, `numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ` | Canonical node-labelled carrier and observations; no replacement size/height API. |
| `Applications/Trees/Observations.lean` | `fold` 17, `fold_node` 24, `fold_map` 30, `fold_fusion` 41, `fold_numNodes` 52, `fold_height` 59 | Arbitrary ordinary fold and explicit transport laws. |
| Same file | `inorder` 68, `inorder_node` 73, `inorder_length` 76, `inorder_map` 82, `numNodes_map` 89, `numLeaves_map` 96, `height_map` 100 | Full ordered occurrence observation and label/shape compatibility. |
| `Applications/Trees/Cached.lean` | `erase` 15, `read` 23, `smartNode` 34, `read_smartNode` 39, `erase_smartNode` 44 | Actual product-labelled cache carrier and local rebuild. |
| Same file | `Valid` 49, `valid_node` 59, `smartNode_valid_iff` 66, `read_eq_fold` 77 | Recursive validity, exact retained-child boundary and independent fold semantics. |
| Same file | `inorder_erase` 89, `numNodes_erase` 93, `height_erase` 99, `annotate` 103, `annotate_valid` 116, `erase_annotate` 123, `read_annotate` 130 | Concrete preparation of valid cached fixtures; erasure preserves only the underlying payload observation. |
| `Applications/Resources/Measured.lean` | `pure` 15, `bind` 17, `bind_value` 23 | Existing sequencing; the next operation consumes the actual returned first value. |
| `Applications/Resources/TreeCache.lean` | `readRun` 19, `nodeRun` 30, `nodeRun_value` 39, `nodeRun_cost` 53, `nodeRun_le` 60, `nodeRun_valid` 68 | One local constructor executes two cache reads, the supplied callback, and one entry tick. |
| `Examples/TreeCache.lean` | `sizeStep` 17, `heightStep` 18, `pairStep` 71, `ordered_summary_fold` 119 | Existing scalar/pair observations and composition with an arbitrary noncommutative monoid. |
| Same file | `balancedThree` 150, `leftThree` 151, `same_inorder_different_height` 154 | Existing repeated-label shape boundary; these two trees are exactly one left rotation apart. |
| Same file | `empty_tree` 168, `empty_observations` 177 | Existing Empty-payload boundary. |
| Same file | `corrupt` 190, `corrupt_root_checks` 194, `corrupt_not_valid` 200 | A correct root observation/local equation cannot replace recursive validity. |
| Same file | `appendStepRun` 290, `append_node_value` 293, `append_node_cost` 300, `append_node_valid` 307 | Actual existing recursive append as a list-summary callback, with cost `length(left cache)+4`. |
| Same file | `chainCache` 324, `chainCache_valid` 327, `chainCache_read` 330, `chainCache_length` 334, `chain_node_exceeds` 355 | Arbitrarily long, valid, repeated-label prepared caches and the existing nonconstant-callback boundary. |
| `Applications/Sequences/OrderedSummary.lean` | `summary`, `summary_nil`, `summary_append`, `summary_singleton` | Existing free-monoid extension retains multiplication order. |

The targeted search found no rotation/reassociation definition in the inspected
`Applications/Trees` or pinned Mathlib `Data/Tree` files. XT01's frozen scope
explicitly excludes rotations. The separate architecture reader owns the wider
reuse assessment. No claim is made that similarly named operations on other
carriers can be substituted without a proved bridge.

## 2. Small ordinary cases

### Generic matching shapes and ordered duplicates

The direct independent calculation is

```text
inorder(L) = inorder(A) ++ [x] ++ inorder(B) ++ [y] ++ inorder(C)
inorder(R) = inorder(A) ++ [x] ++ inorder(B) ++ [y] ++ inorder(C).
```

Equality follows from list associativity and preserves order and multiplicity,
not just set membership. Node counts agree at `|A|+|B|+|C|+2`; leaf equality can
reuse `numLeaves_eq_numNodes_succ`. An arbitrary label map acts on both shapes
in the same positions, even when it identifies labels. The shape formulas are
mutual inverses on their matching domains.

A compact noncommutative-word case makes every fringe nonempty: let A be a
singleton labelled `q`, B another singleton labelled `q`, C a singleton labelled
`p`, x=`r`, y=`s`. Both inorders are exactly

```text
[q, r, q, s, p].
```

Both trees have five nodes and six leaves. A word summary retains that exact
word. Mapping every payload to Unit yields five Unit occurrences, preserving
shape despite the noninjective map. This is one fixture family, not a demand
for a separate theorem or test for every helper declaration. The empty-fringe
specialization A=B=C=Z has two nodes, three leaves and inorder `[x,y]`.

### Failure shapes and Empty

A faithful optional root adapter can return `none` for a left rotation at Z or
`N(x,A,Z)`, and symmetrically for a right rotation at Z or `N(y,Z,C)`. Alternatively,
the operation can take the explicitly matching shape/domain. Do not invent a
payload for a missing pivot, or silently claim that identity fallback is the
source's unspecified branch. The source assessment must choose the adapter's
actual correspondence.

Every `t : BinaryTree Empty` is Z by the existing example `empty_tree`; neither
rotation has a success witness there. Thus Empty tests absence of an accidental
`Inhabited` payload premise without requiring a positive-size Empty tree.
A singleton supplies both ordinary invalid-shape cases on an inhabited carrier.

### Reuse the existing height/balance counterexample

The existing `balancedThree` is
`N(1,N(1,Z,Z),N(1,Z,Z))`. Its left rotation is exactly the existing `leftThree`,
`N(1,N(1,N(1,Z,Z),Z),Z)`. Both have size 3 and inorder `[1,1,1]`, while their
heights are respectively **2 and 3**.

This one connected use refutes arbitrary height preservation, nonincreasing
height, and an unconditional claim that a rotation improves balance. It is also
a counterexample to preservation of an arbitrary tree fold: choose the existing
height algebra `max l r + 1`. No new shape fixture is needed. The inverse right
rotation decreases height, so neither fixed direction has a universal monotone
height effect. Bounds or balancing side conditions specific to AVL/splay/etc.
remain in their owning algorithms.

## 3. Summary preservation has an explicit algebraic boundary

Let `f : beta -> alpha -> beta -> beta` be the node operation and z the empty
summary. Write a, b and c for the three actual fringe folds. The old and new
root folds are respectively

```text
f a x (f b y c)
f (f a x b) y c.
```

The local rotation equation equating these expressions is sufficient. Requiring
it for every summary and payload is a reusable stronger operation law, but a
proof may need only the reached values. The equation must not be silently
assumed for the generic `Trees.fold` operation. Height gives the concrete
counterexample above.

For an existing `[Monoid M]` and payload observation `measure : alpha -> M`,
choose z=1 and `f l a r = l * measure a * r`. Associativity proves the rotation
equation, with no commutativity or injectivity premise. The existing universal
`TreeCacheExamples.ordered_summary_fold` connects this result to
`Sequences.OrderedSummary.summary (Trees.inorder t)`; its free-word use exposes
order. Such a client belongs with the existing Examples composition, so a new
domain module need not import an Examples module or move that existing result.

The size algebra is another preserving specialization. The pair `(size,height)`
correctly illustrates a mixed observation: the size component is preserved but
the height component must be recomputed and can change from `(3,2)` to `(3,3)`.

## 4. Cached rotations: validity and summary equality are different claims

Use the existing product-labelled carrier and perform two actual local smart
constructions. A left rebuild of the three supplied cached fringes is

```text
lower = smartNode z f A x B
result = smartNode z f lower y C.
```

Two applications of `erase_smartNode` give the ordinary rotated payload tree.
Two applications of `smartNode_valid_iff` give exactly

```text
Valid z f result <-> Valid z f A /\ Valid z f B /\ Valid z f C.
```

This requires no associativity or order law. The two old top annotations are
not used by this reconstruction and need not be postulated correct merely to
prove the newly built result valid from its three valid fringes. A valid whole
input is a convenient way to obtain those fringe premises.

Equality of the old and new root summaries is an additional claim. It needs
appropriate old-cache correctness plus the rotation equation above (or a
specialized semantic observation such as the monoid inorder summary). Rebuilding
a valid height cache preserves its correctness, not its old stored height.

A raw rotation on product labels instead retains old annotations with their
payloads. For `annotate 0 sizeStep balancedThree`, the original root/left/right
annotations are `3/1/1`. Raw rotation yields root annotation **1** and lower
annotation **3**, although those subtrees now have respectively **3** and **2**
nodes. The raw result is not a valid size cache. Correct smart rebuilding yields
root/lower/remaining-leaf annotations `3/2/1`.

This also distinguishes full annotated inorder from erased payload inorder:

```text
before: [(1,1), (1,3), (1,1)]
after correctly rebuilding: [(1,1), (1,2), (1,3)].
erased payloads in both cases: [1,1,1].
```

Thus a cache-updating rotation must preserve `Trees.inorder (Cached.erase t)`,
not assert equality of the full `(payload,annotation)` inorder. The raw product
rotation preserves those full pairs but breaks cache validity; the two operations
have genuinely different contracts.

Invalid retained descendants remain invalid. Taking the existing `corrupt`
fixture as A and rebuilding two roots cannot repair its descendants, directly
by the same two `smartNode_valid_iff` applications and `corrupt_not_valid`.
Its root cache nevertheless equals its actual size, so even the newly built
upper root may have the correct numeric size while recursive validity fails.
Reuse this existing boundary; a new malformed-tree campaign is unnecessary.

## 5. Actual local work from existing measured constructors

The natural measured left rebuilding sequence is the ordinary composition

```text
bind (nodeRun z callback A x B)
     (fun lower => nodeRun z callback lower y C).
```

Write a=`read z A`, b=`read z B`, c=`read z C` and let the actual first callback
return `(v1,c1) = callback a x b`. The second callback is evaluated at
`callback v1 y c`, returning work c2. The exact natural observation is

```text
(c1 + 3) + (c2 + 3) = c1 + c2 + 6.
```

The second callback must consume v1, not an independently assumed ideal summary.
`nodeRun_value` can later establish its agreement with f under the actual value
contracts. `nodeRun_valid` gives cache correctness from those contracts and the
fringe validity separately. The exact cost identity itself does not require
cache validity or callback correctness. Reached bounds `c1<=K1`, `c2<=K2` give
`cost<=K1+K2+6`; a common bound K gives `2*K+6`.

The six helper units are exactly two existing nodeRun executions, each with two
root reads and one constructor entry. No additional wrapper entry is charged
in this proposed composition. If an eventual wrapper explicitly adds one, its
count must say so. Preparing the fringes, observing erasure/folds in a theorem,
allocating physical memory and invalid-shape handling are not silently included.
This is XT01's declared local-access interpretation, not a machine runtime or
an inherited selective book tariff.

### Constant scalar callback specialization

The existing `sizeRun` and `heightRun` callbacks have zero observation, so the
two-node composition costs **6**. For the balancedThree case, a correct size
cache still reads 3 after rotation; a correct height cache reads 3 instead of 2.
This ties the fixed local count to concrete actual callbacks while preserving
the distinction between invariant and shape-sensitive observations.

### Actual recursive append callback: independent exact counts

Use existing `appendStepRun`, which executes
`ListReversal.appendRun leftSummary (a :: rightSummary)`. Let the actual prepared
fringe list-cache lengths be p, q and r. Under their validity, these lengths equal
the respective underlying subtree sizes; the basic local count algebra needs
only the actual cached lists and the callback's proven value equation.

For a left rebuild:

1. The lower constructor executes append on A's list. Its work is `p+4`.
2. Its actual returned root list has length `p+q+1`.
3. The upper constructor therefore has work `(p+q+1)+4`.

Consequently the total is **`2*p+q+9`**.

For the inverse right rebuild, construct `smartNode B y C` first and then use
it as the right child in `smartNode A x lower`. The first work is `q+4`; the
second still appends A's list and costs `p+4`. The total is **`p+q+8`**.

Both final payload inorders are the same. Equal observations do not imply equal
construction work. When each fringe is a singleton (p=q=r=1), the totals are
**12 and 10**. The r term is absent from this one-append tariff because the
right list is reused; it remains present in the returned ordered value.

An existing valid-cache family supplies the decisive constant-work boundary:
use `chainCache n` as A and nil as B and C, with Unit payloads at both rebuilt
nodes. Existing `chainCache_valid` and `chainCache_length` give p=n and q=0.
The actual counts become **`2*n+9`** and **`n+8`**, respectively, for arbitrarily
large n. At n=0 the values are already 9 and 8, despite both ordinary trees
having two nodes. Thus rebuilding two nodes is not an unconditional constant-cost
theorem for arbitrary cached folds or callbacks, even with fully valid prepared
caches. No new chain constructor, cost evaluator or asymptotic framework is needed.

## 6. Recommended compact component and retained limits

The cases support a small reusable unit consisting of the ordinary matching
rotation equations and their full inorder/map/size consequences, an explicitly
qualified fold-summary law, and local cached rebuilding through XT01. A thin
optional adapter may express the partial shape domain if the primary source
mapping calls for it. Two composed nodeRun calls provide a useful resource client;
the scalar and actual-append specializations expose the necessary boundary.

Reuse three existing or small case families: the five-node ordered-duplicate
word fixture with generic/Empty domain boundaries; balancedThree to leftThree
for height and annotation distinctions; and existing chainCache n for actual
callback work. The existing corrupt fixture covers retained-descendant validity.
These are recommendations for consequential connections, not new per-declaration
quotas or independently imposed acceptance gates.

XT01 plus existing measured/ordered-summary interfaces suffices. XT02 shape
bounds, XT03 whole-tree execution, XT04 suffix programs, XT05 traversal-work
sums, and later balancing algorithms are not mathematical prerequisites for this
bounded component. Their requirements, histories and pending gates remain intact.
This component must not become an extra prerequisite for the first Chapter 2
foundation integration. The eventual exact source correspondence and scope are
owned by the parent's freeze and the independent source/API assessments.

No BST/order invariant, AVL/RB/splay correctness, heap-priority preservation,
logarithmic height, traversal-time equivalence, global balancing improvement,
constant physical time, storage sharing or whole-chapter completion follows from
these cases. The height and append-work counterexamples show why those boundaries
matter. All newly proposed laws and examples remain uncompiled proof obligations;
this report supplies no final review or acceptance result.

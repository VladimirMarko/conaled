# Tree rotation: bounded API and architecture preflight

Status: read-only preparation followed by this single authorized report write.
No implementation scope is frozen, no chapter is activated, and no validation or
acceptance is claimed. Inspected project checkout: `conaled-tree-cache`, whose
read-only HEAD lookup returned XT01 commit
`64c6b777d828ecfe83234fc2aed94600a1f24297`. Proposed names below are proposals.

## Recommendation

A small ordinary root-rotation unit on the existing `BinaryTree` is a real
reusable gap. The source explicitly needs the same two local rearrangements in
Chapter 5 rotations, Chapter 9 cached AVL rebuilding, and Chapter 21 splaying.
XT01 is a sufficient project dependency. The shared result should stop at the
operation's legal domain, exact inorder/map laws, a conditional fold law, and
connected applications of the existing cache and measured-node interfaces.

There is no reason to introduce another tree carrier, a rotation syntax, a
balance/BST algorithm, a preservation typeclass, or a whole-tree executor.
Positioned rotations, schedules, listification, rotation distance, balance
invariants and amortized bounds remain their existing chapter obligations.
This unit must not become a Chapter 2 prerequisite.

## 1. Existing interfaces inspected first

The governing guidance was read at `AGENTS.md`,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`,
and ADRs 0001 and 0010. The recommendation follows their separation of
operations, semantic observations, laws and independently justified resource
observations. No modification to the shared proof kernel is needed.

All following project locations are at the XT01 commit above. Mathlib is the
pinned 4.35.0 source recorded by ADR 0001,
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Existing location and declaration | Reuse and boundary |
|---|---|
| `Mathlib/Data/Tree/Basic.lean:31–34`, `BinaryTree.nil`, `BinaryTree.node` | Correct empty-leaf, node-labelled carrier. Constructor order is `node value left right`, unlike the source's left/value/right notation. |
| Same file:79–96, `BinaryTree.map`, `id_map`, `comp_map` | Ordinary label transport; no payload order, equality decision or injectivity is needed. |
| Same file:108–147, `numNodes`, `numLeaves`, `height`, `numLeaves_eq_numNodes_succ` | Reuse the existing size observations. Height is not rotation-invariant. |
| `Applications/Trees/Observations.lean:17–50`, `Trees.fold`, `fold_node`, `fold_map`, `fold_fusion` | Generic fold already exists with independent label and summary universes and explicit empty/combine parameters. Rotation preservation needs a local reassociation equation, not a second fold. |
| Same file:68–105, `Trees.inorder`, `inorder_node`, `inorder_length`, `inorder_map`, map-size/height laws | Main ordered observation. Derive rotation size preservation from inorder equality and `inorder_length`; derive leaf count through the existing node/leaf identity. |
| `Applications/Trees/Cached.lean:15–46`, `erase`, `read`, `smartNode`, `read_smartNode`, `erase_smartNode` | Rebuild exactly the two changed roots while reusing the three fringe subtrees. Erasure is a proof observation, not a required traversal performed by the operation. |
| Same file:49–87, `Valid`, `smartNode_valid_iff`, `read_eq_fold` | Recursive cache validity and correct interpretation of a valid root cache. Correct root contents alone do not establish recursive validity. |
| Same file:89–133, `inorder_erase`, `annotate`, `annotate_valid`, `erase_annotate`, `read_annotate` | Existing ways to construct valid fixtures and compare cache observations with independent folds. Do not implement a local rotation by erasing and reannotating the entire tree. |
| `Applications/Resources/TreeCache.lean:19–78`, `readRun`, `nodeRun`, `nodeRun_value`, `nodeRun_cost`, `nodeRun_le`, `nodeRun_valid` | Actual local reads and callback execution. Each node has callback work plus three declared units. Value correctness and callback cost are separate premises. |
| `Applications/Resources/Measured.lean:13–43`, `Measured`, `bind`, `bind_value`, `bind_assoc`, `bind_erases` | Existing sequential composition; the second computation uses the first computation's actual returned value. No new executor is needed. |
| `Applications/Sequences/OrderedSummary.lean:17–28`, `summary`, `summary_nil`, `summary_append`, `summary_singleton` | An inorder-preserved monoid observation without commutativity. The already written bridge is `TreeCacheExamples.ordered_summary_fold`, `Examples/TreeCache.lean:119–131`. |

The project search found no ordinary `BinaryTree` root rotation or reassociation
operation. The pinned `Mathlib/Data/Tree` modules likewise provide no such
operation. Batteries' searched data modules supplied list rotation, which is
unrelated to this operation.

### Why `Ordnode` is not the missing ordinary operation

Mathlib does contain related operations in
`Mathlib/Data/Ordmap/Invariants.lean:182–228`: `Ordnode.node3L`, `node3R`,
`node4L`, `node4R`, `rotateL` and `rotateR`. They operate on the different
`Ordnode` inductive carrier, declared in `Mathlib/Data/Ordmap/Ordnode.lean:70–77`
with a mandatory natural cached-size field.

In particular, `rotateL` and `rotateR` choose single versus double rearrangement
using `size` and `ratio`; they are not the requested unconditional single root
reassociation. Their missing-child cases construct an unrotated node. Adopting
them here would require a carrier/annotation conversion and import their
weight-balancing choices. That is more machinery than defining the two small
pattern matches on the project's canonical node-labelled carrier. Their
existence is not a reason to reproduce the Ordnode balancing library.

Other existing carriers also remain distinct: `Bracketing.Tree` has labelled
leaves and unlabelled forks (`Applications/Bracketing/Basic.lean:7–15`);
`RandomAccess.Tree` has labelled leaves and size-cached internal nodes
(`Applications/Sequences/RandomAccess/Basic.lean:10–28`); the source leftist
queue has its own priority/rank carrier and a child-swapping smart constructor
(`Applications/Search/LeftistQueue.lean:16–51`). Their observations and
invariants must not be silently replaced by inorder of `BinaryTree`.

## 2. Actual source domains and concrete later clients

The source files below are already retained locally; no new source retrieval
was needed. Their pins and licenses are recorded in the existing Chapter 5,
9 and 21 inventories. Shared Isabelle files are at
`f86f290225eebcc52c1ae7dba2e098f405f51c21`; the inspected splay implementation
is from the saved AFP release dated 2026-10-26.

| Source location | Relevant obligation |
|---|---|
| `book-source/Tree_Rotations.thy:78–82` | `rotR` and `rotL` each supply only the matching two-node shape equation. The unmatched HOL cases are underdefined. This is C05-042–043: exact inorder and the legal inverse, without an order assumption. |
| `book-source/AVL_Set_Code.thy:21–48` | `ht` reads the root annotation; `node` stores `max (ht l) (ht r)+1`. The single-rotation branches of `balL` and `balR` explicitly use two nested smart nodes. The three-node double-rotation branches and balance conditions are additional algorithm obligations. |
| Same file:80–86 | `inorder_balL` and `inorder_balR` specify ordered key observations independently of the cached height fields. |
| `book-source/Splay_Tree.thy:19,29,50–72` | The two single zig cases are the same local rotations; the remaining cases compose larger rearrangements with recursion and comparison premises. A root-rotation unit does not prove the full splay algorithm. |
| `book-source/RBT_Set.thy:52–80` | Red-black balancing also has key-inorder preservation, but recoloring and balance invariants remain specific to that algorithm. Exact inorder of all colored labels is not the relevant invariant. |

### Smallest faithful domain choice

The natural proposed operations are ordinary
`Trees.rotateLeft?` / `Trees.rotateRight? : BinaryTree α → Option (BinaryTree α)`.
For example, left rotation succeeds precisely on
`.node x A (.node y B C)` and returns `.node y (.node x A B) C`; the right
operation reverses that shape. Empty roots and missing pivot children return
`none`. No `Inhabited α`, `DecidableEq α`, order, or new validity record is
needed. Arbitrary payload universes, including an empty payload type, remain
available.

A proof-domain function taking the matching two labels and three subtrees is
also sound if that is all the eventual clients use. Avoid offering both an
Option interface and a second dependent wrapper without a demonstrated caller
need. Identity-on-failure is a chosen totalization, not the source equation,
and would obscure whether an attempted counted rotation actually occurred.

## 3. Minimal semantic laws and proof routes

For each direction, matching-shape/failure equations, inorder preservation on
success, and the opposite rotation's recovery of the original tree form the
useful elementary contract. The inverse claim must be conditional on success;
there is no unconditional total inverse after failure.

Label transport has the ordinary shape
`Option.map (BinaryTree.map f) (rotateLeft? t) = rotateLeft? (t.map f)`.
It requires no injectivity, label equality or shared universe between the old
and new label types. Its proof is just root/pivot cases and `BinaryTree.map`.
Inorder preservation follows from `inorder_node`, `List.append_assoc` and the
cons/append equation. Node and external-leaf counts then follow from the
existing observation laws rather than a new size theory.

A generic fold needs the explicit reassociation equation

```text
combine a x (combine b y c) = combine (combine a x b) y c.
```

For one concrete rotation, only the equation at the three actual fringe-fold
values is required. A universally quantified version is a convenient
sufficient hypothesis for repeated uses. Neither form needs a law about the
empty value, a monoid instance, an order, or a new preservation-family record.
`fold_node` exposes exactly these two expressions. The right-rotation proof
uses the same equation in the reverse direction.

Do not infer this hypothesis from `fold_fusion`: fusion transports an explicitly
lawful summary map, while arbitrary folds can depend on tree shape. For the
existing ordered-summary combine `fun l a r => l * measure a * r`, the equation
follows from `mul_assoc`, and the existing `ordered_summary_fold` gives the
independent inorder bridge. Height does not satisfy the equation.

## 4. Cached-summary consequence, with no new cache framework

On three product-labelled fringes `A`, `B`, `C`, the left-rotated result is

```text
smartNode z combine (smartNode z combine A x B) y C.
```

The old right-associated shape is
`.node (x, oldX) A (.node (y, oldY) B C)`. Both old root annotations are
recomputed; the three fringes are retained. Apply `erase_smartNode` twice to
identify the erased result with the ordinary left rotation. Apply
`smartNode_valid_iff` twice to derive recursive output validity from validity
of the three fringes. That proof needs no associativity of `combine` and no
correctness of the two discarded annotations.

These conclusions must remain distinct:

- The repaired output's cache correctly represents the fold of its **new**
  shape, by `read_eq_fold`.
- Equality with the old tree's stored root additionally needs a valid old tree
  and the fold reassociation equation (or a separately justified preserved
  observation).
- Updating annotations preserves the inorder of **erased labels**. It need not
  preserve the raw list of label/annotation pairs.

The two-node composition is a useful checked client of XT01. It does not
require a new generic cached-tree record. A separate public cache-rotation
adapter is optional; it should only be added if its direct reuse warrants
naming it, not to duplicate the smart-node interface.

## 5. Actual measured composition and conditional cost

The left rebuilding program can use exactly

```text
Resources.bind (nodeRun z combineRun A x B)
  (fun ab => nodeRun z combineRun ab y C).
```

Let `p = read z A`, `q = read z B`, `s = read z C`,
`u = combineRun p x q`, and `v = combineRun u.1 y s`.
The existing definitions and `nodeRun_cost` yield total work
`u.2 + v.2 + 6`. The second callback receives `u.1`, the **actual first returned
annotation**. Replacing that argument by a pure specification before proving
the first callback's reached-value equation would skip a required bridge.

`nodeRun_value` and `nodeRun_valid` already accept value correctness only at
the reached arguments. Apply them successively. Bounds `u.2 ≤ K₁` and
`v.2 ≤ K₂` separately give `K₁ + K₂ + 6`; a uniform bound is sufficient but
not necessary. The unconditional cost formula itself does not need cache
validity or callback value correctness. Right rebuilding has the symmetric
execution: first combine `B,y,C`, then combine `A,x` with that actual result.

The six units are precisely two XT01 smart-node charges, each accounting for
two reads and one entry. There is no additional rotation-entry tick in this
specified composition. If an eventual wrapper charges a root-pattern test or
an outer entry, that would be an explicitly separate tariff. These counts are
not Chapter 5's unit-per-rotation metric, a machine-time theorem, or the
zero-helper convention of the source leftist heap.

### Existing nonconstant callback and concrete composition

Reuse `TreeCacheExamples.appendStepRun`
(`Examples/TreeCache.lean:287–312`), which actually calls
`Resources.ListReversal.appendRun l (a :: r)`. Its existing
`append_node_cost` is `length (read [] left) + 4`, and
`append_node_value` / `append_node_valid` provide the value/validity bridges.

For fringe list-cache lengths `p,q,r`, two successful rebuilt nodes therefore
have the following hand-derived work in that declared model:

| Rebuilding direction | Actual callback work plus local-node work |
|---|---|
| Left: first `A,x,B`, then the returned node with `y,C` | `(p+4) + (p+q+1+4) = 2*p+q+9` |
| Right: first `B,y,C`, then `A,x` with the returned node | `(q+4) + (p+4) = p+q+8` |

The intermediate length must come from the actual append value equation.
Validity connects fringe cache lengths to erased inorder lengths when that
interpretation is desired. These calculations agree with the independent
cases assessment; they are not compiled Lean results. Taking `p=n,q=0` rules
out an unconditional constant-work assertion for arbitrary callbacks. By
contrast, the existing `sizeRun` and `heightRun` callbacks are zero-cost
`Resources.pure` computations (`Examples/TreeCache.lean:225–254`), so their
two-node rebuilding count is six under this tariff.

## 6. Smallest dependencies and useful existing cases

Pure root operations and semantic laws can live in a small
`Applications/Trees/Rotations.lean` importing `Applications.Trees.Observations`.
Cached consequences can use `Applications.Trees.Cached`, and measured clients
can directly import `Applications.Resources.TreeCache`; ordered and append
clients reuse the existing modules above. None needs XT02 shape/logarithms,
XT03 whole-fold execution, XT04 accumulators, or XT05 traversal work. No
additional executor or resource hierarchy is justified by this investigation.

Existing cases avoid inventing unrelated examples:

1. `TreeCacheExamples.balancedThree` and `leftThree`
   (`Examples/TreeCache.lean:150–156`) are already an exact left-rotation pair.
   Their inorder is the same and their heights are two and three. A height
   cache should be repaired correctly, not asserted equal to its previous
   root value.
2. `ordered_summary_fold` and `sample_word` (same file:119–148) give a useful
   noncommutative summary client; multiplication order is retained by inorder.
3. The existing zero-cost size/height callbacks and actual recursive append
   callback distinguish conditional constant local work from arbitrary
   callback work. Existing corrupt-fringe examples (same file:189–216) explain
   why repairing two roots cannot validate an invalid retained descendant.

All public statements should keep label and summary universes independent.
Only an ordered-summary specialization adds a monoid assumption; only a later
BST or balance theorem adds its corresponding order/invariant hypotheses.

## Assessment limit

This is a source/API and mathematical design assessment. No Lean, Lake,
compiler, checker, project hash helper, cache action, ref mutation or remote
write was run. No later chapter scope was removed or discharged. The new
module/name choices and small client surface remain proposals for root to
assess against the other reports before any requirements or implementation
are frozen.

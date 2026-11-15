# Frozen requirements: shared root rotations and cached rebuilding

Local ticket: **FDSA-XT06**. Version 1, frozen 2026-11-02 before source edits.

## Authority, sequence and baseline

The governing whole-book request is `../REQUEST.md`. This bounded unit uses the
user's cross-cutting exception for ordinary rotations shared by Chapters 5, 9
and 21, with further cached-tree consumers. Chapter 1 remains active. Tickets,
commits and review evidence remain local; each created durability checkpoint
is exposed and uploaded. No GitHub write is authorized.

The initial source/review base is saved XT01 candidate
`64c6b777d828ecfe83234fc2aed94600a1f24297`, itself unaccepted and uncompiled.
Planned branch: `work/fdsa-tree-rotations`; worktree: `conaled-tree-rotations`.
The exact clean pre-code state is recorded in `tree-rotation-start.json`.
Only pinned external dependency packages may be linked; project outputs remain
isolated. Source authoring starts only after the pre-code checkpoint is saved.

Accepted repaired Chapter 1 and accepted XT01 are prerequisites to integration
or acceptance. XT02–XT05, XD01, the scalar and probability units are not
dependencies. This unit is not a Chapter 2 prerequisite. Preserve the existing
Chapter 2-first prefix and all other saved histories, requirements and findings.
Any later incorporated accepted base is recorded without erasing this original
base or weakening the scope. Ordinary history-preserving merges retain the
accepted Chapter 1 corrections and any accepted XT01 corrections.

Root owns the sole task-local compiler/checker: the full Chapter 1 guarded run
at `07e480f6ec9958d4975bb90151005b84f2907614`. No additional Lean/Lake compiler,
checker or project hash helper runs for this unit while that gate is active.
Source drafts and mathematical preflights provide no compilation credit.

## Source, architecture and preimplementation evidence

Book: July 27, 2026 edition, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Immediate sources are Chapter 5 pp.67 and 70, Chapter 9 pp.105 and 108–110,
and Chapter 21 pp.245–246. The exact ordinary equations are also in the pinned
`Tree_Rotations.thy`, SHA-256
`745064392da1c3ebc450bdc75ddcdf5b22baa2b135014daee8001d9c09e75eea`, at
Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
That companion revision is not claimed to have generated the manuscript.

Root read all three complete reports, the existing XT01 core and examples,
the original chapter inventory entries, the corresponding primary book passages,
and the pinned rotation/AVL definitions and conditional height laws before
freezing these requirements. The reports retain the wider primary identities,
the later-dated AFP support and exact source/model distinctions.

| Preimplementation report | SHA-256 |
| --- | --- |
| `research/tree-rotation-source-preflight.md` | `f2e2fe9f26273c4629828b44c057481f649301a6a7b6cdae976d807b22953da9` |
| `research/tree-rotation-api-preflight.md` | `d5ec4e3d13e7825350dd065d6fb41a6a0242e56c64db9680ce37ffe0c8a7e4ca` |
| `research/tree-rotation-case-preflight.md` | `f90b49bd35c1779339a0d5b5d2c2de163ccc533bbcb3284fcc35f0f39b6bd02b` |

Reuse the existing Mathlib `BinaryTree`, `Trees.fold`, `Trees.inorder`, map/size
laws, `Trees.Cached` operations and validity, `Resources.TreeCache.nodeRun`,
ordinary `Measured`/`bind`, and the existing ordered-summary and append clients.
The pinned Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`Ordnode.rotateL`/`rotateR` have a different mandatory size-cached carrier and
weight-balancing choices; they are not these ordinary single root operations.
No carrier conversion, new tree algebra record, preservation typeclass, syntax
layer or executor is required. Keep label and summary universes independent.

## XT06-01 — Ordinary partial root operations

Use the existing constructor order `BinaryTree.node label left right` and
Option-valued operations on `BinaryTree alpha`. Proposed names are
`Trees.rotateLeft?` and `Trees.rotateRight?`.

The exact matching equations are:

```text
rotateLeft? (node x A (node y B C)) = some (node y (node x A B) C)
rotateRight? (node y (node x A B) C) = some (node x A (node y B C)).
```

Empty roots and a missing required pivot child return `none`. Expose the
success and exhaustive failure-shape equations. Preserve the source's legal
domain explicitly; identity fallback or an invented missing payload is not
the source operation. No payload order, equality decision, inhabitance or
finiteness assumption is needed. Do not add a second dependent-domain wrapper
without a demonstrated need.

## XT06-02 — Exact semantic and label-transport laws

For both directions, prove that success preserves the complete inorder list
and that the opposite operation returns the original tree. The inverse law
is conditional on successful rotation, not an unconditional inverse on failure.
Derive node-count preservation through existing inorder-length laws and
external-leaf preservation through the existing node/leaf identity.

Prove commutation with every label map, including failure:

```text
Option.map (BinaryTree.map label) (rotateLeft? t)
  = rotateLeft? (t.map label)
```

and its right counterpart. The map may be noninjective and change universes.
Annotation erasure is a specialization, not a new carrier or traversal executed
by the rotation. These map laws are useful derived consequences of the source
equations, not separately printed book theorems.

## XT06-03 — Qualified fold-summary preservation

Expose the precise local reassociation rule. At actual fringe summaries a,b,c,
the required equation is

```text
combine a x (combine b y c) = combine (combine a x b) y c.
```

Supply the matching-shape fold consequence using this equation at the actual
fringe folds, with no condition on the empty value and no monoid/order premise.
A uniform algebra-law corollary for successful optional rotations is allowed
as a useful convenience; it must not replace the weaker reached-value law or
introduce a new algebra record. Do not assume whole-tree fold equality as the
premise that purports to prove it.

Connect an arbitrary existing `[Monoid M]` summary with combine
`l * measure x * r`, in that order. Discharge reassociation with associativity
and use the existing `ordered_summary_fold` bridge to the full inorder
observation. Commutativity is unnecessary. Retain height as the concrete
counterexample to unqualified preservation of an arbitrary fold.

## XT06-04 — Local cache reconstruction

Use two existing smart constructors on three supplied cached fringes. Proposed
small adapters in `Trees.Cached` are `rebuildLeft` and `rebuildRight`:

```text
rebuildLeft z f A x B y C = smartNode z f (smartNode z f A x B) y C
rebuildRight z f A x B y C = smartNode z f A x (smartNode z f B y C).
```

They operate on already exposed matching components. No second Option-valued
cached adapter is required. The three fringe trees are retained and the two
changed annotations are recomputed; erasing and reannotating an entire tree
is not an implementation of this local operation.

Prove erasure correspondence with the ordinary legal rotation and preservation
of erased payload inorder. Prove recursive output validity exactly when the
three fringe caches are valid, using `smartNode_valid_iff`. No associativity or
correctness of discarded old top annotations is required for this repair law.
The result represents the fold of its new shape through `read_eq_fold`.

Keep summary equality separate. A comparison of the two smart-reconstructed
associations may use the local reassociation equation at the reached reads.
Any comparison with an arbitrary input's stored root must also establish the
appropriate old-cache correctness. Height may change while remaining correctly
cached. Updating annotations preserves erased payload inorder; the full list
of payload/annotation pairs need not be equal. Invalid retained descendants
are not repaired by these two constructors.

## XT06-05 — Actual measured two-node composition

Define ordinary compositions of the existing `nodeRun` using `Resources.bind`.
For left rebuilding, execute `nodeRun z callback A x B` first, then pass its
actual returned tree to `nodeRun z callback lower y C`. Right rebuilding first
executes `nodeRun z callback B y C`, then uses that actual tree as the right
child of `nodeRun z callback A x lower`. There is no additional outer entry tick
in this declared composition.

For left rebuilding, set p=`read z A`, q=`read z B`, r=`read z C`,
u=`callback p x q`, v=`callback u.1 y r`. Prove exact work `u.2+v.2+6`.
For right rebuilding use u=`callback q y r`, v=`callback p x u.1` and the
same sum. These unconditional cost laws need neither cache validity nor a
callback-value specification. The second callback must use the first returned
annotation, not an idealized value substituted before its bridge is proved.

Prove value refinement to the pure smart reconstruction using callback-value
equations only at the actual two reached calls. Prove validity separately from
those value contracts and the three fringe-validity premises. Reached bounds
`u.2 <= K1` and `v.2 <= K2` yield `cost <= K1+K2+6`; a common bound gives
`2*K+6` if that corollary is useful. Do not impose a global bound or value law
merely to express these weaker reached-call results.

The six units are two XT01 local-node charges: four root reads and two entries.
Fringe preparation, failed pattern attempts, whole-tree observations in proof
statements, physical allocation and machine arithmetic are outside this count.
It is distinct from Chapter 5's unit-per-rotation metric and source conventions
that charge nonrecursive helpers zero. Preserve those future metrics separately.

## XT06-06 — Connected cases and independent expectations

Use the compact cases below alongside the core. They are consequential uses,
not a per-declaration quota or a new executable test campaign. Each intended
general result must be exercised through its public interface and justified
premises; a standalone closed calculation is not its missing connection.

1. A generic five-node fixture uses singleton fringes labelled q,q,p and pivots
   r,s. Before and after the legal left rotation the inorder is exactly
   `[q,r,q,s,p]`, size is 5 and leaf count is 6. Include the inverse connection,
   a noncommutative word-summary use, and a noninjective map to Unit. Arbitrary
   payload variables preserve the absence of order/decidability assumptions.
2. Cover empty/missing-pivot shapes, including an arbitrary `BinaryTree Empty`
   through the existing empty-tree result, and the two-pivot empty-fringe
   boundary. No positive-size Empty tree or default payload is allowed.
3. Reuse `TreeCacheExamples.balancedThree` and `leftThree`: they are one legal
   left rotation apart, keep size 3 and inorder `[1,1,1]`, and change height
   from 2 to 3. This exposes the failure of arbitrary fold preservation and
   universal height improvement without adding a balance algorithm.
4. On the same fixture, connect valid size/height rebuilding to the general
   cache theorem. Raw rotation of the valid size-annotated product tree moves
   stale tags: new root 1 and lower node 3 instead of their true sizes 3 and 2.
   Smart rebuilding repairs them. The full annotated inorder changes from
   `[(1,1),(1,3),(1,1)]` to `[(1,1),(1,2),(1,3)]`, while erased payload inorder
   stays `[1,1,1]`. Reuse the existing `corrupt` fringe to show that rebuilding
   two roots cannot repair invalid retained descendants.
5. Existing zero-cost `sizeRun` and `heightRun` callbacks give measured work 6
   for the actual two-node composition. The height read may change correctly;
   a valid size read remains the underlying node count. A pair specialization
   is optional and not a separate completion gate.
6. Reuse the actual recursive `appendStepRun`, which calls existing
   `ListReversal.appendRun`. For actual fringe list-cache lengths p,q,r, prove
   left work `2*p+q+9` and right work `p+q+8`. Obtain the intermediate list
   length from the first actual callback's value theorem. These cost equations
   need only the actual cached lists; validity is separately needed to identify
   them with subtree inorders. Singleton fringes yield 12 versus 10, with
   matching erased ordered values.
7. Reuse valid `chainCache n` on the left and empty middle/right fringes:
   exact work is `2*n+9` versus `n+8`, including n=0. Retain an explicit
   any-constant counterexample on this valid family. Two local constructions
   alone do not justify constant work for arbitrary callbacks.

## XT06-07 — Integration, statement review and provenance

Suggested module organization is `Applications/Trees/Rotations.lean`,
`Applications/Trees/CachedRotations.lean`,
`Applications/Resources/TreeRotations.lean`, and small ordinary/cost example
modules. Naming refinements may be recorded without changing this scope.
Domain modules must not import Examples. Ordered-summary and existing fixture
compositions may stay in Examples under ADR 0010. Reuse all prior APIs.

Include every new module in the existing public import closure and exhaustive
proof audit. Add a concise source/statement assessment and reconstruction-map
entry with exact model distinctions, public case connections and pending
validation. Preserve all prior root imports and source correspondences.
No tooling, pins, warning policy or integrity mechanism changes are needed.

Every new/changed claim requires statement review: domains, quantifier order,
minimal and satisfiable premises, label order and multiplicity, correct use of
actual returned values, erasure versus full annotation observations, and cost
boundaries. Preserve each discovered finding and its correction evidence.

## Retained later obligations and acceptance

This unit supports C05-042/043 and common local rearrangements underlying
C09-018–026/038 and C21-005–008. It does not complete their owning chapters.
Legal positioned transformations/schedules, listification, rotation distance
and counts, complete BST/interval-tree operations, AVL/RB tag and balance
algorithms, double-rotation selection, splay recursion and amortized analysis,
and later join/treap/priority contracts remain mandatory in their original
tickets. No inventory is rewritten or marked accepted by this shared draft.

After its prerequisites and compiler exclusivity permit validation, reconcile
the saved history with accepted repaired Chapter 1 and accepted XT01, preserving
all corrections. Validate the immutable clean candidate in the retained
isolated-checkout workflow using the pinned environment: focused core/examples,
applicable full `./check.sh --candidate HEAD`, source/coverage/version checks,
both integrity passes, integrated build and exhaustive axiom audit. Save the
actual success record outside transient outputs.

Both independent Standards and Spec axes must assess this complete frozen
scope on the same candidate, carrying findings across corrections. Preflights
are not final reviews. Immediately before acceptance run
`./check.sh --verify-candidate HEAD` on that approved candidate. Any integration
resolution or later correction requires a new candidate and matching evidence.
Preserve committed progress, local tracking and all evidence in self-contained
checkpoints, and upload each promptly. Until those gates pass, this unit and
all later chapters remain unaccepted.

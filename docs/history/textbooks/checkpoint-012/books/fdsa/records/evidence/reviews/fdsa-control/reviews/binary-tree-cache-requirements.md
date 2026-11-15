# Frozen requirements: shared binary-tree observations and cached folds

Local ticket: **FDSA-XT01**. Version: 1, frozen 2026-11-02 before any
implementation edits in the isolated worktree.

## Authority, dependencies and baseline

The user's task is the complete FDSA book, chapter by chapter, with an explicit
exception for cross-cutting concerns. Tickets and commits remain local; new
durability checkpoints are saved and uploaded. This bounded unit supplies
common mathematics required by interval caches, AVL heights and later tree
observations, while preserving the sequential chapter-acceptance boundary.
Chapter 1 remains active. No chapter is accepted by starting this unit.

Starting commit and fixed initial review base:
`a14977b9e316cc484ffad8a470d26b15615956c0`, the unvalidated Chapter 1 repair.
Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-cache`.
Branch: `work/fdsa-tree-cache`.
`binary-tree-cache-start.json` records the clean index/working tree and exact
head before edits. Only `.lake/packages` is linked to the existing pinned
dependency checkouts; project outputs are not shared. The active old-candidate
gate and its source checkout remain unchanged. No compiler, checker or project
hash helper may be run for this unit while that gate is active.

FDSA-001 acceptance is a prerequisite to integrating or accepting this unit.
If a later accepted integration tip changes the unit's review base, retain
the original base/candidate history, explicitly record the incorporated base,
and carry every finding and requirement forward under the review-loop rules.

## Source and architecture basis

The pinned book is the July 27, 2026 edition, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The immediate common source is Chapter 4, pp. 47–49 and 56–58, especially
the explicit zero/ternary fold and recursive augmentation invariant. Concrete
later uses are Chapter 5's interval maximum, Chapter 9's height caches and
Chapter 15's cached minimum-height mathematics. Their complete algorithms,
ordering/balance conditions and cost bridges remain in their original tickets.

Read and retain these preimplementation reports:

| Report | SHA-256 |
| --- | --- |
| `research/binary-tree-shared-api-preflight.md` | `f20e19c370dec48eccd3a52aa65223012853d75240bfa411b36bad5e5f03bafb` |
| `research/binary-tree-shared-source-preflight.md` | `1ba6a33ae3af2018a843de6ca6b8b5f6daaedca78f4cb5eabb4ae0433451db07` |
| `research/binary-tree-shared-case-preflight.md` | `15964bb73f6ffcfb8ff2ff1792aacb7b2c155d1c73a08fcc37f450f41cc000bd` |

Use the existing Mathlib `BinaryTree` at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. It already provides the matching
empty-leaf/node-labelled carrier, `map`, `numNodes`, `numLeaves`, `height`,
and the node/leaf identity. Preserve those canonical observations. The
existing leaf-labelled Bracketing/RandomAccess trees are distinct carriers.
Reuse conaled's ordinary `Measured`, `bind`, `pure`, `CallCount.tick`,
`ListReversal.appendRun` and `Sequences.OrderedSummary` where specified below.

All applicable AGENTS, architecture/domain, implement, example-driven and
review-loop requirements remain in force. The only nested AGENTS found is
under an unrelated toolkit-authoring experiment and does not govern these paths.

## Exact included scope

### XT01-01 — Ordinary branching fold

Use independent universes for payloads and summary values. Supply an ordinary
operation on `BinaryTree alpha`, with an explicit empty result `z : beta`
and `combine : beta -> alpha -> beta -> beta`:

```text
fold z combine nil = z
fold z combine (node a l r) = combine (fold z combine l) a (fold z combine r).
```

Expose constructor equations, label-map transport, and fusion under precisely
the supplied empty-value and node-operation compatibility equalities. No new
algebra record, carrier/typeclass, monoid, order, equality decision, inhabited
payload or inhabited-summary instance is allowed merely to express this fold.
Prove the natural size and height instances equal the existing `numNodes`
and `height` operations rather than introducing competing size definitions.

### XT01-02 — Inorder and shape compatibility

Define one ordinary node-labelled inorder observation through the fold or
equivalent structural recursion. Its value recurrence is
`inorder l ++ a :: inorder r`, equivalently `inorder l ++ [a] ++ inorder r`.
Prove its length equals `numNodes`, it commutes with arbitrary label maps,
and arbitrary label maps preserve `numNodes`, `numLeaves` and `height`.
Use the existing node/leaf identity for reuse where appropriate.

The label map may be noninjective. Annotation erasure is the existing
`BinaryTree.map Prod.fst`, optionally given a small named adapter. Its
inorder and shape laws are unconditional, including malformed annotations.
No cost identity between differently parenthesized or simplified append
executions is part of these value laws.

### XT01-03 — Cached folds on product labels

Use `BinaryTree (alpha × beta)` directly, with the same explicit z/combine.
The root reader returns z on empty and the stored beta at a node. The smart
constructor retains its supplied children and stores the actual combine of
their root summaries and the supplied payload. Recursive validity requires
validity of both children and equality of the stored annotation to that local
combine, with `True` at empty.

Prove constructor/reader equations, validity of a smart constructor exactly
when both children are valid, unconditional erasure of a smart constructor,
and the central theorem:

```text
Valid z combine t -> read z t = fold z combine (map Prod.fst t).
```

The independent structural fold must occur on the right; correctness may not
be defined by reading the stored result again. No BST ordering, balance,
payload/summary decidable equality, associativity or commutativity is required.
A root-only equation or correct root observation cannot replace all-node
validity. The smart constructor does not repair invalid descendants.

### XT01-04 — Bottom-up annotation as an ordinary fold

Include the concrete ordinary-fold client that annotates an unannotated tree
bottom-up using the cached smart constructor. It must compute the actual
cached tree, with no independent stored-value assumption.
Prove erasure back to the original tree, recursive validity at every node,
and root-summary agreement with the original fold. These are value theorems;
no full-annotation running-time theorem is included in this bounded unit.

### XT01-05 — Explicit local resource interpretation

Use the existing `Resources.Measured` and ordinary sequencing. Name and
document a separate natural-number local-access tariff: each actual root
cache read costs one, and the local smart-constructor entry costs one.
Projections, pair/constructor formation and primitive operations are otherwise
inlined; a supplied measured combine callback contributes its own observation.

The measured constructor must sequence the two actual cache reads, invoke
that callback on their returned summaries and the payload, and store the
callback's actual returned value while retaining both supplied child trees.
It must not recompute a subtree fold or run an erasure/annotation pass.

Prove the reader's value/count equations, the constructor's value refinement
under the callback value equation on the reached arguments, and its exact
count `actualCallbackCost + 3`. A bound `actualCallbackCost <= K` yields
`constructorCost <= K+3`; it may be stated only on the reached arguments.
Validity of the result follows separately from valid children and that value
contract. Cost equations themselves require no cache-validity hypothesis.

This is explicitly distinct from the source leftist selective tariff, which
charges its nonrecursive cached reader and smart constructor zero. It does
not assert physical constant time for unbounded arithmetic, allocation or
arbitrary callbacks. Preserve source observations rather than substituting
one cost model for another.

### XT01-06 — Connected specializations and compositions

Develop the formal cases alongside the core. Independently stated expectations
are retained in the preflight; each meaningful use must exercise the public
operation/theorem that it is intended to check.

1. General size and height cache clients over arbitrary payloads, obtaining
   the canonical observations through the generic validity theorem and fold
   specialization. Height correctness must not assume AVL balance.
2. A pair `(size,height)` summary. Use fold fusion with both projections and
   the one generic pair-cache theorem to recover both observations. Do not
   replace the intended connections with unrelated arithmetic proofs.
3. The asymmetric fixture `node 1 (node 0 nil nil)
   (node 3 (node 2 nil nil) nil)` has size 4, height 3 and inorder `[0,1,2,3]`.
   Its annotated realization must erase back to this tree and meet the generic
   validity contract. Preserve duplicates in a separate map/chain use.
4. Compose the full inorder observation with the existing
   `Sequences.OrderedSummary.summary`. For arbitrary `[Monoid M]`, derive its
   equality with the tree fold using combine `l * measure a * r`, in that
   order. A noncommutative word specialization must expose ordering. No
   commutativity premise is allowed on the generic composition.
5. Retain the boundary that identical inorder need not imply identical
   height, using a balanced three-node tree and a three-node chain with
   matching labels/inorder and respective heights 2 and 3.
6. Use `BinaryTree Empty` and annotation erasure to detect accidental default
   payload assumptions. The only possible tree is empty; its fold returns
   the supplied base, size/height are zero and inorder is empty.
7. Retain the malformed four-node fixture: annotations at labels 1,0,3,2 are
   respectively 4,2,1,1. Root observation and the local root equation both
   agree with size 4, but recursive validity fails. Smart construction over
   those malformed children does not fix them; erasure still preserves
   payloads and shape. The simpler three-node counterexample may be used as
   additional supporting evidence but is not an independent quota.
8. Inlined size/height callbacks with observation zero give local constructor
   cost 3 under the chosen tariff. Their value/cache correctness must connect
   through the public measured and pure contracts.
9. Use the existing actual recursive
   `Resources.ListReversal.appendRun leftSummary (a :: rightSummary)` as a
   list-summary callback. Its public exact theorem gives callback cost
   `leftSummary.length+1`, hence local constructor work
   `leftSummary.length+4`, with the corresponding inorder value. Retain a
   valid repeated-label chain/annotation family with n left nodes to obtain
   local work `n+4`; this rules out a universal constant for arbitrary
   callbacks even on valid caches. This chosen one-append callback is not a
   timing theorem for the source's displayed two-append traversal.

The full abstract composition, not just a fixed arithmetic fixture, is required.
No per-declaration quota or new executable test harness is required.

### XT01-07 — Integration, evidence and provenance

Proposed modules are `Applications/Trees/Observations.lean`,
`Applications/Trees/Cached.lean`, `Applications/Resources/TreeCache.lean`
and `Examples/TreeCache.lean`, with namespace `Trees` for the pure operations
and `Resources.TreeCache` for local observations. Routine naming refinements
may be documented without changing this mathematical scope. Import only
the capabilities actually used. Include every new module in the normal
public root, directly or through its transitive import closure, and in the
exhaustive proof audit.

Update the reconstruction map and a concise source/statement assessment in
`docs/research/`. Record the source distinctions, independent expected cases,
actual public connections, and validation limitations. Preserve every prior
draft and existing API. Every new/changed formal statement needs statement
review for assumptions, quantifier order, semantic meaning and boundary cases.
Any discovered error must retain its identity and correction history.

## Excluded and retained later obligations

This unit excludes a whole-fold measured executor, accumulator/direct-inorder
costs, minimum-height/logarithmic tree structure theory, tree reconstruction
or enumeration, completeness/almost-completeness, balancing, rotations, AVL
algorithms, interval maximum attainment/search, Braun array observations,
binomial/rose carriers, and a general tree executor or language framework.

It also excludes raw maximum-cache Exercise 4.11's representation bridge and
the source-to-existing-leftist-queue adapter. Preserve the latter's current
carrier and all queue theorems; its smart fork can swap children, and its
unconditional content result is permutation, not fixed inorder. No later
chapter or existing priority-queue implementation is replaced by this unit.

These exclusions bound only this shared unit, not the user's whole-book scope.
All corresponding chapter obligations stay mandatory and queued. The book's
ordinary two-append timing associativity/evaluation question remains explicit
in its source plan, without affecting these semantic inorder laws.

## Validation and acceptance

No acceptance is inferred from source preparation or an uncompiled draft.
After the active old-candidate gate exits and Chapter 1's repaired candidate
is accepted, preserve the reviewed integration/base history and validate this
unit's immutable clean candidate in an isolated checkout using the pinned
environment. Finish focused core/examples validation and the applicable
`./check.sh --candidate HEAD` build, source/coverage guards and exhaustive
axiom audit. Retain the success record outside transient outputs.

Both independent Standards and Spec axes must cover this full frozen scope
on the same candidate. Keep the existing review-coordination workflow and
findings; do not substitute preflights for either final axis. Immediately
before acceptance, run `./check.sh --verify-candidate HEAD` on the approved
candidate. Any source correction or integration conflict resolution needs a
new immutable candidate and matching validation/review evidence.

Record all remaining blockers, preserve committed source progress in a
self-contained checkpoint, and upload it promptly. Only after all gates
pass may this shared ticket be accepted. Its acceptance alone does not
close any complete chapter or appendix.

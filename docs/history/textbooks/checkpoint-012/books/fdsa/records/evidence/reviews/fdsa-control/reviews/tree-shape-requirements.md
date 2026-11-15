# Frozen requirements: shared binary-tree shape bounds

Local ticket: **FDSA-XT02**. Version: 1, frozen 2026-11-02 before any
implementation edits in the isolated worktree.

## Authority, dependencies and baseline

The user's task is the complete FDSA book in chapter order, with an explicit
exception for cross-cutting concerns. This bounded unit supplies common shape
mathematics used by Chapters 4, 11 and 15. It does not activate a later chapter,
close an inventory row or change the whole-book scope. Tickets and commits
remain local; self-contained durability checkpoints are saved and uploaded.

Fixed initial review base and starting head:
`64c6b777d828ecfe83234fc2aed94600a1f24297`, the saved but unvalidated XT01
tree-cache draft, itself based on the unvalidated Chapter 1 repair.
Branch: `work/fdsa-tree-shape`.
Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-shape`.
`tree-shape-start.json` records the clean index and working tree before edits.
Only `.lake/packages` is linked to the pinned dependency checkouts; no project
build outputs are shared. The existing old-candidate gate remains unchanged.
No second compiler, checker or project hash helper may run while it is active.

Accepted repaired FDSA-001 and accepted FDSA-XT01 are prerequisites to integrating
or accepting this unit. Later incorporation of an accepted integration base
must retain this original base, candidate history and every requirement or
finding. Matching candidate validation, exhaustive audit, independent Standards
and Spec approval, and immediate candidate verification remain required.

## Source and architecture basis

The book is the July 27, 2026 edition, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The common source is Chapter 4, pp. 47–48 and 51–53. Later uses are the
almost-complete height/optimum consequences for Braun trees in Chapter 11,
pp. 128–130, and minimum-height bounds for leftist spines in Chapter 15,
pp. 183–186. Their representation, invariant, algorithm and runtime obligations
remain with those chapters.

Supporting `Tree.thy` and `Tree_Real.thy` are retained at Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. This mirror postdates the manuscript
and is not asserted to be its build revision. Retain the recorded provenance
and applicable BSD-3-Clause notices when translating proof structure.

The bounded preimplementation reports are:

| Report | SHA-256 |
| --- | --- |
| `research/tree-shape-api-preflight.md` | `1ef2501b2b4aa448122fa859cabe3fb7459f8b5c07e2db6be20e4a93564bbf2c` |
| `research/tree-shape-source-preflight.md` | `c7a69ed3220d94ea333af4974aabf7ed4531368b9323c12867d5d4987a6a47f8` |

Independent hand-calculated client expectations were also supplied before this
freeze and are retained in `research/tree-shape-case-preflight.md`. The exact
case report identity is recorded with the preimplementation handoff. The prior
626-shape calculation is historical evidence and is not repeated or treated
as proof of this unit.

Use Mathlib's existing `BinaryTree` at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, its canonical `numNodes`,
`numLeaves`, `height` and positive-leaf/node-successor identities, XT01's
ordinary fold/map/cache laws, and the pinned `Nat.log`, `Nat.clog` and real-log
bridges. The existing leftist queue and leaf-labelled random-access trees are
distinct carriers; preserve their public interfaces and proofs.

All applicable AGENTS, architecture/domain, implement, example-driven and
review-loop instructions remain in force. Root owns implementation. The core
must not import real analysis merely to establish discrete structural facts.

## Exact included scope

### XT02-01 — Ordinary minimum height and source predicates

For arbitrary `alpha : Type u`, define minimum external-leaf height using the
existing ordinary fold with base zero and combine `min left right + 1`.
Expose its nil/node equations and preservation under every label map, including
noninjective maps. Prove `minHeight t <= t.height`.

Use one recursive Prop-valued complete predicate with source semantics:

```text
Complete nil = True
Complete (node a l r) <-> l.height = r.height AND Complete l AND Complete r.
```

Prove `Complete t <-> minHeight t = t.height`. Define almost completeness by
`t.height <= minHeight t + 1`, and prove its exact equivalence to the source's
natural-subtraction formula `t.height - minHeight t <= 1`. Include the empty
equations, complete-implies-almost-complete, passage of almost completeness
to both immediate children, and map invariance of both predicates.

The predicates concern external-leaf depth. Complete means all such leaves
have one depth; almost complete allows one or two adjacent depths. Neither
means left packing. No payload order, equality decision, finiteness,
nonemptiness, injectivity or `Inhabited` assumption is permitted merely for
these facts. An executable complete checker and the general subtree relation
remain separate Chapter 4 obligations; a Prop predicate alone must not be
reported as completing those requirements.

### XT02-02 — Sharp leaf bounds and completeness

For every tree, prove the natural-number inequalities

```text
2^(minHeight t) <= t.numLeaves <= 2^(t.height).
```

For complete trees, prove equality at both bounds. For every incomplete tree,
prove strict inequality at both bounds. Derive both converse equivalences:

```text
Complete t <-> t.numLeaves = 2^(t.height)
Complete t <-> t.numLeaves = 2^(minHeight t).
```

These are structural induction results, not definitions of completeness in
terms of a desired numerical answer. Preserve the ordinary recursive predicate
and its independent minimum/maximum-height interpretation. Do not weaken
strictness or silently add a nonempty-tree premise.

### XT02-03 — Rounded logarithms and height optimum

Reuse the existing power/log adjunctions to establish universal bounds

```text
minHeight t <= Nat.log 2 t.numLeaves
Nat.clog 2 t.numLeaves <= t.height.
```

For almost-complete trees establish the exact formulas

```text
minHeight t = Nat.log 2 t.numLeaves
t.height = Nat.clog 2 t.numLeaves.
```

Retain the source's height optimum with two independent payload types and
universes and a node-count inequality:

```text
(s : BinaryTree alpha) (t : BinaryTree beta)
AlmostComplete s -> s.numNodes <= t.numNodes -> s.height <= t.height.
```

Only `s` must be almost complete. Do not replace `<=` by equality, require
common labels, infer strict height order from strict size order, or assert a
converse. No existence of a tree of every positive size is asserted uniformly
over an uninhabited payload type. In node-count spelling the logarithm takes
`numNodes + 1`, including the empty tree.

### XT02-04 — Separate real-log source correspondence

In a separate module, prove for every tree the actual real sandwich

```text
(minHeight t : Real) <= Real.logb 2 (t.numLeaves : Real)
Real.logb 2 (t.numLeaves : Real) <= (t.height : Real).
```

Prove both corresponding strict inequalities for incomplete trees and the
real height/log equality for complete trees. Supply the book's natural floor
and ceiling formulas for almost-complete trees by consuming the exact pinned
`Real.natFloor_logb_natCast` and `Real.natCeil_logb_natCast` bridges. Do not
substitute a floating-point approximation or leave the real correspondence
only in prose. Each analytic equivalence must use the actual positive leaf
count and base two greater than one.

The natural floor and ceiling are the nonnegative versions of the printed
source expressions. Nil has one external leaf, both heights zero and real
logarithm zero. There is no need to exclude it or define a new logarithm.

### XT02-05 — Connected uses and consequential boundaries

Develop the following formal cases alongside the core and keep their
independently calculated values. Use the public theorem named by the intended
connection; unrelated reduction of an arithmetic result is not that connection.

1. Empty and singleton boundaries, including an arbitrary `BinaryTree Empty`.
   The empty tree has zero nodes, one external leaf, and both heights/logs zero.
2. A complete three-node tree has four leaves and both heights two. Exercise
   the recursive/equality characterizations and exact complete real formula.
3. A two-node right chain has three leaves, minimum height one and height two.
   It is almost complete and incomplete. Use public strict power bounds and
   rounded-log equalities to show that strict rounded bounds would be false.
   The right-heavy shape also excludes any implicit left-packing requirement.
4. Reuse XT01's actual asymmetric four-node sample: leaves five, minimum height
   two, maximum height three. Derive the natural and real floor/ceiling results
   from its almost completeness, retaining the `numNodes + 1` offset.
5. Compose map invariance with an explicitly noninjective label map and with
   cached annotation erasure. Reuse actual XT01 bottom-up annotation or its
   saved pair-summary sample. Structural invariants do not require valid cached
   values; include the saved malformed annotation as a boundary if useful.
6. Specialize the saved generic cache reader to the minimum-height fold and
   connect it to the ordinary structural observation under recursive validity.
   Obtain an actual annotated sample through the existing `annotate` function;
   add no new measured executor or tariff.
7. A three-node chain has four leaves but is incomplete; being some power of
   two is insufficient. A root with nil left child and a complete three-node
   right child has four nodes, five leaves, minimum height one and height three.
   Compare it with an almost-complete four-node tree through the cross-type
   optimum, and retain that its optimal height does not imply almost
   completeness. At least one use must have genuinely different payload types.
8. Retain the independent seven-node counterexample to recursive sibling-height
   balance implying almost completeness. With `P1 = node () nil nil`,
   `Q = node () nil P1`, `A4 = node () Q P1`, the tree `node () A4 Q` has
   eight leaves, minimum height two and height four, while every sibling-height
   difference is at most one. A local example predicate may express that
   premise; no new AVL implementation or exported balance framework is needed.

## Integration, statement review and limits

Place reusable natural mathematics under `Applications/Trees`, the real bridge
in a separate module, and connected compositions/cases under `Examples`.
Include every new Lean file in the public root's import closure. Record source
correspondence, meaningful use connections, exact domains and boundary cases
in a concise reconstruction note, and add the shared unit to the existing map.

Statement review must inspect quantifiers, universes, leaf versus node counts,
recursive predicate semantics, strict versus rounded bounds, satisfiable
examples, and real casts/rounding. Preserve the original source scope and all
findings. No new axiom, `sorry`, `admit`, unsafe/partial definition,
`native_decide` or skipped kernel checking is permitted.

This unit does not include tree enumeration, a Boolean completeness checker,
the complete/almost-complete constructor exercise, arbitrary subtree machinery,
weight balance or a Braun invariant, array operations, search/order invariants,
a leftist carrier adapter or queue refactor, merge/execution costs, fold-pass
costs, physical storage/sharing claims, or a generic tree/logarithm framework.
Those exclusions delimit shared preparation only; every original book
obligation remains mandatory in its owning chapter or shared follow-up.

No source preflight, hand calculation, draft or focused build counts as
acceptance. Preserve an immutable committed draft and its full local records
in the next durability checkpoint before relying on it as recoverable work.

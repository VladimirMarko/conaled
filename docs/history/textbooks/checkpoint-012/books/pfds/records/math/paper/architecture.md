# PFDS architecture inventory

Inspected repository: `conaled`, baseline
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
Read-only exploration for the chapter-by-chapter PFDS work. No Lean code has
been changed or checked by this exploration, and this is not an acceptance review.

## Rules and design implications

Read `AGENTS.md`, architectural/domain guidance, glossary, ADR 0001/0010,
`docs/research/functional-data-structures.md`, relevant sections of
`data-structure-architecture.md`, all of `data-structure-resource-contracts.md`,
and the language-direction criteria.

Use chapter-indexed tickets and coverage records, but domain-oriented Lean
modules in `Applications/Sequences`, `Applications/Search`, `Applications/Resources`
and checked applications in `Examples`. Reuse `Squares` and `Relational` rather
than defining another book-wide refinement framework. Keep operations,
observations, representation invariants, semantic laws and resource laws distinct.
Avoid requiring a universal container signature from clients with smaller needs.

Representation variation in ordinary Lean is useful but is not interpretation
of arbitrary inductive proofs in other mathematical settings. A new container
may be an ordinary realization without pretending to fulfill that long-term goal.

## Reuse for chapters 1–2

| Obligation | Existing definitions and results | Boundary |
| --- | --- | --- |
| Pure stack/list values | Ordinary `List`, optional `head?`/indexing and standard `List.set`; `Sequences.AbstractFIFO` illustrates operation/law separation, but its `snoc` is FIFO, not stack push | Do not redefine core list semantics; do not disguise FIFO as a stack |
| Append and copied-cell count | `Resources.TreeFlattening.appendWithCost`, `appendWithCost_exact` in `Applications/Resources/TreeFlattening/Core.lean`: result is `(xs ++ ys, xs.length)` | Explicit source-recursion model; not a physical heap/allocation theorem |
| Append visits including terminal nil | `Resources.FIFOContracts.appendRun`, `appendRun_exact` in `Applications/Resources/FIFOContracts.lean`: singleton append result and count `length + 1` | Different primitive convention from copied-cell count; preserve that distinction |
| All suffix values | `DynamicProgramming.suffixRow_length`, `_ne_nil`, `_head`, `_last`, `_entry` in `Applications/DynamicProgramming/SuffixRow.lean` | Uses standard `List.tails.map evaluate`; `_entry` gives `some (evaluate (xs.drop i))` for `i ≤ length`. No sharing/linear-space result |
| Optional list lookup with actual recurrence | `Resources.RandomAccessCosts.fetchListRun`, `_value`, `_count` in `Applications/Resources/RandomAccess/Lookup.lean` | In-range visits are `k + 1`; invalid indexing is `none`, not a default element |
| List-index specification | `RandomAccess.fetch` is an abbreviation for `xs[k]?`, in `Applications/Sequences/RandomAccess/Access.lean`; `fetch_eq_getElem` | No need to construct another indexing meaning |
| Exact representation contracts | `Squares.Rep`, `Square`, `compose`, `Rep.after`, `product`, `pair` in `Squares.lean` | Decoder need not be injective; equality of values gives no equality of cost or physical identity |
| Invariants and optional/relational observations | `Relational.RelRep`, `RelSquare`, `compose`, `product` in `SquareKit/Relations.lean` | Relation may encode `Inv r ∧ decode r = s`; proof witnesses do not imply runtime witness erasure |
| Folded client refinement | `SquareKit.ListFusion.foldl_reachable`, `foldr_reachable`, `scanl_reachable` | Reuse reachable-invariant fusion instead of another full-list induction for each realization |
| Value/resource separation | `Resources.Measured`, `bind`, `bind_erases`, `erasureSquare`, `reweight`, `reweight_bound` in `Applications/Resources/Measured.lean` | Observations may be noncommutative; monotonicity is separate from additivity |
| Actual finite histories | `Resources.run`, `run_append`, `run_state`, `run_invariant`, `run_value_fusion`, `reweight_run` in `Applications/Resources/Workload.lean` | One state trajectory; not an arbitrary branching version graph |
| Resource bound to standard asymptotics | `Resources.isBigO_of_nat_bound` in `Applications/Resources/Growth.lean` | Requires a specified size-indexed family and explicit bound; casts counts into standard `Asymptotics.IsBigO` |
| Fresh-cell persistence | Generic initial declarations of `Applications/Durability/Storage.lean`: `Durability.Heap C := Nat → Option C`, `Extends`, reflexivity/transitivity, `put`, `extends_put` | Generic cell algebra is reusable; later records/roots in the same file are specific to accepted-history durability. Infinite-function heap alone gives no finite capacity/allocation bound |

## Missing chapter-2 realizations

Searches of integrated `Applications`, `SquareKit` and `Examples` found no
generic unbalanced binary-search-tree set or finite-map realization corresponding
to PFDS chapter 2. This is a scoped inspection, not a claim about every dependency
or the archived ADWH source. The integrated `Search.LeftistQueue` is a heap,
not an ordered-search set; `Bracketing.Tree` and `RandomAccess.Tree` have values
at leaves rather than PFDS-style empty-or-keyed-branch BST structure.

Consequently a node-valued unbalanced tree is justified as a distinct realization.
Keep its structural type, ordered invariant, set/map observation and measured
comparison recursion separate. Use only needed order hypotheses. If using
`LinearOrder`, state the restriction clearly. The stronger generality of Std's
comparator interfaces is a separate choice: comparator equivalence must not be
silently turned into Lean equality.

Likely independent semantic specification for sets: membership in the tree's
inorder list, or `Set α` as observation, with ordered invariant. Prove member
correctness, insert membership and invariant preservation, including duplicate
insertion. A finite map needs optional lookup and overwrite semantics separately;
set insertion correctness does not establish map replacement.

Verify actual chapter text before declaring the exact optimization/exercise
inventory. In particular, candidate-based membership, no-copy duplicate
insertion, shared complete trees and pair-based near-balanced construction
must have their source requirements recorded before acceptance. Do not mark
the chapter complete based on the recollected algorithm list.

## Sharing and persistence model

Returning an old subtree in a Lean expression supports an intended sharing
implementation, but extensional datatype equality does not state pointer identity,
fresh allocation, retained space or compiler preservation. To cover chapter-2
sharing claims, use an explicit cell graph/arena with root references:

1. Fresh writes preserve every existing occupied address (reuse `extends_put`).
2. A representation relation decodes a root into the independent list/tree value.
3. The relation is monotone under cell-preserving heap extension.
4. Operations produce a new root while preserving every retained old root.
5. Instrument allocation or graph-size events separately from traversed/decoded
   tree size. Shared complete trees have exponentially large unfolded values
   but only linearly many distinct modeled cells.

Finite backward references are one way to obtain acyclicity and total decoding;
an inductive representation relation on an arbitrary heap is another, with
existence/uniqueness obligations. This is a choice for the implementer, not a
mandated architecture. Either model remains mathematical until connected to a
compiler/runtime/allocator. Do not call abstract cell counts Lean allocations.

`Durability.Chain.mono`, `Array.mono`, `Prefix.mono`, `Represents.mono` and their
uniqueness lemmas are concrete examples of old-root persistence. They concern
ordered durability records and are not a generic lazy evaluation semantics.

## Cross-cutting resource warnings

- Reuse `Resources.run_potential`, `run_potential_exact`, `run_cost_le` and
  `run_constant_charge` in `Applications/Resources/Potential.lean`. Their initial
  and final potential are explicit; the step hypothesis currently ranges over
  all states, so a reachable-only rule needs an invariant subtype or an explicit
  trajectory argument.
- Existing `Examples/FIFOContracts.lean` has a branching counterexample: the same
  valid symmetric queue has credit 12 and two independent deletes cost 18 each;
  36 exceeds `12 + 2*8`. Neither immutable values nor the linear potential theorem
  licenses spending initial potential twice.
- Cost erasure and operation simulation are different obligations. Counts should
  come from actual instrumented recursion, with the returned value used by later
  steps, rather than an unrelated count formula named after the algorithm.
- Counted primitive calls, allocation events, retained live space, asymptotic
  families and measured runtime are different evidence. A graph-space theorem
  must identify retained roots and reachable distinct nodes; summed allocations
  are not automatically peak live space.
- Lazy chapters need suspension identity, shared memoized evaluation and demand
  histories if their original performance statements are to be retained. Existing
  `Measured`/`run` should be reused where possible, but they do not supply that
  evaluation graph themselves.

## Existing later-chapter coverage to revisit at its turn

`Applications/Search/LeftistQueue.lean` already provides keyed leftist heaps:
`Ranked`, `Heap`, `Valid`, `rank_paths`, `rank_size`, `rank_log`, `combineQ`,
`insertQ`, `deleteQ`, invariant preservation, multiset/permutation semantics and
ordered output. This is promising chapter-3 reuse, with source-specific cost
and exercise coverage still to assess.

`Applications/Sequences/RandomAccess/*` and `Applications/Resources/RandomAccess/*`
already provide cached binary-digit random-access lists, canonicality, optional
lookup, totalized `List.set` update, carry/borrow and measured costs. Their
perfect-tree invariant is stronger than shallow cache correctness. Do not trust
older survey language saying their costs remain archived: the current baseline
has the later integrations.

## Completion guidance

For chapter 1, source inventory and precise scope may be the appropriate
deliverable if its statements are introductory rather than new mathematical
claims. Do not manufacture tautological Lean theorems to inflate coverage.
For chapter 2, require exact source-backed semantic, exercise, sharing and cost
coverage, meaningful connected examples, statement review, public import closure,
clean-candidate build/proof audit and independent Standards/Spec review.

Examples should expose empty input, duplicates, invalid indices, old-version
reuse, a skewed tree, branching roots, and equal unfolded values with different
sharing/allocation histories where relevant. Explicitly record which intended
claims remain outside a model rather than relabeling them completed.

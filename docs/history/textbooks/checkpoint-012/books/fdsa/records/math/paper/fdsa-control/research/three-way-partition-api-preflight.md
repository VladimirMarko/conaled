# Shared three-way partition: bounded architecture and API preflight

Prepared 2026-11-02 for root's possible shared Sorting/Selection unit.
**Read-only preparation, not a frozen implementation scope, chapter activation,
compiler result or either independent final review axis.** No source, ref,
worktree, dependency, cache or validation state changed. Only this report was
written. Root retains the sole Chapter 1 compiler/checker run at 07e480f.

## 1. Decision and evidence

The smallest coherent extraction is the existing `partition3` and its seven
independent filter/permutation/membership/length/strict-size facts. Put them in
`Applications/Sequences/Partition.lean`, under `Sequences.Partition`, and retain
every existing `Applications.Selection` name through a same-signature definition
wrapper or theorem adapter. Keep `sorted_partition` and everything following it
in the Selection domain. Add only the useful pure nil/cons value equations
needed to connect an actual one-pass measured realization. No new classifier,
keyed-partition layer, carrier, partition-spec record or two-pass measured
executor is needed for the two identified clients.

This follows the already retained Chapter 2 reuse plan and Chapter 3 proof
plan, rather than replacing either. Neither the initial Chapter 2 foundation
prefix c80eec9 nor the chapter acceptance order changes. Accepted repaired
Chapter 1 is still required before integration/acceptance; the proposed shared
work supplies no acceptance credit for either owning chapter.

I read AGENTS.md, architectural-quality and domain guidance, GLOSSARY.md,
the ADR index and ADRs 0001/0010, the README development/build sections,
fdsa-control/REQUEST.md, the relevant complete partition/selection modules and
their existing examples. I read the relevant portions of the retained Chapter
2 and Chapter 3 plans; their unrelated algorithm proofs were not re-investigated.
The local-ticket/no-GitHub override remains in force.

The inspected Selection and example files in the main checkout are
byte-identical to those in `conaled-ch01-cost-models`, whose saved candidate is
07e480f. The plans retain their own historical input bases; this comparison
does not rewrite them.

| Inspected project input | Bytes / lines | SHA-256 |
| --- | --- | --- |
| `Applications/Selection/ThreeWay.lean` | 10,489 / 226 | `bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52` |
| `Applications/Selection/Rank.lean` | 3,713 / 91 | `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965` |
| `Applications/Selection/Consumers.lean` | 5,450 / 122 | `7ddfe4da069279ac03b075088ce34e32a5ee8c1a251f6b035b45275bafa3167b` |
| `Examples/RankSelection.lean` | 5,085 / 121 | `641a752cdee9b2ab30e66bb2f7feda2548cffebfe6733460b52ff5f7e119520e` |

The retained plans' identities are:

- `chapter02-reuse-plan.md`: 31,586 bytes, SHA-256
  `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a`.
- `selection-proof-plan.md`: 31,813 bytes, SHA-256
  `4683072c5b47f168f81d0f35b727e247bc2c36af6922c76ab8eaac4fb542d18b`.

## 2. Exact extraction boundary

The existing operation first partitions the input by `< p`, then partitions
the first pass's rejected list by `= p`. It returns the existing right-nested
product `List α × List α × List α`, observed with `.1`, `.2.1`, `.2.2`.
Preserve that representation, component order, input order and every occurrence.

| Existing declaration | Shared disposition | Actual dependency/premise |
| --- | --- | --- |
| `partition3` | Move the existing two-`List.partition` body to the shared module; retain the old ordered-domain wrapper | Supplied pivot and finite input list; existing `[LinearOrder α]` signature. |
| `partition3_eq_filters` | Move proof and expose shared theorem; old name becomes a direct adapter | Full strict/equal/greater filter characterization; linear-order laws discharge the complements. |
| `partition3_perm` | Move proof; old direct adapter | Two existing `List.filter_append_perm` uses compose the two partitions. No pivot-membership or distinctness premise. |
| `partition_left_mem` | Move proof; old direct adapter | Membership in input and `x < p`. |
| `partition_equal_mem` | Move proof; old direct adapter | Membership in input and `x = p`. |
| `partition_right_mem` | Move proof; old direct adapter | Membership in input and `p < x`. |
| `partition_lengths` | Move proof; old direct adapter | The three occurrence counts sum to input length, via the permutation law. |
| `partition_strict_sizes` | Move proof; old direct adapter | Retain the substantive `p ∈ xs` premise: it gives a nonempty equal bucket, so both strict buckets are smaller. |

These eight declarations have no dependency on `RankedAt`, `ordered`, the
selector, a pivot policy, fuel, sortedness of input or a resource module.
Their existing code precedes `sorted_partition` in ThreeWay. The original
ordinary operation is not replaced by the proposed measured execution.

Keep the following in their present domain:

- `sorted_partition` uses `ordered`, `ordered_perm`, `ordered_pairwise`,
  sorted-permutation uniqueness and pairwise append reasoning. It is the first
  genuine Sorting/Selection consumer of the partition facts, and should continue
  to import `Applications.Selection.Rank`.
- `dispatch` and `dispatch_value` concern zero-based selection branches and
  optional indexing in the equal block. The source direct-pivot middle-branch
  adapter remains Selection work, rather than a condition on partitioning.
- `PivotValid`, `runWith`, `selectWith`, policy independence and sort/index
  baselines remain Selection interfaces. Their ordinary definitions and public
  one-based versus internal zero-based conventions do not change.
- `RankedAt` and its semantic/rank laws remain in Rank; median and monotone-map
  consumers remain in Consumers. Moving them into a sequence partition module
  would reintroduce the dependency this extraction is intended to remove.

The only explicit unfoldings of the old `partition3` body in the inspected
project source are in the extracted filter and permutation proofs. The remaining
ThreeWay code calls the old operation/fact names without unfolding its body.
Consumers and Examples.RankSelection can therefore remain byte-identical.

## 3. Compatibility mechanism and dependency direction

Retain `Applications.Selection.partition3` as a `def` with its existing argument
order and `[LinearOrder α]` signature, whose body is the shared operation.
An `abbrev` would also give definitional equality, but changing the declaration
kind/reducibility is unnecessary. Retain the seven theorem names with exactly
their existing binder order, statements and premises, proved by the corresponding
shared theorem. The existing declarations carry no simp attribute that needs
to be migrated. Do not add deprecation warnings during this compatibility move.

This preserves the complete current external surface and makes the old/new
value connection definitional. There is no duplicate algorithm implementation
or new hypothesis hidden in the adapter. A separate mandatory family of
identity theorems is unnecessary; a connected example can witness the actual
old/shared interface equality with `rfl`.

The proposed import direction is:

| Module | Direct project dependencies and role |
| --- | --- |
| `Applications/Sequences/Partition.lean` | Only concrete standard-library/Mathlib list and order imports; shared value operation and laws. No Selection, Sorting, Resources or Examples import. |
| `Applications/Selection/ThreeWay.lean` | Existing Rank import plus the new shared partition import; compatibility adapters and unchanged selection-specific remainder. |
| `Applications/Resources/Partition.lean` | Shared partition plus existing `Applications.Resources.CallCount`; actual one-pass source realization, value bridge and declared entry count. |
| `Examples/ThreeWayPartition.lean` or an equivalently small example module | Shared/resource interfaces and Selection only for old-name/consumer compatibility compositions. Existing RankSelection examples stay present. |
| `SquareApplications.lean` | Preserve all imports and add the new examples; their dependency chain includes all new modules. |

Suggested names for the new resource entrypoint are
`Resources.Partition.partitionRun` with its `_value` and `_cost` laws; exact
naming can follow the eventual frozen scope. Its core value theorem should
target `Sequences.Partition.partition3`. Targeting the old Selection name in
the resource module would force a Resources-to-selection-algorithm dependency.
The retained plan's old-name equation remains available by definitional
adaptation after importing ThreeWay, so its mathematical intent is preserved.

The shared core needs no pending ListCalls/insertion/potential/probability/tree
unit. A one-pass program can use `CallCount.tick`, ordinary `Resources.bind`
and `Resources.pure` on the standard triple. No measured callback parameter is
needed merely to reproduce the source's zero-charge comparisons.

## 4. Useful constructor equations, without another pure algorithm

Expose a nil equation returning `([], [], [])` and a cons value equation for
the *existing* shared operation. In mathematical notation, with
`(ls, es, gs) = partition3 p ys`, the cons equation is:

```text
partition3 p (y :: ys) =
  if y < p then (y :: ls, es, gs)
  else if p = y then (ls, y :: es, gs)
  else (ls, es, y :: gs).
```

Use the source orientation `p = y` in the second test. The existing filter
predicate uses `x = p`; equality symmetry supplies that bridge. This equation
can be proved directly from `partition3_eq_filters`, `List.filter_cons`, and
the three linear-order cases. It does not introduce another definition or
assign a traversal count to the two-pass value implementation.

The one-pass measured definition can then recurse once on `ys`, bind its
actual returned triple, and construct the chosen cons triple under one entry
tick. An induction consumes the actual tail-value bridge and the new cons
equation. Its separate count induction obtains `xs.length + 1` from the actual
nil/cons program, with the empty entry included. The exact source tariff and
branch correspondence remain subject to the companion source preflight; this
API plan adds no further counted comparison, append, length or wrapper pass.

Neither value nor cost should require `p ∈ xs`. The membership premise belongs
only to strict decrease on a *whole input* that contains the chosen pivot.
For three-way quicksort partitioning a tail after removing its head pivot,
`List.length_filter_le` and the tail's already smaller length suffice. Reusing
`partition_strict_sizes` there by asserting pivot membership would be false
for a singleton input or a tail without another equal pivot.

## 5. Assumptions and limits of generalization

The two identified book clients have ordered strict/equal/greater buckets, and
the current source semantic API uses `[LinearOrder α]`. Retaining that ordered
API and its current public signature is sufficient for this bounded extraction.
It adds no `Nodup`, `Inhabited`, finite-universe, bottom/top-element, input
sortedness or pivot-membership assumption. A supplied pivot is not a global
inhabitation instance, and duplicate occurrences remain supported.

At the implementation-only level, the two-stage operation, permutation and
length proof can run from decidable `<` and equality tests without linear-order
laws. That observation does not justify advertising the last component as
`p < x` for an arbitrary relation. General two-predicate partitioning already
exists through `List.partition`; neither present client needs a second public
classifier interface. A future concrete keyed or weak-order client may justify
a direct, separately stated generalization. It should not be made a new gate
or silently alter the old wrapper's domain in this unit.

Likewise, the existing `selectWith_map` under a possibly noninjective monotone
map is a theorem about selected rank values. It is not partition transport:
merging keys can move an old strict-bucket occurrence into the equal bucket.
Do not infer a bucketwise map law from it. If such a law becomes useful, retain
the actual predicate-agreement/strict-order/equality conditions it needs.

## 6. Pinned interfaces and import risks

The manifest pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`,
Batteries to `66e469188fe07963e5cf666c7d4433f45b8131c5`, and Lean to
`v4.35.0` / `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The retained Lean Basic/Lemmas source copies were read at the relevant
definitions and independently matched, using ordinary source-blob identities,
to the saved complete source-tree manifest for that Lean commit. They establish:

- `List.partition` is the existing accumulator-and-reversal implementation;
  its semantic interface is `partition_eq_filter_filter`.
- `List.filter_filter` combines its second predicate before its first in the
  resulting Boolean conjunction. The existing partition proof already accounts
  for that exact orientation; keep it when moving the proof.
- `List.filter_congr` requires agreement only on input members.
- `List.mem_filter`, `List.filter_cons` and `List.length_filter_le` supply the
  needed membership, constructor and tail-length interfaces.

The actual current permutation proof already uses `List.filter_append_perm`
twice, followed by `List.Perm.append_left` and transitivity. Reuse that proof
instead of inventing a new permutation argument. A direct remote read of the
pinned Init/Data/List/Perm.lean was unavailable in this run; I do not claim to
have re-read its declaration independently. The explicit existing project use
and later compilation remain the evidence for that particular dependency.

A sensible narrow starting import set is `Mathlib.Data.List.Perm.Basic` plus
`Mathlib.Order.Defs.LinearOrder`. This is a source-level proposal, not a compiled
minimal-import certificate. The former explicitly asserts that `Preorder` does
not already exist; importing it alone cannot supply the ordered bucket API.
The latter provides `LinearOrder` and the order complement facts used by the
existing proof, through its PartialOrder dependency. If a proof tactic needs
a direct small tactic import after extraction, add that import rather than
retaining the whole Selection/Sorting chain or importing the Mathlib root.

| Inspected dependency source | SHA-256 |
| --- | --- |
| Mathlib `Data/List/Perm/Basic.lean` | `73cb327fd595ffec05bc06dc317f339b05824096cb2d68873d4f39d49e96ef71` |
| Mathlib `Order/Defs/LinearOrder.lean` | `80b40cffbc66b648612bd1195941e30e52d8309701d280a23dc2fc48047a9209` |
| Lean `Init/Data/List/Basic.lean` reading copy | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293` |
| Lean `Init/Data/List/Lemmas.lean` reading copy | `9365fb1c6da0313a4c73e8cf096377e69c28ece28d38290a0423e5f8cc1fdfdb` |

## 7. Concrete compatibility and validation obligations

Before implementation, freeze the chosen base, exact extraction/adapter scope,
nil/cons equations, actual one-pass metric and compact cases. Preserve this
report and both earlier plans. No requirement has been frozen by this report.

The later immutable candidate should be checked for these specific risks:

1. All eight old public names still resolve with the same binder order,
   tuple projections, theorem orientation and premises. The operation wrapper
   remains definitionally the original two-stage computation.
2. The seven adapters and the retained `sorted_partition`/dispatcher proofs
   elaborate against the shared core. Rank, Consumers and RankSelection retain
   their source and semantics, including duplicate ranks, policy independence,
   invalid ranks, median indices and noninjective monotone relabeling.
3. The nil/cons value law retains bucket order, duplicate multiplicity and stable
   within-bucket occurrence order, including equality-test orientation.
4. The one-pass value theorem consumes the actual returned tail triple; its
   cost theorem counts that program and does not reinterpret the two-pass
   operation or the separate two-filter quicksort exercise tariff.
5. The shared core and resource module have no Selection/Sorting/Examples
   dependency. The old selection module and the new examples provide the
   compatibility/composition clients instead.

When the sole compiler slot and accepted prerequisites permit, focused targets
include the new core/resource/examples and existing Selection.ThreeWay,
Selection.Consumers and Examples.RankSelection. The unchanged public root,
source/coverage policy, applicable full guarded build, exhaustive audit, both
independent review axes and immediate candidate verification remain required.
No new runtime test campaign or tooling/pin change is implied by this formal
extraction. No such check ran during this preflight.

The bounded proposal resolves the actual dependency risk identified by the
retained plan: future Sorting clients can use partition semantics without
importing the entire selector. Full quicksort3, rank/median algorithms, actual
selection execution, randomness and later cost analyses remain in their owning
chapter scopes. No chapter, appendix or shared unit is accepted here.

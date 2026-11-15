# Frozen requirements: shared three-way partition values and source execution

Local ticket: **FDSA-XQ01**. Version 1, frozen 2026-11-02 before source edits.

## Authority, sequence and baseline

The governing whole-book request is `../REQUEST.md`. This bounded unit uses
the user's cross-cutting exception for the partition operation shared by
Chapter 2's three-way quicksort and Chapter 3's selection, with Appendix B.2's
source count. It implements the shared boundary already proposed in the
retained Chapter 2 reuse and Chapter 3 selection plans. Those original plans,
inventories and the full chapter order remain unchanged.

Original source/review base: repaired Chapter 1 candidate
`07e480f6ec9958d4975bb90151005b84f2907614`, focused-pass but still unaccepted.
Planned branch: `work/fdsa-three-way-partition`; worktree:
`conaled-three-way-partition`. Record the clean pre-code state separately.
Accepted repaired Chapter 1 is required before integration or acceptance.
The initial Chapter 2 foundation prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this unit neither widens that prefix
nor delays it. It does not depend on ListCalls, insertion, tree, potential,
builder, scalar or probability drafts. Preserve original history and carry
any accepted predecessor corrections through later history-preserving merges.

Root owns the sole task-local compiler/checker: the full Chapter 1 gate at
07e480f, session 83124. No other Lean/Lake compiler, checker or project hash
helper may run while it is active. Use only pinned external dependency links;
project outputs remain isolated. Save and upload the frozen clean pre-code
checkpoint before releasing source authoring. Tickets, commits and evidence
remain local; no GitHub mutation. Every created checkpoint is exposed and
uploaded promptly under the user's standing authorization.

## Sources and preimplementation evidence

The manuscript is the July 27, 2026 FDSA PDF, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Exercise 2.3 on p.28 supplies the three-filter value specification. Chapter 3,
pp.34–35 and 40–41, uses partitioning in selection and its time composition.
Appendix B.2 on p.348 supplies the empty/cons timing recurrence and exact count.

The exact one-tail-recursion implementation is the companion
`Selection.partition3_code`, not a separately displayed Chapter 3 code block.
Pinned `Selection.thy` has SHA-256
`c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8` at
Isabelle mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
Its timing command selects those code equations before proving `T_partition3`.
Keep the companion revision distinct from the manuscript version and preserve
applicable source notices/attribution. The primary source, timing and license
identities are retained in the source preflight. Do not include manuscript
copies in the source deliverable or checkpoints.

Root read the three complete preflights, the actual full Selection.ThreeWay
source, Rank/resource interfaces and original relevant inventory/plan passages,
plus the book/companion partition and timing passages before this freeze.

| Preflight | SHA-256 |
| --- | --- |
| `research/three-way-partition-source-preflight.md` | `67dbab76a7b3e27dff569171197496273f86fe6fae3c97a62f6ace6191e50656` |
| `research/three-way-partition-api-preflight.md` | `08d76951855c0fc52ebc9ff6c7a26846a89f33bb2dd35d37f63ea252c9d768e5` |
| `research/three-way-partition-case-preflight.md` | `2837e5dc0cd2255fb668d2bacee0988d4ca312f5dbf12bed0e9aade6b154e72c` |

## XQ01-01 — Extract the existing value owner and preserve compatibility

Place the existing operation and seven independent facts in
`Applications/Sequences/Partition.lean`, namespace `Sequences.Partition`:

`partition3`, `partition3_eq_filters`, `partition3_perm`,
`partition_left_mem`, `partition_equal_mem`, `partition_right_mem`,
`partition_lengths`, and `partition_strict_sizes`.

Keep the existing two-`List.partition` operation body and right-associated
`List α × List α × List α` result, with projections `.1`, `.2.1`, `.2.2`.
The exact specification is the three ordered occurrence filters `< p`, `= p`,
`p < ·`; every bucket retains input order and multiplicity. The concatenation
is a permutation, not generally equality to the original sequence.

Keep the existing universe-polymorphic `[LinearOrder α]` domain. Add no
`Nodup`, `Inhabited`, finite payload, boundedness, sorted-input or pivot-member
premise to general value/filter/permutation/length claims. The strict-size
implication alone retains `p ∈ xs`, sufficient to make both strict buckets
smaller than the full input. Do not turn that sufficient condition into an iff.

In `Applications/Selection/ThreeWay.lean`, retain the old operation as a
same-signature `def` wrapper and all seven theorem names as direct adapters.
Keep argument order, theorem orientation, hypotheses and attributes; add no
deprecation warning or declaration-kind change. Preserve the entire remainder
starting at `sorted_partition` byte-for-byte, and keep Rank, Consumers and
existing RankSelection examples unchanged. Their ordered/rank, indexing,
policy/fuel and one-based public versus zero-based internal contracts remain
Selection work. The shared core must not import Selection, Sorting, Resources
or Examples. Use narrow concrete list/order imports, with only necessary small
tactic imports rather than retaining the old whole-algorithm dependency.

## XQ01-02 — Source value equations of that existing operation

Expose `partition3_nil` and `partition3_cons` (equivalent names are acceptable
if documented). The former returns the empty triple. The latter is a theorem
about the existing operation, not a second pure recursive implementation.
For `(ls,es,gs) = partition3 p ys`, its head step is exactly:

```text
if y < p then (y :: ls, es, gs)
else if p = y then (ls, y :: es, gs)
else (ls, es, y :: gs).
```

The companion's second test is `p = y`; equality symmetry reconciles the
filter predicate `y = p`. Derive these equations through the existing filter
characterization and order laws. An extensional cons equation alone assigns
no one-pass cost to the unchanged two-pass operation.

## XQ01-03 — Actual one-pass measured source realization

Add `Applications/Resources/Partition.lean`, namespace `Resources.Partition`,
with proposed entrypoint `partitionRun`. It imports the shared value core and
existing `Applications.Resources.CallCount`, not the selector. Reuse ordinary
`Measured`, `Resources.bind`, `Resources.pure` and `CallCount.tick`.

The empty program is one tick around the pure empty triple. The cons program
calls itself once on the tail, binds its actual returned triple, applies the
source branch order from XQ01-02 to that triple and adds one entry tick. No
synthetic `(oldValue, length+1)` definition, extra length traversal, second
recursive call, outer wrapper entry, comparison charge, new carrier/executor
or generic classifier/callback framework is required or permitted as a
substitute for this actual source program.

Prove independently:

```text
(partitionRun p xs).1 = Sequences.Partition.partition3 p xs
(partitionRun p xs).2 = xs.length + 1.
```

Expose its empty and cons source equations, including empty cost one and cons
cost equal to the actual tail count plus one. The value induction must consume
the actual returned tail buckets. No pivot membership, distinctness or positive
length belongs to either general contract. The old Selection-name value bridge
is definitional after importing its wrapper; keep that compatibility use in
Examples so the resource module retains the shared dependency direction.

The observation counts every recursive entry, including nil. Primitive
comparison, equality, projection, tuple and cons operations add zero here.
This is not a machine-comparison, allocation, stack, garbage-collection or
physical-runtime theorem. Processing one tail is not tail recursion: the
source reconstructs after the recursive result. The existing two-pass value
implementation has no measured `n+1` theorem from output equality alone.
Exercise 2.4's two charged filters and separate quicksort tariff remain intact.

## XQ01-04 — Compact consequential cases

Use one small Examples module, suggested `Examples/ThreeWayPartition.lean`,
with the following independently fixed expectations and public connections.
These are consequential uses, not a per-declaration quota or new test campaign.

1. Empty input with an explicitly supplied pivot returns the empty triple and
   work one. Generic `replicate n p` returns `([], replicate n p, [])` with
   work `n+1`, including singleton/zero. For positive n, establish membership
   before applying strict-size preservation; never assert `0<0` at n=0.
2. Pivot 2 on `[4,1,2,0,3,2,1,4]` returns
   `([1,0,1],[2,2],[4,3,4])` with work nine. Connect actual values to shared
   filter laws and obtain permutation, lengths 3/2/3 and qualified shrinking
   through their public interfaces. The buckets are not silently sorted.
3. Absent outside pivot 4 on `[3,1,3]` returns `([3,1,3],[],[])`, work four;
   the lower length is unchanged. Absent interior pivot 2 on `[3,1,3,1]`
   returns `([1,1],[],[3,3])`, work five; both strict sides shrink despite
   absence. Keep correctness unconditional and the equal bucket possibly empty.
4. Bind the mixed result at pivot 2 directly to the same actual `partitionRun`
   at pivot 1 on its returned lower list. The continuation receives `[1,0,1]`,
   returns `([0],[1,1],[])`, and the combined count is `9+4=13`. Use the actual
   first-value bridge and ordinary bind; no extra outer tick or new executor.
5. Exercise the old/shared value compatibility and preserve the existing
   selector clients, especially RankSelection's duplicate, invalid-rank,
   policy and median cases. Do not duplicate that entire suite or claim the
   unchanged existing selector now executes the new measured operation.

Do not invent an Empty pivot or force a global inhabitation instance. No keyed
or tagged-record interface is required. A noninjective monotone map can turn
strict comparisons into equalities; existing selected-value map theorems do
not establish bucketwise transport. No such new map law is part of this scope.
Quicksort3's tail argument may lack the removed pivot; tail-size bounds, not a
false tail-membership assertion, provide its later recursion decrease.

## XQ01-05 — Integration, provenance and acceptance

Preserve existing imports and add the new modules to the public/audit closure
through the connected examples. Add a source/statement note and reconstruction
map entry with exact book versus companion correspondence, actual program and
tariff distinctions, old interface compatibility, domains and cases. Record
all source findings and corrections without erasing original evidence.
No tooling, pin, warning policy or integrity mechanism changes are needed.

This unit supplies the shared component of C02-102, existing C03-011/013 facts,
and the new C03-031/B-018/019 realization after its own acceptance gates.
Complete quicksort3, rank/middle-index bridges, selector recursion/termination,
median-of-medians, random policies, whole-algorithm costs and all other chapter
obligations remain mandatory. No chapter is activated or accepted by a draft.

Once prerequisites and compiler exclusivity permit, validate a clean immutable
history-preserving candidate. Focused targets include the new shared/resource/
example modules and existing Selection.ThreeWay, Selection.Consumers and
Examples.RankSelection, addressing the concrete compatibility risk. Then run
the applicable complete `./check.sh --candidate HEAD`, source/coverage/version
checks, both integrity passes, integrated build and exhaustive axiom audit.
Retain matching success evidence outside transient outputs. Both independent
Standards and Spec axes must assess the whole original frozen scope/base on
that candidate, carrying findings through corrections. Immediately before
acceptance run `./check.sh --verify-candidate HEAD`, then save/upload the
acceptance checkpoint. Preflights, authored proofs and focused builds alone
are not acceptance.

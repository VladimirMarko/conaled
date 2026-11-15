# VFA sharing and space: existing models and the insert7 obligation

Read-only investigation, 2026-11-02; proposed checks below are **not new proved
results**. No Lean source, compiler, build, cache, or tracker was changed. This
supplements `RESOURCE-AND-EXECUTION-OBLIGATIONS.md` and leaves chapter acceptance
to the chapter workflow. Paths in the reuse table are relative to `conaled/`;
VFA pointers refer to the pinned `reference/vfa/vfa/` sources.

## Source claims and their separate meanings

`Sort.v:30–34,56–78` computes insertion of 7 into `[1,3,4,8,12,14,18]`, then
describes shared tail cells, four allocations, three cells eligible for GC,
`4X` time and a one-cell net space increase. These require different evidence:

| Observation | Required meaning and scope |
| --- | --- |
| Suffix value equality | The result has the expected tail values; ordinary `List` equality suffices. It neither identifies addresses nor excludes a copy. |
| Physical sharing in a model | Two traversals reach the **same named cell**, whose payload and next pointer are unchanged. Distinct cells with equal payloads remain distinct. A theorem about symbolic addresses still needs a realization argument to describe a running backend. |
| Cumulative allocations | Number of fresh allocation events during the call, regardless of later reachability or collection. Source constructor events are a separate observation unless a realization connects them to allocation events. |
| Retained live nodes | Cardinality of the union of nodes reachable from **all** roots, including client aliases and any temporary roots relevant at that execution point. |
| Net retained nodes | Final minus initial live-node count for specified initial/final root sets. This is neither cumulative allocation nor an automatic bound on intermediate space. |
| Resident allocated nodes | Allocated heap support, including unreachable cells awaiting collection. Require finite support; `Nat → Option Cell` alone does not provide it. |
| Peak live/resident space | Maximum of the corresponding count along an explicitly chosen execution and root schedule. Stack frames, payload objects and allocator metadata require additional observations if included. |
| Garbage eligibility | Allocated and unreachable from the complete root set. This permits deletion under an appropriate preservation theorem; it does not guarantee collection, a collection deadline, or reclaimed physical bytes. |

The literal terminal branch is `i :: h :: t`. Charging each displayed cons
gives **five** constructed cells in this example: new 8, 7, 4, 3, 1. The book's
**four** allocations require reuse of the already matched `h :: t` cell (8),
as in a separately declared implementation returning `i :: l` at that branch.
Those two programs have equal list values; their allocation observations need
not agree. Both share the original `[12,14,18]` under the proposed models.

There are four comparator invocations, at heads 1, 3, 4, 8. Uniform `X` per
invocation is an explicit tariff, not a consequence about unary comparison,
Lean `Nat`, wall-clock time or GC. Likewise `Y` bytes per node needs a chosen
layout, payload representation and pointer width; the source's “2 to 4 words”
is not a layout theorem supplied by conaled.

## Existing declarations inspected and usable scope

| Existing file and exact declarations | Reuse and boundary |
| --- | --- |
| `Applications/Durability/Storage.lean:12–28`: `Durability.Heap`, `Extends`, `Extends.refl`, `Extends.trans`, `put`, `extends_put` | An actual symbolic-address heap already exists. `Extends a b` preserves every allocated cell of `a` in `b`; `extends_put` needs a fresh address. These definitions are generic in cell type and directly fit immutable list nodes. They do not impose finite support or target allocation semantics. |
| Same file `:33–147,201–235`: `Record`, `Cell`, `Root`, `Chain`, `Represents`, `Chain.mono`, `Chain.unique`, `Represents.mono`, `append_rep`, `LinkNeeds`, `RootNeeds`, `KeepsRoot`, `Chain.keep`, `Represents.keep` | Existing pointer reachability and preservation after deletion are real reuse evidence. `Chain` follows `previous` links but observes records in chronological order (`h ++ [e]`); a forward-list decoder must reverse/map that observation. `Root` and `Represents` also include checkpoint/log layout. Directly adapting these is possible, but do not silently equate chronological history with list order or impose the entire history protocol on insertion. Multiple roots require quantifying over a chosen root collection. |
| `Applications/Durability/ResourceEvents.lean:8–75`: `StorageEvent`, `StorageStep.reclaim`, `StorageStep.sound`, `weighted`, `weighted_append`, `reweight_storage`; `DiagnosticStorage.lean:239–295`: `eraseCell`, `ReclaimTrace`, `reclaim_cells`, `ReclaimTrace.sound`, `reclamation_count` | Explicit reclamation of an allocated cell requires `¬RootNeeds` plus the storage protocol's ready/idle/no-pending conditions. `reclaim_cells` requires distinct addresses and proves an actual deletion trace. These are specialized storage transitions, not an ambient Lean GC. The arithmetic/event composition is reusable; a list model must declare its own applicable transition conditions. |
| `Applications/Parallel/PrefixDAG.lean:13–175`: `PrefixDAG.Port`, `Port.run`, `Port.reach`, `Network`, `Network.run`, `Network.reach`, `Network.gates_eq_image_reach`, `Circuit.retained`, `Circuit.work`, `Circuit.compile_gates`, `Circuit.compile_work_le` | Finite topological **named-node** identity, reachability and root-union cardinality already exist. Distinct nodes may denote equal expressions. This is a strong candidate for the finite insert7 sharing witness: encode a cons as a gate with singleton input on the left and a tail port on the right. Appending gates preserves earlier addresses under `Fin.castSucc`. No deletion, allocator, list-heap adequacy or GC schedule is provided. |
| `Applications/Parallel/MeasuredScan.lean:159–257`: `Wire`, `Wire.gates`, `Wire.arrival`, `SharedCircuit.gates`, `SharedCircuit.work` | Counts **structurally equal expressions** as a single shared node. Useful union/cardinality precedent, but alone would merge separately allocated equal cells. The `PrefixDAG` compilation theorem explicitly distinguishes named nodes from structural hash-consing. Neither circuit model claims Lean evaluator sharing. |
| `Applications/Resources/Measured.lean`: `Measured`, `bind`, `bind_erases`, `reweight_bind`, `erasureSquare`, `same_value_different_cost`; `Workload.lean`: `run`, `run_append`, `run_invariant`, `run_value_fusion`, `reweight_run`; `Potential.lean`: `run_potential`, `run_potential_exact` | Compose additive source events and prove erasure into the source algorithm along the actual state trajectory. Comparisons and fresh allocations can be separate counters. Root sets, heap state and live counts belong in the state/invariant; ordinary additive `Nat` accumulation is not a peak-live calculation. Potential theorems retain boundary credit; they do not justify reusing the same credit across persistent branches. |
| `Applications/Resources/TreeFlattening/Core.lean:26–61`: `appendWithCost`, `appendWithCost_exact`, `fromTWithCost`, `fromTWithCost_value`, `copies`, `fromTWithCost_count`; `Thinning.lean:57–77`: `bumpWorkRun`, `thinWorkRun`, `bumpWorkRun_value` | Existing faithful constructor/append instrumentation and value-erasure patterns. Thinning deliberately charges a reconstructed retained head as a cons. These are source counts, not node-identity or GC theorems. |
| `Applications/Circuits/Execution.lean:39–113`: `Circuit.localSpace`, `arena`, `Executes`, `executes`, `Executes.result`, `allocations`, `allocations_sum`, `arena_prefix` | An explicit copied-value arena retains every allocation until tick end, so allocation-prefix sums bound intermediate arena size. Useful precedent for a **declared no-free schedule**, not a theorem that cumulative allocation equals peak live space under arbitrary reclamation. |
| `Applications/Durability/DiagnosticStorage.lean:367–375`: `retainedAfterCopy`, `steadyCheckpoint`, `copy_peak`, `interrupted_space`; `RetentionResources.lean:110–120,220–240`: `bank_live_bound`, `volatileRecords`, `ResourceInv`, `resource_bound` | The first group is arithmetic under a declared coexistence/prior-garbage account, not a general heap-support theorem. The second bounds the specialized two-bank and volatile record slots under phase invariants. Neither transfers automatically to persistent cons lists. |
| `Applications/Linear/StructuredCosts.lean:143–155`: `Plan.retained`, `Plan.workspace`, `eligible`; `Applications/Resources/BoundedSummary.lean:160–210`: `clone`, `clone_eq`, `retained`, `conversionPeak`, `operationPeak`; `Applications/Sequences/ByteBuffer.lean:133–153`: `convert`, `convert_buffer`, `convert_decode`; `Applications/Resources/ByteBuffer.lean:58–77,140–149`: `Events`, `events`, `output_ownership`, `iterative_workspace` | Existing contracts explicitly separate retained/workspace/peak observations from additive work. Byte-buffer extensional copy equality does not prove physical separation; ownership is an adapter obligation. These finite-slot models do not supply arbitrary linked-heap identity. |
| `Applications/Durability/RetentionOwnership.lean:5–65,119–152`: `Handle`, `Ownership`, `Ownership.admits`, `OwnershipStep`, `Owns`, `Exclusive`, `machine_exclusive` | Proof-side affine handles and pinning control reuse of a specialized retained-history service. This is neither Lean value linearity nor a general collector/root registry; do not silently use its single-owner premise for arbitrary persistent client aliases. |

Also inspected `SquareKit/Internal/Graph.lean` (graph of function composition)
and `Applications/Durability/DiagnosticGraph.lean` (`Edges`, `Reach`, `closure`,
`closure_correct`, `Acyclic`: diagnostic graph payloads). A name containing
“graph” is not evidence of a heap/liveness contract. No archived standalone
orbifold source was used.

## Smallest concrete proof target

Prefer a **finite named-node example** over a new universal heap framework.
Use `PrefixDAG.Network` for value, identity and reachable-cardinality checks,
with one explicit encoding: `.one` is the empty tail, `.input x` denotes the
singleton `[x]`, and each new gate appends that singleton to a previously
represented tail. Restrict this example to that cons shape. `Network.run`
with list append gives its value; `Circuit.retained` counts named cons gates
from the chosen roots. List payloads and empty-tail ports are free in this
model. State this interpretation instead of describing the existing circuit
definition itself as a physical linked-list implementation.

Build the old chain tail-first, so addresses 0–6 hold 18,14,12,8,4,3,1 and each
nonempty tail points to an earlier address. The input root is 6. For the
matched-cell-reuse variant, append addresses 7–10 holding 7,4,3,1, with tails
3,7,8,9 respectively; the new root is 10. The proposed checks are:

1. Decode the old root as `[1,3,4,8,12,14,18]` and the new root as the exact
   source insertion result. Check the unchanged old-root value after extension.
   Connect this observation to the actual insertion definition; a standalone
   manually chosen graph without that equality is insufficient.
2. Prove exact named reach sets: old `{0,1,2,3,4,5,6}`, new
   `{0,1,2,3,7,8,9,10}`, intersection `{0,1,2,3}`. This identifies the same
   suffix cells `[8,12,14,18]`, hence the source's smaller `[12,14,18]` suffix.
   Count four fresh appended nodes, not merely four equal values.
3. With only the new root retained, identify `{4,5,6}` as allocated but
   unreachable. With both roots retained, show all eleven nodes reachable.
   A client alias into the old prefix changes this conclusion and must be in
   the root set.
4. Declare a schedule retaining the input root and the current partial-result
   root throughout construction, with no intermediate frees. Check all five
   allocation prefixes: live/resident counts `7,8,9,10,11`. Publication drops
   the old root and temporary roots, leaving eight live nodes. Resident count
   remains eleven until collection; this distinction is part of the result.

For an actual deletion/preservation check, directly reuse `Durability.Heap`,
`put`, `Extends`, `extends_put` with a small local list-cell representation
and a finite support witness, or explicitly adapt `Cell`/`Chain` and reuse
`Chain.keep`. Show deleting exactly the unreachable prefix preserves the
new-root decoder and reduces support from eleven to eight. This additional
step needs no crash protocol, new general graph hierarchy or assumed GC
progress. The named-DAG witness alone establishes eligibility, not deletion.

The literal-constructor variant is a useful connected countercase: append a
new 8 pointing to old address 2, then 7,4,3,1. Both value results agree, but the
proposed accounting differs:

| Chosen realization, same seven-cell input | Reuse matched 8 | Allocate literal 8 |
| --- | ---: | ---: |
| Comparator invocations | 4 | 4 |
| Fresh cells during the call | 4 | 5 |
| Shared original suffix cells | 4 | 3 |
| Unreachable old cells after retaining only the result root | 3 | 4 |
| Result-root live cells | 8 | 8 |
| Both-root live cells / no-free resident peak | 11 | 12 |
| Resident cells after deleting precisely the unreachable cells | 8 | 8 |
| Net live increase after dropping the old root | 1 | 1 |

These are proposed model-specific equalities to check, not measured backend
results. If a later chapter claims bytes or a compiler's actual sharing, keep
the layout/realization obligation explicit rather than treating this example
as a compiler-correctness proof.

## Later persistence and composition

`SearchTree.v:90–100` states that insertion preserves the old tree. Preserve
that value-level claim independently of address sharing. A later pointer
realization can reuse immutable extension and explicit roots, with path-copy
allocation counts and unchanged-subtree identities; none is proved by the
ordinary tree equality alone. `ADT.v:112–129,251–266` wraps persistent function
or tree updates, so old table handles may remain client roots. Its “sharing
constraint” at `:618–624` is module-definition identity and has no GC meaning.

For sequential measured insertion/sorting, reuse `Resources.bind`/`run` and
their erasure laws for additive events, and carry heap/root observations in
the state. A later peak theorem must inspect that trajectory, rather than
sum per-operation net changes. These findings justify a small declared list
realization where needed; they do not justify building a new generic memory
framework, advancing later data-structure implementations, or closing Sort.

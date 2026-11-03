# Disjoint-set connectivity reconstruction (#158)

`Connectivity` connects the textbook's list and weighted-parent-array
implementations to the same finite partition. The query and cycle-rejection
consumers agree even when the implementations choose different representatives.
Successful request histories retain the source's distinct-component premises.
Repeated requests and invalid vertices have explicit executable outcomes.

## Interface and representations

`Observation.lean` defines `partition` using Mathlib's `Relation.EqvGen` and
`Setoid` on the subtype of vertices in a `Finset`. Edges are the original
requested vertex pairs. `Connected` requires both endpoints to belong to the
finite universe. `observe` returns `none` for an invalid endpoint and otherwise
returns its connectivity Boolean. This mathematical specification is
noncomputable; the list and array queries are executable.

`Requests.lean` separates the `Ops` record (`find`, `union`) from `QueryLaws`.
The laws state the find domain and its common-representative interpretation.
`QueryLaws.query_eq` derives exact agreement with `observe`. The shared `request`
uses both find results from its own implementation. It returns `missingVertex`,
`alreadyConnected`, `unionFailed`, or `merged state`. `unionFailed` remains
observable on arbitrary malformed representations; it is not mislabeled as an
invalid vertex. `request_merged_iff` recovers the successful distinct-name call
premise exactly.

`Realizations.lean` supplies `arrayOps` and `listOps`, and proves their query laws
from actual source histories. `sourceConnected_iff` identifies the retained
source closure with the Mathlib partition. `joint_request` extends a successful
synchronized history from actual executable results. `joint_request_realized`
constructs the list step from a successful array step, using the list's own
find results. `array_request_success_iff` characterizes reachable successful
merges by valid, disconnected endpoints.

The concrete representation proof modules retain useful source mathematics:

| Module | Representation-specific responsibility |
|---|---|
| `ListPartition` | Source filter/head find, first-name union, partition invariant and list merge proofs. |
| `ParentArray` | One-based partial reads/writes, bounded parent chase, source size-directed union and finite root paths. |
| `ParentForest` | Dimensions, valid parents and increasing cached sizes imply complete find on valid vertices. |
| `ParentComponents`, `ParentUnion` | Independent components and the effect of linking distinct roots; invariant preservation. |
| `ParentHistory`, `ParentCounts` | Actual successful requests, reachable invariants and logical component counts. |
| `ParentConnectivity`, `Refinement` | Original-edge connectivity and synchronized list/array histories. |

The list keeps its first name. The array chooses the larger cached component,
keeping the first name on a tie. Losing-root cache entries can remain stale;
the proofs preserve the source's distinction between those entries and exact
root sizes. `ComponentRefines` compares components and requires the list's
partition invariant. It does not equate representative names or state arrays.

The shared library has no pre-existing disjoint-set realization. Mathlib's
finite sets, setoids and equivalence closure supply the semantic foundation;
Lean's lists and arrays supply storage. The source's independent `RootSteps`
and concrete list partition proofs are retained to establish the actual
executors' laws. The source closure is kept behind the proved
`sourceConnected_iff` bridge so its existing induction proofs remain useful.

## Two consumers and composition

`querySquare` relates the pair of concrete queries to the independent
observation of the original request log. `rejectCycleSquare` maps that
observation to the edge-retention decision. `retainEdgeSquare` is their actual
`Relational.compose`; `joint_retainEdge` consumes its preservation theorem.
`QueryLaws.retain_iff` states the decision contract: an edge is retained exactly
when both endpoints exist and are disconnected. This is the connectivity
component of a cycle-rejecting forest builder. No minimum-spanning-tree or
complete forest-construction theorem is asserted.

## Provenance and retained scope

The immutable source is
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md).
All ten members of the actual `DisjointSetsArrayRefinement` import closure were
verified against the preserved SHA-256 manifest before adaptation. The
[declaration ledger](adwh-connectivity-provenance.tsv) records snapshot,
archive-relative member, member hash, original declaration, visibility,
destination and disposition for 404 explicitly named definitions, abbreviations,
structures, inductives and theorems: 301 adapted, 5 reused and 98 deferred. Private names
use their source spelling, not Lean's generated private-name prefix. Anonymous
instances, examples and generated constructor/proof declarations are not
separate ledger rows; the exhaustive project audit includes their compiled
mathematical declarations.

The nine retained source modules are relocated by mathematical responsibility.
Their operations and theorem assumptions are preserved. Five identical helper
proofs are consolidated in public `ListPartition` lemmas for head membership,
block symmetry, singleton initialization, edge monotonicity and empty-edge
connectivity; the array/refinement modules use those results directly. Event traces and
associated observed-execution cost bounds (`DisjointSetsArrayTrace` and the
trace-facing part of `DisjointSetsArrayForest`) remain reference. Removed
historical diagnostic declarations remain available in the snapshot; the new
public examples exercise the selected interfaces. Other disjoint-set variants,
random-access implementations, client cost models and graph algorithms remain
outside this slice. Root, block and successful-request counts are logical
cardinalities. No physical mutation, allocation-cost, amortized-complexity or
runtime claim follows from this reconstruction.

## Checked cases and statement review

The initial case used requests `(2,3), (1,2)` on four vertices. A worked
calculation gives array representative 2 and list representative 1 for the
same component, with vertex 4 isolated. The raw operations compute these
states, but initially lacked the connection to the new Mathlib observation,
shared request outcomes and composed consumer. The realization proofs supply
those missing connections. `Examples.Connectivity` retains these applications:

| Case | Public result and expected mathematics |
|---|---|
| `before_history`, `different_representatives` | `joint_request`, `jointHistory_refines`: equal partitions despite representatives 2 and 1. |
| `own_find_arguments`, `after_history`, `own_find_realization` | A third request `(2,4)` uses array union arguments `(2,4)` and list arguments `(1,4)`; direct list union `(2,4)` fails. The public realization theorem constructs the matching successful step. |
| `one_three_connected`, `query_after_history` | Independent edge/transitivity evidence establishes connectivity; `joint_queries` derives both executable answers. |
| `retain_before_merge`, `retained_endpoints_disconnected` | The composed square transfers the array's computed retain decision to the independent specification and list consumer; `retain_iff` exposes disconnected endpoints. |
| `already_connected`, `cycle_rejected` | Query laws and `no_joint_extension_of_already` reject `(1,3)` without extending the successful-only history. |
| `invalid_vertices` | Both failed array finds are equal for 0 and 5, while public query laws yield `none` and request laws yield `missingVertex`. |
| `logical_counts` | `jointHistory_counts` gives one component after three successful requests on four vertices. |

Statement review covers all new claims and retained statement families.
The semantic partition is on valid vertices; ambient invalid reflexivity is
excluded. Generic operations use separate state, vertex and representative
types. Query laws constrain only find observations; they do not silently assume
union correctness. Concrete laws are proved from reachable histories, and
successful-union existence retains those hypotheses. Raw union operations keep
the source's behavior on same-name arguments; the request wrapper checks that
case first. `JointHistory` continues to contain successful merges only.
Relational squares preserve observational agreement and never require equality
of the chosen names. The new examples establish their premises through actual
operations or independent original-edge reasoning.

Targeted validation: `direnv exec . lake build Examples.Connectivity` passes.
`SquareApplications.lean` imports the examples and their entire implementation
closure. Fresh full compilation, exhaustive axiom audit and independent reviews
are performed by the coordinating integration run.

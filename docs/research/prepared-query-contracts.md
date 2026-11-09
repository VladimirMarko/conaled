# Prepared queries and phase requirements

Ownership update: #193 is closed and supplies completed measured-execution
evidence. Historical assignments to #193 below are not an active work queue;
use the [current residual-owner map](workstream-status-reconciliation.md) for
new resource, runtime and error-comparison work.

`Applications/Resources/Prepared.lean` separates operations, semantics,
resource interpretations and application requirements. It adds phase bounds to
the existing measured execution and finite optimization interfaces (#305).
`Examples/PreparedQueries.lean` contains direct callers.

A caller supplies `Ops S Q A R`, an independent `f : S → Q → A`, and a
relation `Valid : S → R → Prop`. `Laws` proves that preparation establishes
validity and every query from valid state answers `f`. Preparation receives
only `S`. The query type `Q` is unavailable until operation. Lean's total
functions require terminating preparation even when `Requirements.startup`
is `none`. A genuinely offline interface instead receives `S × List Q` at
preparation and may use the entire future word.

`Profile S` separates preparation work, worst-case query work, maintenance
work, retained cells and peak cells. `Bounds` connects the work fields to
measured executions and the storage fields to a declared backend `Storage`.
`response_deadline` combines those bounds with `Feasible`. The maintenance
field becomes an operational guarantee only with a `Maintenance` witness;
`maintenance_deadline` requires that witness. Immutable compositions do not
provide a maintenance operation. Their zero maintenance profile is not a
promise that arbitrary updates cost zero.

These costs count declared primitive events. They do not certify wall-clock
latency, allocation in generated Lean code, or fixed-width encoding of
mathematical naturals. A physical realization needs an interpretation of
primitive work and storage, index capacity, scheduling and interference.
The existing byte-buffer realization supplies a precedent: its byte payloads,
finite counters and scalar references are separate observations.

## Reuse and composition

The inspected implementations supply these reusable laws:

| Existing implementation | Reuse and boundary |
|---|---|
| `Incremental.Stateful` | Valid initialization, repair and retained intermediate states; no resource guarantee follows from validity alone. |
| `Arithmetic.Staging` | Static inputs are separate from runtime inputs; the existing unavailable-runtime-variable theorem remains a checked case. |
| `Resources.Measured` and `Workload` | `bind` adds sequential work; workload composition retains state. `Prepared` uses the same measured pairs and bind. |
| `Resources.Potential` | Total or amortized bounds; they do not imply individual deadlines. The checked `[0,10]` counterexample has average five and a response of ten. |
| Bounded summaries and byte buffers | Exact scans, conversion, capacity rejection, cache validity and storage observations; the new summary client reuses those proofs. |
| `Optimization.Thinning` and scan search | Executable finite argmin and catalog-relative minimality, with feasibility filtering before selection. |
| `ParserWorkload` | Separate setup/query work and explicit lifetime accounting. Its exact semantic scope remains broader than its measured fragment. #309 owns its prepared-query specialization. |

`comp` prepares two realizations from the same static source and retains both
states. Queries run sequentially and the second consumes the first's answer.
`comp_bounds` adds work, retains both representations, and includes a proved
bound on intermediate answer cells during the second stage. The peak formula
is the maximum of two simultaneous-live-storage sums. It does not infer
parallel latency or add two unrelated peaks. The arithmetic caller proves
both stages feasible individually and rejects their composition at the same
deadline.

Static conversion uses `Reduction`, which measures conversion and retains
translation state. It also measures query encoding and answer decoding.
Its semantic law transfers agreement; its work theorems retain the converted
static input in the backend's size-indexed profile. The expanded-RMQ caller
converts a two-cell source into four cells, accounts for four writes plus
backend preparation, and adds both query translations. `Reduction.Arena`
observes converted inputs, retained translator state, and actual encoded
queries and backend answers. `Reduction.CapacityLaws` requires bounds on
those values and translation stages. `Reduction.bounds` combines these
premises with backend `Bounds` to certify the reduced operations themselves.
The storage schedule retains the converted input during backend preparation,
the encoded query during backend answering, and the backend answer during
decoding. Its maximum ranges over a finite query domain; this particular
storage construction requires `Fintype Q`. Core operations, semantics and
work composition do not require finite queries. An infinite query domain,
such as an unrestricted parser request type, needs a different uniform storage
interpretation before applying this storage construction.

The expanded caller proves the component premises: zero translator cells,
four converted cells, one encoded-query cell, and one answer cell. Conversion
holds its two source cells and four output cells simultaneously. Backend
preparation overlaps the four converted cells with its ten-cell peak, giving
a conservative fourteen-cell arena bound. The checked caller derives full
`Bounds`, including eight retained cells and five query steps, then establishes
feasibility for those requirements. The standalone `reductionPeak` arithmetic
helper is not itself a certificate for an operation.

## Concrete realizations

`PreparedSummary` adapts both existing bounded-buffer representations.
Preparation of the cached form uses `BoundedSummary.convert`, including its
copy, scan and cache write. Both maintenance operations preserve validity,
including overflow as a specified no-op. The checked stale-cache example
shows why changing the buffer without repairing its cache is invalid.
Unsupported changes require rebuilding. Capacity-zero and capacity-one
examples exercise empty queries, singletons, saturation and maintenance.
Peak storage reuses the existing conversion overlap and recursive-scanner
frame bounds. The resulting bound is conservative; it retains both copied
representations during conversion.

`PreparedRMQ` is a bounded sparse-table baseline, with arbitrary ordered
values in four input cells. The ten query constructors enumerate all
nonempty inclusive intervals. Preparation materializes rows of lengths four,
three and one. Row zero retains the source vector; each later cell performs
two reads, a minimum comparison and a write. The four cells cost sixteen
primitive operations. Queries read one stored answer, or read two overlapping
pairs and compare them for a length-three interval. The `overlap` proof uses
idempotence; this is not a valid transformation for arbitrary associative
operations such as addition.

The independent `rangeMin` specification scans an inclusive interval;
`rangeMin_le` and `le_rangeMin` characterize its minimum independently of
the table representation. #306 consumes this generic specification for its
larger sparse/block construction. The baseline is not a scalable sparse-table
implementation or the full LCA algorithm. An ordered lexicographic
(depth,index) value can express leftmost argmin; the small examples here
observe minimum values.

Table storage counts the four source cells, three pair cells and one whole
interval cell. Two scratch values give the declared ten-cell peak; counters
and control registers are outside this cell observation. Direct queries
retain four cells and use two scratch values. Abstract ordered cells need
not have fixed byte width.

The catalog has exactly direct and sparse candidates, each with its own
representation type and semantic law. `selected` reuses `argmin_correct` to
prove feasibility and minimality. `selected_agreement` retains each
candidate's semantic witness. Examples cover no feasible candidate, zero
queries, repeated queries, a deadline excluding the lower objective,
workload-dependent choice and storage-dependent choice. The objective in
these examples is preparation plus the worst-case query bound times the
query count; it is explicitly an upper-bound objective for unknown future
queries. Catalog minimality does not establish global strategy synthesis.

## Statement review and remaining scope

The semantic quantifiers cover every runtime query from any related state,
not only prepared states. Preparation establishes a usable state for every
static input. Maintenance relates the repaired representation to the new
source. Deadline proofs bound individual operations; repeated-query sums
are separate. Sparse correctness ranges over arbitrary ordered values,
including ties, and all admitted intervals. There is no nonempty RMQ query
on an empty domain; empty summary queries remain meaningful and checked.

The initial failed cases exposed missing phase/resource connections to
existing summary laws, then the missing sparse-table overlap identity.
The retained cases call the public laws and bounds rather than inspecting
proof syntax. Ordinary Lean clients retain their previous interfaces.

No preservation-family interface changed. The new resource contract does
not claim transport to arbitrary mathematical settings, so no demonstrated
#235 mismatch needs a separate issue. #306 owns arbitrary-size LCA/RMQ and
its target witness; #309 owns parser policies and their catalog. Physical
WCET and scheduling remain under the existing reactive/resource owners
#193/#234. Dynamic rebuild scheduling, universal index discovery and offline
strategy synthesis remain deferred; these bounded clients do not yet justify
another framework issue.

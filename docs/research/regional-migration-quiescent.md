# Quiescent regional repartitioning

This first stage of [#487](https://github.com/VladimirMarko/conaled/issues/487)
changes actual fused, split and checked regional plans while preserving their
joint continuation. The mandatory pending-work/shared-dependency extension is
described in [regional-migration-pending.md](regional-migration-pending.md).
This quiescent client remains a separate richer-input case; its results alone do
not establish transfer of pending effects or internal fork/join messages.

## State and ownership

`Regional.Reconfiguration.transfer` reconstructs each target's nested state from
the two current logical delay cells. It never replays the seed. Fused and split
plans use the distinct executors delivered by #485; the checked plan additionally
runs the existing redundant encode/decode boundary. The placement-only control
retains the original delay/redundant suffix theorem.

Preparation keeps the old executor authoritative and freezes business ticks.
The prepared target carries erased semantic/resource evidence; it cannot execute
until ownership commit. Failure and cancellation retain the old continuation.
The same source relation covers arbitrary valid states, suffixes and repeated
transfers. An unequal-state example rejects swapping the two delays.

Every attempted preparation consumes a Boolean permission, including allocation,
validation, stale-source and capacity failures. Commit/cancel and other controls
do not restore it. A completed ordinary modeled tick restores it. This prevents
repeated successful or failed attempts between business ticks. Progress still
requires scheduling enabled business work and a cooperating sink; an infinite
external stream of control commands is not a fairness assumption.

## Policy and certificates

The policy path reuses #486's actual candidate inspection, context/epoch
validation and ranking. It proposes a target, then runs migration-specific
admission. Passing target steady-state selection alone does not authorize a
transfer: source identity, permission, preparation state and transition capacity
are checked separately. The target's semantic and storage certificate is tied
to its actual plan. The implementation does not adopt a #489/#490 frontend or
certificate architecture.

## Resource and execution boundary

The logical copied-value model reserves eight scalar control/tag/plan-index
cells. Old state remains live while two logical bits are copied and the new
representation is allocated; the conversion buffer is then released. Successful
preparation stores exactly the target in `TransferRuns`. Admission checks that
trace and both steady executors. Tick allocation uses the existing actual
`Plan.SpaceRuns` witness, including regional adapters and copies. Commit frees
the old representation; cancellation frees the prepared representation.

The event bill counts modeled checks, copied/allocated/released cells, actual
regional execution work and output observations. A check is one model operation,
not one CPU instruction. Policy traversal uses #486's finer operation bill.
These are explicit logical resource units, not physical Lean heap bytes or a
verified host allocator. The public byte adapter uses a fixed finite catalog and
fixed capacity constants. General API workloads/evidence have their own charged
sizes and are not claimed to fit a uniform public-adapter buffer bound.

The public adapter streams business output before installing the tick's next
local state and then writes control status. Write/flush exceptions abort the
process without replay. A partial write can be externally effective even when
local installation did not finish; no atomic external publication, acknowledgment
or crash recovery is inferred. A query/control-write failure is not evidence of
failure during business publication.

## Retained checks and remaining scope

The independent two-site fixture produces `11,01,10` and final state `01`.
Transfers after a nonempty prefix preserve it across fused/split/checked cuts.
Other checks exercise unequal state, frozen ticks, stale source, insufficient
migration capacity despite target eligibility, allocation/validation failure,
cancellation, policy proposal and permission exhaustion.

The pending stage will use #480's stable bounded peer, two slots, owned event
queue, explicit delivered confirmation and retirement contract. It must add a
real shared producer with two consumers, retained intermediate values and
consumer-delivery state across changed cuts. Its response observation differs
from the delay-only source, so it needs its own source/protocol relation and must
publish the actual joined payload. Quiescent success does not discharge any of
those obligations.

## Local adapter measurements

The [raw round trips](regional-migration-measurements.json) contain 42 command
observations from three repetitions of ordinary and repartitioning schedules.
The ordinary schedule substitutes two queries for each prepare/commit pair;
both schedules execute the same three business inputs. Process startup is
excluded. Preparation, including conversion and validation, ranged from
122,088 to 260,516 ns; commit ranged from 8,289 to 19,696 ns. These include local
pipe and dispatch overhead on this host and are not deadlines or speedups.
Conversion is included in the preparation timing, not independently timed.
The checked logical preparation bill is 12 operations/cells, including four
copied cells; injected validation failure bills 14 because the target is also
released. The transfer peak for the fixture is 14 logical cells; the admitted
whole capacity additionally covers both steady executors.

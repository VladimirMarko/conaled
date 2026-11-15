# Executed dynamic front-array policies

Issue #508 implements the selected R4 contracts under #459. Literal and eager
resizing share concrete storage operations and existing resource execution.
Their logical outputs agree under layout; their storage histories and costs can
differ. This does not adopt a general storage or allocator architecture.

## Sources and native ownership

The inspected checkpoint-233 archive has SHA256
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Its `project/adwh-lean/ADWH/Chapter02/DynamicArray.lean` member has SHA256
`a8f9e0bbb49d31a5cc8f4e19dd7fba339d32c5fd0ac52300b3030b8bd0789469`;
`DynamicArrayEager.lean` has SHA256
`d708457628cb6a1fe7d344f14397e15b887568888942c395147138a19c4bfcb4`.
Both inspected files match the archive bytes. Historical proofs were not
replayed. Their exercise/answer attribution is evidence to reconcile with the
printed book under #149, not independent verification of the book or licensing.

The [#476 design investigation](design-challenges/2026-11-11/dynamic-arrays/synthesis.md)
identified snapshot copy, raw-state potential bounds and the positive-spare
hypothesis. This implementation tests its bounded local-policy proposal.
Checkpoint names do not dictate module ownership or theorem statements.

[DynamicFrontArrays](../../Applications/Resources/DynamicFrontArrays.lean)
contains actual total array updates and the two insertion boundaries.
`Resources.run` owns repeated execution; `Measured` owns sequencing and
reweighting. Existing free-monoid observations retain event order.
[DynamicFrontArrayCosts](../../Applications/Resources/DynamicFrontArrayCosts.lean)
packages additive prices for `reweight_run` and uses `run_constant_charge` for
both potential bounds. No new workload executor or telescope is introduced.
[DynamicFrontArrayGrowth](../../Applications/Resources/DynamicFrontArrayGrowth.lean)
derives the eager capacity and geometric schedule from actual execution.

Fixed-capacity ByteBuffer, finite-index Dijkstra Store and their resource clients
retain their original interfaces. They supply useful bounded storage and cost
results; they do not already implement these raw resize policies.

## Recovered contract disposition

| Recovered declarations | Native disposition |
| --- | --- |
| Literal Event/State/Layout, copy/grow/write/add operations and their trace, size, layout, value and in-bounds laws | Retained in DynamicFrontArrays, with total raw domains and the additional arbitrary-old-window theorem. |
| Both adds executors and workload layout/value laws | Replaced recursive workload owners with wrappers over Resources.run; retained exact equations and logical refinement. Literal capacity monotonicity and workload in-bounds results remain. |
| Both adds_metered, potential/allocation laws and initial-price bounds | Retained through native reweighting and potential telescoping, including all raw-state domains and setup cost. |
| Eager spare/density/balance/capacity-growth laws | Retained with their original distinct hypotheses; added raw literal capacity-growth accounting using the same event projection. |
| Eager geometricExtras and printed_total_cost | Retained finite extra-charge identity and renamed the execution-linked result total_work_power_interval to avoid presenting unverified printed attribution as authority. |
| Both recursive stepCosts and short price schedules | Replaced by bills over retained insertion blocks; bills_sum connects them to complete execution. The literal_bills/eager_bills examples retain both schedules. |
| Distinct initial capacity and concrete storage examples | Connected examples and runtime full-state/event fixtures retain their observable conclusions. |

This accounts for all 58 named literal and 40 named eager declarations in the
inspected source, with shared storage and potential names retained only once.
The source's anonymous small examples are covered by complete native fixtures.
The source definitions were useful here, but neither a second generic executor
nor historical naming was needed to preserve their mathematics.

## Storage and observations

Raw states contain an array of optional payloads and an unconstrained natural
free cursor. `Layout s xs` separately requires positive capacity and an empty
prefix of length free followed by the payload list. Consequently malformed
cursors and zero capacity remain executable, while logical list refinement and
in-bounds conclusions state their layout hypotheses explicitly.

`copyInto` consumes a fixed snapshot list, writes increasing indices with
`Array.setIfInBounds`, and records every attempted copy including out-of-bounds
indices and none payloads. It does not read a changing source array.
`copyInto_layout` preserves arbitrary surrounding prefix and suffix around a
blank destination window. `copyInto_window` strengthens this to arbitrary old
window contents of the same length, on the same operation.

Growth allocates twice the capacity, copies the occupied suffix starting at
old capacity plus old free, and retains that sum as the new free cursor.
WriteFront uses natural truncated decrement and attempts the indexed write.
Literal insertion grows at free=0; eager insertion grows at free≤1.
Layout-preserving workloads decode to inputs.reverse ++ initialValues.

Events carry allocation size, copy index/optional payload and write index/value.
An allocation of zero slots still records an event. Work counts copy/write
attempts; allocation counts allocated slots; growth counts allocation events.
These are source-model tariffs. They do not measure native array allocation,
conversion, proof evaluation, allocator failure, ownership or machine time.

`grouped` wraps the same insertion operation and existing workload executor to
retain one block per insertion. Its flattening theorem equates the complete
state and ordered flattened events with ordinary execution. `bills` maps a
price over these retained blocks. Grouping is not reconstructed from an already
flattened trace, and no second policy state algorithm is used.

`execute_metered` covers every natural-valued list price with empty/append laws.
It packages precisely those laws as an additive homomorphism and applies native
reweighting. This exact identity does not promise a uniform amortized constant
for all tariffs; index- or value-sensitive prices may grow arbitrarily. The
ordered trace remains available independently of commutative price projections.

## Potential and growth statement review

Both policies prove their one-step inequalities on all raw states, using
potential = capacity - 2*free with natural subtraction. Work plus final potential
is at most initial potential plus 3; allocation plus twice final potential is at
most twice initial potential plus 4. Native telescoping gives the workload
bounds with both endpoints and arbitrary initial states. Empty-state
specializations follow from zero initial potential; fixed allocation prices
include the one-slot setup cost explicitly.

Eager positive-spare and balance theorems require layout and initially positive
free space. A valid full singleton lacks that premise and is a checked negative
control: its insertion preserves layout but leaves free=0. Its balance equation
without the premise is false. Capacity-growth accounting retains its broader
raw-state domain, including zero capacity and non-power initial capacities.

The eager finite extra-charge sequence sums 2^(k+1)-1. Its exact identity and
capacity bounds yield a power-interval characterization of every nonempty
insertion workload. This scalar recurrence describes observed resize extras;
it does not replace value-producing execution. The argument uses natural power
arithmetic and the execution-derived balance, not a new generic geometric-sum
framework. Empty workloads are handled separately.

## Connected examples and validation

The [examples](../../Examples/DynamicFrontArrays.lean) connect public refinement,
full observation, potential and growth theorems with concrete clients and
negative controls. Complete expected states and event blocks were frozen before
generic implementation. The standard empty state has one none slot and free=1;
the raw zero-capacity control is different.

| Insertions | Policy | Work | Allocated slots | Growths | Capacity | Free |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| [1,2,3] | Literal | 6 | 6 | 2 | 4 | 1 |
| [1,2,3] | Eager | 4 | 6 | 2 | 4 | 1 |
| [1,2,3,4] | Literal | 7 | 6 | 2 | 4 | 0 |
| [1,2,3,4] | Eager | 8 | 14 | 3 | 8 | 4 |

Neither policy is uniformly cheaper. Eager work bills begin
[1,2,1,4,1,1,1,8,1], while literal bills begin [1,2,3,1,5,1,1,1,9].
The [runtime driver](../../scripts/DynamicFrontArraysTest.lean) checks complete
states and ordered event blocks, projection totals, independent reverse-list
values, copy windows, attempted out-of-bounds writes, empty commands, malformed
cursors, zero capacity, repeated values and non-power capacity.

A deliberate wrong-policy runtime control substitutes literal insertion for
eager insertion. The frozen complete-state/event test rejects it at the eager
fixture. This is a postimplementation discrimination check, not a claim that a
behavioral red preceded implementation. Expected observations were frozen first.

Development and acceptance evidence belongs to the immutable candidate handoff.
Focused private compilation reuses copied dependencies from the exact accepted
base. It does not replace the coordinator's guarded integrated build,
exhaustive proof audit and independent Standards/Spec review. No physical
performance or backend claim is made.

This delivery accounts for the selected R4 policy contracts only when those
acceptance gates pass. Demand/sharing and delayed insertion remain separate
#459 obligations; whole-book coverage and attribution remain #149.

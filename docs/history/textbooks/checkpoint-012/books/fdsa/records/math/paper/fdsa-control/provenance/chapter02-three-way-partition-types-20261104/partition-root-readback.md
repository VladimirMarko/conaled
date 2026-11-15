# XQ01 source and elaborated-statement readback

Recorded 4 November 2026 by root, after the actual successful combined type
inspection at immutable development candidate
4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9. This is the coordinator's statement
assessment, not either final independent review axis or unit acceptance.

All 48 intended declarations were read in the explicit-universe/explicit-argument
output: ten shared value declarations, seven measured declarations, 23 connected
example declarations and eight preserved Selection wrappers. Root also read the
complete corresponding shared core, measured core, example sources and wrapper
prefix, including proof bodies. The input inventory and exact output section
are retained alongside this record. The inspected full output contains 49,149
bytes, SHA256 e11516d6b42a939c886b90aa08b71e3d3f9f558a98f94906767a60ac949c45c4.
The overall 84-declaration command returned exit0 in 14.876180347s, clean
unchanged source. Its full 91,292-byte log has SHA256
c05a5e5a0098492721b81c689383d421a24ec3d6bf2b00a7629ae18be5ad8d99.

## Shared values and preserved interfaces

`partition3` has arbitrary universe-polymorphic payload α with the intended
LinearOrder instance, an actual supplied pivot and an arbitrary list. There is
no hidden finiteness, global inhabitance, duplicate-free or pivot-membership
premise. Its ordinary two-stage List.partition definition remains separate
from the measured one-pass source realization.

`partition3_eq_filters` gives precisely strict-less, equal and strict-greater
filters of the original list. Filter order and duplicate occurrences are kept.
`partition3_perm` preserves the full list permutation after grouping buckets;
it does not assert that grouping retains the original cross-bucket order.
The three membership equivalences retain original membership and exactly the
proper comparison/equality condition. `partition_lengths` sums all three bucket
lengths with no occurrence loss. `partition_strict_sizes` alone adds pivot
membership; its proof uses a nonempty equal bucket. The nil and cons equations
retain all three branches and the returned tail buckets.

The eight legacy `Applications.Selection` declarations have the same intended
signatures and predicates under the same LinearOrder assumption. Their source
wrappers consume the new shared operation/theorems. The elaborated output's
longer derived-order projection paths do not introduce extra hypotheses.
The remaining Selection algorithm is outside these wrapper changes and its
previous exact-byte preservation/compatibility checks remain retained.

## Actual measured execution and count

`partitionRun`, its nil and cons equations, value bridge and three cost laws
keep actual `Resources.bind`, `Resources.pure` and `CallCount.tick`. The source
recurses once on the tail, uses the actual returned triple, then prepends the
head to its selected bucket. The nil count is one. The cons count is the actual
tail count plus one; induction yields length plus one independently of values.
No cost law is inferred from the equality to the ordinary two-stage partition.
No comparison, tuple/projection/cons charge, machine-time or stack theorem is
silently added to this declared entry-count tariff.

## Every connected client

`replicate_partition`, `replicate_run` and `singleton_run` retain every equal
occurrence, including zero length for the family and count n+1. Only
`replicate_strict` requires n>0 to justify pivot membership and strict decrease.
`selection_partition` and `measured_selection_value` bridge the exact legacy
operation. `empty_run` retains the final empty invocation.

`mixed`, `mixed_partition`, `mixed_run`, `mixed_value`, `mixed_cost`, `mixed_perm`,
`mixed_lengths` and `mixed_strict` refer to the same eight-element fixture.
The ordered buckets are [1,0,1], [2,2], [4,3,4], with lengths 3/2/3, full
permutation, strict sides and count nine. The conclusions distinguish bucket
order from sorting and preserve repeated values.

`outside_partition`, `outside_run`, and `outside_boundary` use pivot4 on
[3,1,3]. The unchanged lower side has length3 and refutes unconditional strict
shrinking; the count is four. `interior_partition`, `interior_run` and
`interior_boundary` use absent pivot2 on [3,1,3,1]: both strict sides shrink,
the equal bucket is empty, and the count is five. Thus pivot membership is a
sufficient premise for the shared strict-size theorem, not an asserted
necessary condition. `lower_partition` supplies the ordered [0]/[1,1]/[] result
for pivot1 on the mixed example's actual lower bucket.

`bind_returned_lower` applies the second partition to the actual first returned
lower bucket, not the original input or an unrelated fixture. The public value
and count laws establish the result [0]/[1,1]/[] and total nine plus four equals
thirteen; ordinary measured bind adds no wrapper entry.

All fixed expectations and satisfiable arbitrary-parameter uses match the
prepared scope. Every statement has the intended quantifiers, universe,
comparison orientation, full occurrence observation and resource boundary.
No concrete source/type mismatch was found. The source proofs and checked types
preserve XQ-ELAB-001/002's bounded repairs; all earlier actual failures remain.

## Remaining gates

The complete frozen XQ01 unit scope, independent Standards/Spec reviews on the
final integrated candidate, full immutable check/audit, matching verification
record and immediate candidate verification remain pending. The combined type
check and this readback close no ticket or coverage row by themselves. The
first outstanding acceptance remains unchanged foundation f17cc6b.

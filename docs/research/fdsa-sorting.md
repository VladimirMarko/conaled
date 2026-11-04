# FDSA Chapter 2: sorting correspondence and resource models

This note maps every section, displayed definition and supporting claim, named
result and exercise in Chapter 2 of *Functional Data Structures and Algorithms:
A Proof Assistant Approach* to conaled source. The complete inventory contains
**112 obligations**: the original C02-001–107 and the five explicit operational
clarifications C02-108–112 of the existing natural-sort requirement. Chapter
headings organize this correspondence; the Lean modules remain organized by
sorting, resources, sequences and probability.

**Source correspondence.** The table records the implemented definitions,
claims and connected examples; it does not certify an integration candidate.
The initial combined source was `f673ee87195e4aaeef4b41767a7468c70ad6214f`
(M2), followed by the preserving corrections recorded in the local evidence.

**Development validation — 4 November 2026.** At development source
`4b5dbfa07288acc73f25c27838d3fb2f78e77d71`, both independent reviewers
completed the full source assessments and all 815 current printed-type
assessments. Their complete accounting retained 920 qualified historical
public names and 28 accepted-base public names, totaling 1,763 explicit public
names. These are historical results for that development candidate; they do
not establish the later integration candidate's validation or acceptance.
Earlier failed checks and the full correction history remain preserved.

**Accepted predecessor history — 4 November 2026.** Chapter 1 was accepted at
`07e480f6ec9958d4975bb90151005b84f2907614` and the shared foundation at
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`. Chapter 2 integration follows the
independently recorded acceptance of every included shared prerequisite in the
required order. Historical type evidence requires matching receiving inputs;
the complete immutable-candidate gates below remain mandatory.

## Source identity and correspondence

The pinned book is the July 27, 2026 edition, Chapter 2 printed pages 13–29
(PDF pages 19–35). Its SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The [author-maintained source](https://fdsa-book.net/) and
[official PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf)
identify the manuscript. The companion `Sorting.thy` was inspected at Isabelle
mirror commit `f86f290225eebcc52c1ae7dba2e098f405f51c21`, file SHA-256
`dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
The natural merge-sort correspondence also uses the dated AFP
Efficient-Mergesort archive of 2026-10-26, SHA-256
`148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708`.
These are source/proof references; they are not Lean axioms or evidence of an
Isabelle rebuild. The manuscript and extracted prose remain research inputs.

Lean/Lake 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` supply the standard libraries.
The development retains the qualified native execution profile and all proof
and validation restrictions; only the Nix requirement is waived. This note
adds no theorem framework, probability carrier, resource executor or root-level
assumption.

The source lineage includes the uniform-input pair from
`9d5dcd2cfbd6fc5df572234a85bf4957d0c32a21` (U), the growth pair from
`08a1e78d6becc713256d245206ef163f9eb55a0a` (G), and rank correction
`a111774b7b393cf462029fec8d16e8b6ff1b0089`. That rank correction supplies
explicit parentheses around intended indexed arguments in seven source
headers; `6f3e010eb3b0a55fe8005c26deefacf2eed10cfc` adds four preserving
proof conversions. Conditional-tail core correction
`fa86bfb800c1e70cdf61fefd75b8cb2f428daea6` is followed by boundary-proof
correction `ee2ea2406a014e43c355f93317455f27b90dd680`. Natural-operation
example corrections `b87e4e05d89d774a3e217d0fafd271bee4a9cd9a` and
`47f66dccc414d41bddf0dc6576a2338227ee221e`, and numerical mean correction
`e0df28b7bbfa722b25623606a5a1905620fac91e`, retain their stated observations.

Uniform-input correction `aa89aeccf7e06cd046b4f3c5c430631d4ea73b5b` names
the original measure and the rank/sum/cast applications explicitly. Twelve
scoped omissions remove irrelevant section instances, and the intended pairwise
disjoint-event relation is written explicitly. The actual algorithm, conditional
mean route, occurrence transport and connected examples are retained; matching
successor elaboration and statement inspection remain required.

Focused attempt 5 at `c0440a99c2a503b7816a44367f7e4168378dbbf1` (C) and
attempt 6 at M2 both closed with exit 1. Attempt 6 individually built the
conditional-tail core and numerical mean core/examples; its natural-operation
examples, conditional-tail boundary examples, rank core and uniform-input core
reported failures. Dependent targets reported as `Ran` are not successful
builds. The original logs and later corrections remain separate evidence.
These source identities and individual results do not establish complete
candidate validation or acceptance.

## Sorting, keys and the chosen stable exercise

Ordinary correctness is pairwise sortedness together with `List.Perm`.
`Multiset.coe_eq_coe` supplies the multiset reading, retaining every repeated
occurrence. Membership/support and length are separate consequences. The
always-empty list illustrates why sortedness alone is insufficient. Generic
operations use decidable comparisons; their sortedness theorems retain
relation-specific or input-local laws. A `LinearOrder` on keys supplies the
book specialization without imposing an order on payloads.

`Applications.Sorting.KeySorted`, `Stable` and `StableSort` keep three
observations separate: sorted mapped keys, full-record permutation and equality
of each filtered equal-key subsequence. Ordinary output uniqueness reuses
`List.Perm.eq_of_pairwise'` under antisymmetry. The generic chapter corollaries
are `UQ.sorters_eq_at`, `UQ.sorters_eq` and `UQ.sorters_eq_of_multiset`.
The displayed premises (2.33)–(2.34) belong to that proof; they do not introduce
two additional public theorem requirements. Totality and antisymmetry have
different roles, especially for records with equal keys.

**Exercise 2.7 selects the source floor-left top-down sorter.** It splits at
`length / 2` using contiguous `take`/`drop`, then uses the non-strict left-tie
merge. `TD.sortFloorOn_correct`, `TD.sortFloorOn_stable` and
`TD.sortFloorOn_spec` preserve all records and the order of equal-key payloads.
`ETD.payload_expected_spec`, `ETD.stable_across_split` and
`ETD.signed_record_value` are connected clients. Alternating piles and reversed
bottom-up passes retain their own ordinary-correctness and instability cases.
Their output correctness does not supply this stable-sort contract.

## Resource observations and their domains

Every cost theorem names an actual measured execution or an explicit
observation-preserving transport. Equality of sorted outputs alone does not
identify costs. The shared `Resources.Measured`/call/list interfaces are reused.

| Source construction | Declared observation and principal domain |
| --- | --- |
| Insertion | Function entries, including the terminal branch, with insertion applied to the actual recursively sorted tail. Global bounds are `2*n+1 ≤ T ≤ (n+1)*(n+2)/2`; sorted input attains the lower bound and `reverse (range n)` attains the upper bound. The source's weaker `(n+1)^2` result remains explicit. |
| Ordinary merge | Actual selected-branch head comparisons C; the separate entry observation E satisfies E=C+1. C is zero when either list is empty, and C≤left length+right length needs no sortedness premise. |
| Floor-left top-down sort | Comparisons on actual sorted child values, with zero cost at sizes 0/1. The source power-of-two theorem retains `n=2^k` and yields `k*2^k`; its real-log corollary retains that same premise. All-length ceiling-log and genuine Big-O results are additional contracts. |
| Ordinary/reversed bottom-up | Pass comparisons are bounded by total flattened length, including ragged and empty inner runs. Repeated merging has bound total length times `Nat.clog 2` of the run count. Uniform-length/power-of-two theorems retain their own hypotheses; per-pass equality does not assert equality of whole differently ordered merge trees. |
| Natural comparison count | Actual scanning uses `n-1` comparisons with truncated Nat subtraction; worker tails use their actual lengths. Merge comparisons act on the returned runs. The printed upper bound `n+n*ceil(log₂ n)` and the stronger adaptive intermediate bounds remain separate. Sorted nonempty input has one run, zero merge comparisons and exact best comparison count `n-1`; sizes 0/1 cost zero. |
| Quicksort exercise tariff T | Empty cost 1. Each length-m filter costs `2*m+1`, including the unit predicate tariff. A nonempty size-n node has local toll `4*n-1`; singleton T=5. The global bound is `2*n²+2*n+1`, attained by the source's sorted/all-right families, including equal keys. Append traversal is outside T. |
| Literal quicksort F | The existing execution also charges both actual right-associated appends. With A the append observation, F=T+A and T≤F≤2T. Empty F=1 and singleton F=8. The extra local append tariff is left-result length+3. Neither T nor F charges sampler implementation, pivot lookup/indexing/removal, random bits or payload-map evaluation. |
| Ordinary list building | Repeated singleton append from empty has subcost `n*(n+1)/2`; loop/wrapper entries have separate formulas. Cons followed by the verified accumulator reverse preserves order with full declared work `2*n+3`. This is a comparison of the named constructions. |
| Difference-list closures | Creating a composition has constant local capture work independent of stored callback application costs. Materialization has an explicit finite construction/application model, with separate `Rep` and `AppCost` contracts. Extensional `D` alone is not an application-cost bound. |
| Natural operational scanner | `NRO.runsOpsBy_work_le` gives scanner work≤`6*n+1` for all inputs. Arbitrary ascending workers require `AppCost f k` and have bound `k+6*m+5`; descending workers have bound `6*m+5`, where m is the remaining tail length. Actual zero/single-run final dispatch has work≤`6*n+2` only on the stated run-count≤1 domain. Its exact empty/singleton work is 2/4; sorted size n≥2 gives `6*n-4`; a nonempty strict descending chain gives `3*n+1`. |

The operational scanner count includes branch/entry work, callback creation and
application, descending cons construction, emitted-run construction and the
actual final zero/one-run dispatch. It is distinct from the printed comparison
counter. No all-input operational merge tariff, machine runtime, allocation,
garbage collection, compiler sharing or random-bit complexity follows from
these abstract observations. The examples retain arbitrary lawful builders,
nonempty seeds/suffixes, repeated materialization and histories with empty
represented output but growing application work.

## Two actual quicksort expectation experiments

C02-024 retains both assertions even though their analyses are omitted from the
book's main exposition. Each has its own execution and probability bridge.

| Experiment | Actual sample and observation | Source connection |
| --- | --- | --- |
| Uniform input, deterministic first pivot | Sample one uniform permutation of the input's occurrence labels, map those occurrences to the original payloads, and evaluate the existing deterministic `QC.exerciseCost`. | `UM.occurrenceInput`, `UM.occurrenceInput_cost`, `UM.inputMeanBy`, `UM.inputMean` and `UM.integrable_inputCost`. |
| Fixed input, fresh random pivot | Execute `RP.run`; every nonempty call chooses a fresh uniform valid occurrence index, erases that occurrence, performs the measured filters and recursively binds those actual children. Integrate its actual Nat exercise marginal. | `RP.uniformIndex`, `RP.run`, `RP.exerciseLaw`, `RM.exerciseMean`, `RM.exerciseLaw_integrable`, `RM.exerciseMean_cons`. |

For the uniform-input proof, `PO.restrictedOrder` and the conditional-tail
interfaces retain the same sampled environment. `UM.left_filter_on_first` and
`UM.right_filter_on_first` identify the actual child filters on the revealed-head
event. `UM.integrable_observedCost` and `UM.integrable_observedCost_cond` justify
the original and conditional real integrals. `UM.child_integral_cond` transports
each actual child marginal; `UM.conditional_mean` adds their expectations
without assuming a joint independence law. The valid disjoint head events give
`UM.meanBy_recurrence`. Cardinal induction and actual selected-key rank then
give `UM.meanBy_eq_closedForm`.

The generic label result requires key injectivity only on the selected finite
set, `Set.InjOn key S`; collisions outside S remain allowed. Its complete finite
position list supplies the finite probability environment. The arbitrary-input
wrapper uses `Fin xs.length` occurrence labels and
`hkeys : (xs.map key).Nodup`, so it adds no finite, equality, inhabited or
measurable-space instance on the payload type. Its varying-length family theorem
is `UM.inputMean_family_isBigO`. The sample is taken once; recursive head
conditioning does not silently resample the children.

For fresh random pivot, `RK.occurrenceRank` is a permutation of actual
occurrences. `RK.left_length_eq_rank` and `RK.right_length_eq_rank` prove the
sizes of the actual erased/filter children; `RK.child_keys_nodup` supplies their
inherited hypothesis. `RK.exerciseMean_eq_of_length_eq` compares actual means
across independent payload/key universes and equal lengths. Only then does
`RK.sizeMean`, defined as the actual execution on `List.range n`, acquire its
zero, successor and positive-size recurrence. The proof does not assume that
the child inputs themselves are uniformly shuffled.

For each actual exercise mean, the derived numerical sequence has

```text
A 0 = 1
A n = (2/n) * sum (A k, k < n) + 4*n - 1, for n > 0
A n = 8*(n+1)*H_n - 12*n + 1.
```

`QM.eq_closedForm` is the probability-independent solver. The actual consumers
are `UM.inputMean_eq_closedForm` and `RG.exerciseMean_eq_harmonic`; the latter
discharges the solver premises directly with `RK.sizeMean_zero` and
`RK.sizeMean_recurrence`. The common formula does not assert a joint-law or
execution-distribution identity between these distinct experiments.

At n≥1, the exercise mean is bounded by `16*n*(1+Real.log n)`. At n≥2, both
models have explicit binary-log exercise bound `32*n*Real.logb 2 n` and
append-inclusive bound `64*n*Real.logb 2 n`. The append bound comes from
observations of the same experiment: `UM.inputLiteralMean_bounds` and
`RM.literalMean_comparison`. It is an inequality, not the exercise's exact
harmonic equality. The uniform-input exercise family has the standard
`Asymptotics.IsBigO Filter.atTop` theorem; the fresh-pivot module additionally
exports natural/binary-log theorems for both means on arbitrary filters with
eventual mapped-key distinctness and actual lengths tending to infinity.
Their comparison function uses actual length, not an assumed-equal family index.

Consequential independent values are A0=1, A1=5, A2=13, A3=71/3, A4=109/3 and
A5=253/5. The three-key actual root costs are 21 at the middle key and 25 at either
extreme, with masses 1/3 and 2/3 respectively. The uniform-input examples calculate
71/3 both from the actual head partition and from the universal closed-form
result, including a key collision outside the selected set. Fresh-pivot examples
retain nonidentity occurrence ranks and actual unsorted child order.

Distinct raw records do not imply distinct keys. Under equal keys both models'
exercise mean remains `2*n²+2*n+1`; the fresh-pivot literal mean remains
`2*n²+5*n+1`. At n=3 the exercise mean is 25, not 71/3. At n=256 the fresh-pivot
means 131585/132353 violate the fixed distinct-key scalar right sides 65536/131072.
These concrete examples witness the missing hypothesis; the finite example does
not itself assert a general non-Big-O theorem. Empty and singleton positive
costs also preclude a scalar `C*n*log₂ n` bound at those two sizes, for any real C.

## Reading the correspondence

The following aliases give exact project paths and namespaces. In an alias
reference, `QC.run` means `Resources.QuickSort.run` in the stated resource file.
An unqualified name immediately following an alias in the same declaration
group uses that same namespace/path unless a separate standard namespace or
alias is given. Standard `List`, `Multiset`, `Nat` and `Fin` references retain
their library meanings. All paths below are relative to the repository root.
They identify source declarations, not an additional wrapper API.

| Alias | Exact source path | Namespace |
| --- | --- | --- |
| `S` | [Applications/Sorting/Sort.lean](../../Applications/Sorting/Sort.lean) | `Applications.Sorting` |
| `ST` | [Applications/Sorting/Stable.lean](../../Applications/Sorting/Stable.lean) | `Applications.Sorting` |
| `IO` | [Applications/Sorting/InsertionObservations.lean](../../Applications/Sorting/InsertionObservations.lean) | `Applications.Sorting` |
| `EIO` | [Examples/InsertionObservations.lean](../../Examples/InsertionObservations.lean) | `Examples.InsertionObservations` |
| `IC` | [Applications/Resources/InsertionSort.lean](../../Applications/Resources/InsertionSort.lean) | `Resources.InsertionSort` |
| `EIC` | [Examples/InsertionCosts.lean](../../Examples/InsertionCosts.lean) | `Examples.InsertionCosts` |
| `Q` | [Applications/Sorting/QuickSort.lean](../../Applications/Sorting/QuickSort.lean) | `Applications.Sorting` |
| `EQ` | [Examples/QuickSort.lean](../../Examples/QuickSort.lean) | `Examples.QuickSort` |
| `QC` | [Applications/Resources/QuickSort.lean](../../Applications/Resources/QuickSort.lean) | `Resources.QuickSort` |
| `EQC` | [Examples/QuickSortCosts.lean](../../Examples/QuickSortCosts.lean) | `Examples.QuickSortCosts` |
| `M` | [Applications/Sorting/Merge.lean](../../Applications/Sorting/Merge.lean) | `Applications.Sorting` |
| `SM` | [Applications/Sorting/SourceMerge.lean](../../Applications/Sorting/SourceMerge.lean) | `Applications.Sorting` |
| `MC` | [Applications/Resources/ListMerge.lean](../../Applications/Resources/ListMerge.lean) | `Resources.ListMerge` |
| `EMC` | [Examples/MergeCosts.lean](../../Examples/MergeCosts.lean) | `Examples.MergeCosts` |
| `TD` | [Applications/Sorting/TopDown.lean](../../Applications/Sorting/TopDown.lean) | `Applications.Sorting` |
| `ETD` | [Examples/TopDownSorting.lean](../../Examples/TopDownSorting.lean) | `Examples.TopDownSorting` |
| `TDC` | [Applications/Resources/TopDownSorting.lean](../../Applications/Resources/TopDownSorting.lean) | `Resources.TopDownSorting` |
| `BU` | [Applications/Sorting/BottomUp.lean](../../Applications/Sorting/BottomUp.lean) | `Applications.Sorting` |
| `EBU` | [Examples/BottomUpSorting.lean](../../Examples/BottomUpSorting.lean) | `Examples.BottomUpSorting` |
| `BUC` | [Applications/Resources/BottomUpSorting.lean](../../Applications/Resources/BottomUpSorting.lean) | `Resources.BottomUpSorting` |
| `NR` | [Applications/Sorting/NaturalRuns.lean](../../Applications/Sorting/NaturalRuns.lean) | `Applications.Sorting` |
| `ENR` | [Examples/NaturalRuns.lean](../../Examples/NaturalRuns.lean) | `Examples.NaturalRuns` |
| `NRC` | [Applications/Resources/NaturalRunComparisons.lean](../../Applications/Resources/NaturalRunComparisons.lean) | `Resources.NaturalRunComparisons` |
| `NS` | [Applications/Sorting/Natural.lean](../../Applications/Sorting/Natural.lean) | `Applications.Sorting` |
| `NSC` | [Applications/Resources/NaturalSorting.lean](../../Applications/Resources/NaturalSorting.lean) | `Resources.NaturalSorting` |
| `AL` | [Applications/Sorting/Alternating.lean](../../Applications/Sorting/Alternating.lean) | `Applications.Sorting` |
| `EAL` | [Examples/AlternatingSorting.lean](../../Examples/AlternatingSorting.lean) | `Examples.AlternatingSorting` |
| `TQ` | [Applications/Sorting/ThreeWayQuickSort.lean](../../Applications/Sorting/ThreeWayQuickSort.lean) | `Applications.Sorting` |
| `ETQ` | [Examples/ThreeWayQuickSort.lean](../../Examples/ThreeWayQuickSort.lean) | `Examples.ThreeWayQuickSort` |
| `RP` | [Applications/Resources/RandomQuickSort.lean](../../Applications/Resources/RandomQuickSort.lean) | `Resources.RandomQuickSort` |
| `ERP` | [Examples/RandomQuickSort.lean](../../Examples/RandomQuickSort.lean) | `Examples.RandomQuickSort` |
| `LB` | [Applications/Resources/ListBuildCosts.lean](../../Applications/Resources/ListBuildCosts.lean) | `Resources.ListBuildCosts` |
| `ELB` | [Examples/ListBuildCosts.lean](../../Examples/ListBuildCosts.lean) | `Examples.ListBuildCosts` |
| `DL` | [Applications/Resources/DifferenceListCosts.lean](../../Applications/Resources/DifferenceListCosts.lean) | `Resources.DifferenceListCosts` |
| `EDL` | [Examples/DifferenceListCosts.lean](../../Examples/DifferenceListCosts.lean) | `Examples.DifferenceListCosts` |
| `PT` | [Applications/Sequences/Partition.lean](../../Applications/Sequences/Partition.lean) | `Sequences.Partition` |
| `ETC` | [Examples/TopDownCosts.lean](../../Examples/TopDownCosts.lean) | `Examples.TopDownCosts` |
| `EBC` | [Examples/BottomUpCosts.lean](../../Examples/BottomUpCosts.lean) | `Examples.BottomUpCosts` |
| `ENRC` | [Examples/NaturalRunComparisons.lean](../../Examples/NaturalRunComparisons.lean) | `Examples.NaturalRunComparisons` |
| `ENS` | [Examples/NaturalSorting.lean](../../Examples/NaturalSorting.lean) | `Examples.NaturalSorting` |
| `ENSC` | [Examples/NaturalSortingCosts.lean](../../Examples/NaturalSortingCosts.lean) | `Examples.NaturalSortingCosts` |
| `EST` | [Examples/StableSorting.lean](../../Examples/StableSorting.lean) | `Examples.StableSorting` |
| `UQ` | [Applications/Sorting/Uniqueness.lean](../../Applications/Sorting/Uniqueness.lean) | `Applications.Sorting` |
| `EU` | [Examples/SortUniqueness.lean](../../Examples/SortUniqueness.lean) | `Examples.SortUniqueness` |
| `NRO` | [Applications/Resources/NaturalRunOperations.lean](../../Applications/Resources/NaturalRunOperations.lean) | `Resources.NaturalRunOperations` |
| `ENRO` | [Examples/NaturalRunOperations.lean](../../Examples/NaturalRunOperations.lean) | `Examples.NaturalRunOperations` |
| `RM` | [Applications/Resources/RandomQuickSortMean.lean](../../Applications/Resources/RandomQuickSortMean.lean) | `Resources.RandomQuickSort` |
| `ERM` | [Examples/RandomQuickSortMean.lean](../../Examples/RandomQuickSortMean.lean) | `Examples.RandomQuickSortMean` |
| `RK` | [Applications/Resources/RandomQuickSortRank.lean](../../Applications/Resources/RandomQuickSortRank.lean) | `Resources.RandomQuickSort` |
| `ERK` | [Examples/RandomQuickSortRank.lean](../../Examples/RandomQuickSortRank.lean) | `Examples.RandomQuickSortRank` |
| `QM` | [Applications/Resources/QuickSortMean.lean](../../Applications/Resources/QuickSortMean.lean) | `Resources.QuickSortMean` |
| `EQM` | [Examples/QuickSortMean.lean](../../Examples/QuickSortMean.lean) | `Examples.QuickSortMean` |
| `QT` | [Applications/Resources/QuickSortTransport.lean](../../Applications/Resources/QuickSortTransport.lean) | `Resources.QuickSort` |
| `EQT` | [Examples/QuickSortTransport.lean](../../Examples/QuickSortTransport.lean) | `Examples.QuickSortTransport` |
| `UM` | [Applications/Resources/UniformQuickSortMean.lean](../../Applications/Resources/UniformQuickSortMean.lean) | `Resources.UniformQuickSortMean` |
| `EUM` | [Examples/UniformQuickSortMean.lean](../../Examples/UniformQuickSortMean.lean) | `Examples.UniformQuickSortMean` |
| `RG` | [Applications/Resources/RandomQuickSortGrowth.lean](../../Applications/Resources/RandomQuickSortGrowth.lean) | `Resources.RandomQuickSort` |
| `ERG` | [Examples/RandomQuickSortGrowth.lean](../../Examples/RandomQuickSortGrowth.lean) | `Examples.RandomQuickSortGrowth` |
| `PO` | [Applications/Probability/PermutationOrder.lean](../../Applications/Probability/PermutationOrder.lean) | `Applications.Probability.PermutationOrder` |
| `PL` | [Applications/Probability/PermutationTail.lean](../../Applications/Probability/PermutationTail.lean) | `Applications.Probability.PermutationTail` |

## Complete 112-obligation correspondence

Every ID is retained exactly once in this table. The source item column fixes
what is being accounted for; the declaration and example columns give its
implementation, standard reuse or explicit explanatory/correction disposition.
No row is marked accepted by this draft. The frozen original inventory and its
five-row clarification remain preserved in the local checkpoint records.

### Specification and insertion

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-001 | Account for reflexive, transitive, antisymmetric, total `<=`, and the compatible strict comparison `<`. | Standard LinearOrder, LE/LT and their reflexive/transitive/antisymmetric/total laws; `S.sortOn_correct` and the book specializations of `Q.quickSortOn_correct`, `TD.sortFloorOn_correct`. Generic operations retain weaker input-local or relation-specific laws. | `EIO.transitivity_boundaries`; `ETD.local_comparator_keys`. |
| C02-002 | `S []`; `S (x :: xs)` iff every member of `xs` is at least `x` and `S xs`. | `ST.KeySorted` id is List.Pairwise (· ≤ ·); List.Pairwise.nil and List.pairwise_cons give exactly the source nil and head/all-tail recursion. The source proofs repeatedly use that interface. | Standard List.Pairwise nil/cons interface; `EIO.keyed_sort_observations` is the connected mapped-key predicate client. No duplicate predicate theory is required. |
| C02-003 | Correct sorting means both `S (sort xs)` and `M (sort xs) = M xs`, preserving multiplicities. | Ordinary contracts use KeySorted plus List.Perm; Multiset.coe_eq_coe converts the source multiset equality without losing duplicates. `S.sortOn_correct`, `Q.quickSortOn_correct`, `TD.sortFloorOn_correct` and `EIO.keyed_sort_observations` are concrete destinations. | `EIO.keyed_sort_observations`; `EQ.source_multiset`; `EU.constant_key_boundary` separates ordinary correctness from stability. |
| C02-004 | `insort1 x [] = [x]`; on `y :: ys`, insert before `y` if `x <= y`, otherwise recurse into `ys`. | List.orderedInsert, orderedInsert_nil and orderedInsert_cons; `EIO.keyed_insert_equations` specialize the source non-strict left-tie test. | `EIO.keyed_insert_equations`; `EIO.equal_key_payloads`. |
| C02-005 | `insort [] = []`; `insort (x :: xs) = insort1 x (insort xs)`. | List.insertionSort is the right fold of orderedInsert; insertionSort_nil and insertionSort_cons, exposed by `EIO.keyed_sort_equations`. | `EIO.keyed_sort_equations`; `EIO.signed_tail_fixed`. |
| C02-006 | (2.1) `M (insort1 x xs) = {x} + M xs`. Isabelle `mset_insort1`. | List.perm_orderedInsert and Multiset.coe_eq_coe; `EIO.keyed_insert_observations` explicitly proves the full-record inserted multiset equality. | `EIO.keyed_insert_observations` preserves one full-record occurrence. |
| C02-007 | (2.2) `M (insort xs) = M xs`. `mset_insort`. | List.perm_insertionSort; `S.insertionOn_spec`.perm and `EIO.keyed_sort_observations` expose source multiset preservation. | `EIO.keyed_sort_observations`; `EIC.key_contract`. |
| C02-008 | (2.3) `U (insort1 x xs) = {x} union U xs`. `set_insort1`. | List.mem_orderedInsert and `EIO.keyed_insert_observations` give membership iff equality with the new element or membership in the input. | `EIO.keyed_insert_observations` contains the exact membership iff. |
| C02-009 | (2.4) `S (insort1 a xs)` iff `S xs`. `sorted_insort1`. | `IO.pairwise_orderedInsert_iff`; separately `IO.pairwise_of_orderedInsert` gives the law-free converse, even for a separately observed relation. `EIO.keyed_sorted_iff` is the mapped-key source form. | `EIO.keyed_sorted_iff`; `EIO.raw_insertion_cannot_repair`; `EIO.transitivity_boundaries`. |
| C02-010 | (2.5) `S (insort xs)`. `sorted_insort`. | List.pairwise_insertionSort, `S.insertionOn_spec`.sorted and `EIO.keyed_sort_observations`. | `EIO.keyed_sort_observations`; `EIO.empty_type_sort`. |
| C02-011 | `Tinsort1 _ [] = 1`; `Tinsort1 x (y :: ys) = (if x <= y then 0 else Tinsort1 x ys) + 1`. | `IC.insertRun` defining nil/cons equations count one entry, including the terminal call; insertRun_value ties that execution to canonical insertion. | `EIC.empty_cost`; `EIC.singleton_cost`; `EIC.immediate_insertion`; `EIC.full_traversal`. |
| C02-012 | `Tinsort [] = 1`; `Tinsort (x :: xs) = Tinsort xs + Tinsort1 x (insort xs) + 1`. | `IC.sortRun` and sortRun_cons_cost sequence the actual returned sorted tail into insertRun, charging the source sort entry. | `EIC.singleton_cost`; `EIC.sorted_with_duplicates`; `EIC.tied_head_ignores_tail`. |
| C02-013 | (2.6) `Tinsort1 x xs <= len xs + 1`. `T_insort1_length`. | `IC.insertRun_cost_bounds` proves 1 ≤ cost ≤ input length + 1 for arbitrary decidable insertion relation. | `EIC.full_traversal`; `EIC.key_contract`. |
| C02-014 | (2.7) `len (insort1 x xs) = len xs + 1`. `length_insort1`. | List.orderedInsert_length; `EIO.keyed_insert_observations` includes the source length-plus-one statement. | `EIO.keyed_insert_observations` contains the exact length equation. |
| C02-015 | (2.8) `len (insort xs) = len xs`. `length_insort`. | List.perm_insertionSort.length_eq and `IC.sortRun_length` after erasure. | `EIO.keyed_sort_observations` supplies the multiset client; `IC.sortRun_length` is the direct generic length theorem. |
| C02-016 | Lemma 2.1: `Tinsort xs <= (len xs + 1)^2`. `T_insort_length`. | `IC.sortRun_quadratic` proves the printed bound (length + 1)^2; `EIC.source_quadratic` applies it. Stronger triangular bounds remain separate. | `EIC.source_quadratic`; `EIC.empty_cost`. |

### Two-way quicksort

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-017 | `quicksort [] = []`; a nonempty list uses its head as pivot, recursively sorts the `< pivot` and `>= pivot` filters of its tail, and appends left result, pivot, right result. | `Q.quickSortBy`, `Q.quickSortBy_nil`, `Q.quickSortBy_cons`, `Q.quickSortBy_singleton`; `Q.quickSortOn_cons` specializes the first held pivot, strict-less tail filter and complementary greater-or-equal tail filter. Termination is by tail-filter length; the literal append association is retained. | `EQ.mixed_source_equation`; `EQ.all_equal_right_recursion`; `EQ.empty_first_input`. |
| C02-018 | (2.9) `M (quicksort xs) = M xs`. `mset_quicksort`. | `Q.quickSortBy_perm` plus `EQ.source_multiset` gives exact occurrence/multiset preservation for every comparator and input. | `EQ.source_multiset`; `EQ.arbitrary_comparator_occurrences`. |
| C02-019 | Unnumbered helper: `M (filter P xs) = filter P (M xs)`. | `EQ.source_filter_multiset` uses Multiset.filter_coe for the exact list-to-multiset filter correspondence. | `EQ.source_filter_multiset`, the exact source-specific library bridge. |
| C02-020 | Unnumbered helper: complementary predicates partition a multiset; `filter P M + filter Q M = M` if `P x` iff `not Q x` for every `x`. | `EQ.source_complementary_multiset` retains the input-local complement hypothesis; `EQ.source_key_partition` specializes strict-less/greater-or-equal for lawful keys. | `EQ.source_complementary_multiset`; `EQ.source_key_partition`. |
| C02-021 | Unnumbered helper: `S (xs ++ ys)` iff `S xs`, `S ys`, and every member of `xs` is at most every member of `ys`. | `EQ.source_sorted_append` gives the exact Pairwise/KeySorted append iff: both pieces sorted and every left element precedes every right element. | `EQ.source_sorted_append`, with the cross-block relation explicit. |
| C02-022 | Unnumbered helper: `U (quicksort xs) = U xs`. `set_quicksort`. | `Q.mem_quickSortBy` and `EQ.source_support` give equality of support; quickSortBy_length supplies the size consequence separately. | `EQ.source_support`; `EQ.arbitrary_comparator_occurrences`. |
| C02-023 | Unnumbered theorem: `S (quicksort xs)`. `sorted_quicksort`. | `Q.quickSortBy_sorted_compatible_on` uses transitivity plus compatibility only on members of the actual input; quickSortOn_correct is the lawful-key source specialization. | `EQ.local_comparator_sorted`; `EQ.local_comparator_fails_globally`; `EQ.arbitrary_payload_order`. |
| C02-024 | Formalize both stated `O(n log n)` claims: average cost of first-pivot quicksort under a uniform ordering of distinct keys, and expected cost with a uniformly chosen pivot occurrence at every recursive call on distinct-key inputs. | `QC.run`, `QC.exerciseCost` and `QC.literalCost` give the actual deterministic observation; `QT.run_map` and `QT.exerciseCost_map` preserve it under payload projection. Uniform input: `UM.occurrenceInput`, `UM.inputMean`, `UM.integrable_inputCost`, `UM.observedCost_on_first`, `UM.child_integral_cond`, `UM.conditional_mean`, `UM.meanBy_recurrence`, `UM.meanBy_eq_closedForm`, `UM.inputMean_eq_closedForm` and `UM.inputMean_family_isBigO` connect the single sampled occurrence permutation to its actual execution mean. Fresh random pivot: `RP.run` and `RP.uniformIndex` feed `RM.exerciseMean`, `RM.exerciseLaw_integrable` and `RM.exerciseMean_cons`; `RK.left_length_eq_rank`, `RK.right_length_eq_rank`, `RK.child_keys_nodup` and `RK.exerciseMean_eq_of_length_eq` derive `RK.sizeMean_recurrence`. `RG.exerciseMean_eq_harmonic`, `RG.exerciseMean_le_nlogb` and `RG.exerciseMean_family_isBigO_logb` apply the actual recurrence. `UM.inputLiteralMean_bounds` / `UM.inputLiteralMean_le_nlogb` and `RG.literalMean_harmonic_comparison` / `RG.literalMean_family_isBigO_logb` retain their respective same-experiment append-inclusive bounds. `QM.closedForm` is the shared numerical expression, not an assumed execution law. | `ERM.three_key_exercise_mean`; `ERK.four_selected_children`; `ERG.three_reordered_harmonic`, `ERG.function_tagged_family_growth`, `ERG.shifted_range_family_growth`, `ERG.equal_key_binary_bounds_fail`; `EUM.three_mean_from_heads`, `EUM.three_mean_from_closedForm`, `EUM.outside_collision`, `EUM.equal_key_counterexample`, `EUM.arbitrary_payload_growth`, `EUM.taggedRange_literal_bound`. Zero/one domains and quadratic duplicate families remain explicit. |

### Ordinary merge and floor-left top-down sorting

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-025 | `merge [] ys = ys`, `merge xs [] = xs`, and head comparison chooses the left head on ties. | `SM.sourceMerge` defining equations, sourceMerge_eq_merge and mergeBy_source connect the source non-strict left-tie merge to canonical List.merge; `MC.run_value` and `EMC.source_value` connect measured execution to that same source value. | `EMC.source_value`; `EMC.key_source_value`; `EMC.empty_sides`. |
| C02-026 | `msort xs = xs` if `len xs <= 1`; otherwise split with `take (len xs / 2)` and `drop (len xs / 2)`, recursively sort, and merge. | `TD.sortFloorBy`, sortFloorBy_of_length_le, sortFloorBy_step, nil and singleton laws implement take/drop at floor(length/2), preserving the source ≤1 base. `ETD.source_three_split` checks the odd split. | `ETD.source_three_split`; `ETC.floor_three_run`; `ETC.same_values_different_comparisons`. |
| C02-027 | Termination of `merge` by sum of lengths; of `msort` by strict decrease of both floor-half and complementary lengths when `len xs > 1`. | `SM.sourceMerge` has a sum-of-lengths decrease. `TD.sortFloorBy` proves both source half lengths strictly decrease only in the length > 1 branch. | `ETD.source_three_split` and `EMC.source_value` exercise the actual decreasing recurrences; termination is supplied by the source definitions, not an input-size assumption. |
| C02-028 | (2.10) `M (merge xs ys) = M xs + M ys`. `mset_merge`. | List.merge_perm_append and `M.mergeBy_perm`; `MC.run_value` plus `EMC.result_multiset` yield the source sum of input multisets. | `EMC.result_multiset`; `EMC.tagged_exact`. |
| C02-029 | (2.11) `U (merge xs ys) = U xs union U ys`. `set_merge`. | The same permutation yields union membership; `EMC.result_mem` states the actual result's membership iff, with `MC.run_value` and `SM.sourceMerge_eq_merge` supplying the source form. | `EMC.result_mem`, for arbitrary comparison operations. |
| C02-030 | Lemma 2.2: `M (msort xs) = M xs`. `mset_msort`. | `TD.sortFloorBy_perm` and Multiset.coe_eq_coe; `ETD.full_multiset` retains repeated values under an arbitrary comparator. | `ETD.full_multiset`; `ETD.arbitrary_comparator_preserves_occurrences`. |
| C02-031 | (2.12) `S (merge xs ys)` iff `S xs and S ys`. `sorted_merge`. | `M.sublist_merge_left`, `M.sublist_merge_right` and `M.pairwise_of_merge` provide the law-free converse. `M.merge_sorted_compatible_on_iff` supplies the input-local iff; `EMC.source_key_sorted_iff` explicitly states the source/key specialization. | `EMC.source_key_sorted_iff`; `EMC.unsorted_for_every_comparator`. |
| C02-032 | Lemma 2.3: `S (msort xs)`. `sorted_msort`. | `TD.sortFloorBy_sorted_compatible_on` and sortFloorOn_correct give source sortedness with raw local compatibility and a lawful-key specialization. | `ETD.arbitrary_payload_order`; `ETD.local_comparator_keys`. |
| C02-033 | `Cmerge [] ys = Cmerge xs [] = 0`; two nonempty lists cost one comparison plus the chosen recursive branch. | `MC.run`, `MC.comparisons`, `MC.comparisons_nil_left`, `MC.comparisons_nil_right` and `MC.comparisons_cons_cons` give actual selected-branch merge comparison equations. The separate entries projection is not charged to this source counter. | `EMC.empty_sides`; `EMC.interleaving_observations`; `EMC.nonempty_tariffs` distinguish comparisons from entries. |
| C02-034 | `Cmsort xs = 0` for length at most one; otherwise the two recursive comparison counts plus `Cmerge` on the actual sorted halves. | `TDC.run` and comparisons_step sequence both measured source children, then `MC.run` on their actual returned sorted lists. run_value separately proves erasure. | `ETC.floor_three_run`; `ETC.floor_ascending`; `ETC.floor_descending`; `ETC.same_values_different_comparisons`. |
| C02-035 | (2.13) `len (merge xs ys) = len xs + len ys`. `length_merge`. | List.merge_perm_append.length_eq and `EMC.result_length`; SM/MC erasure gives the source merge length sum. | `EMC.result_length`, with no sortedness premise. |
| C02-036 | (2.14) `len (msort xs) = len xs`. `length_msort`. | `TD.sortFloorBy_length` and `TDC.run_length` give the source sorter length. | `ETC.raw_occurrences_and_bound` is the connected measured permutation/bound client; `TD.sortFloorBy_length` and `TDC.run_length` are the direct length APIs. |
| C02-037 | (2.15) `Cmerge xs ys <= len xs + len ys`. `C_merge_ub`. | `MC.comparisons_le` proves comparisons ≤ left length + right length for all inputs, with no sortedness premise. | `EMC.unsorted_cost_bounds`; `EMC.twoStage_bounds`; `EMC.low_singleton_attains_factor_two`. |
| C02-038 | Lemma 2.4: if `len xs = 2^k`, then `Cmsort xs <= k * 2^k`. `C_msort_le`. | `TDC.comparisons_le_of_length_pow` proves C ≤ k·2^k when length = 2^k; comparisons_le_clog proves the stronger all-length ceiling-log statement. `ETC.power_zero_boundary` retains k = 0. | `ETC.power_zero_boundary`; `ETC.raw_occurrences_and_bound`. The explicit power-of-two source theorem remains `TDC.comparisons_le_of_length_pow`. |
| C02-039 | Supporting source corollary `C_msort_log`: under the same power-of-two premise, comparison count is at most `len xs * log 2 (len xs)` after coercion. | `TDC.comparisons_le_real_log_of_length_pow` is the source real-log corollary with the power-of-two premise retained. The general comparisons_isBigO uses the separately proved growth bridge. | `ETC.descending_family_isBigO`; `ETC.empty_and_singleton`. |

### Ordinary bottom-up sorting

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-040 | `merge_adj [] = []`; singleton lists are unchanged; two leading runs are merged and prepended to the recursive pass over remaining runs. | `BU.mergePairsBy` and its nil/singleton/step equations implement adjacent pairs and retain the final odd run unchanged. | `EBU.ragged_pass_value`; `EBU.empty_inner_runs_are_counted`. |
| C02-041 | Intended (2.16): `len (merge_adj xss) = (len xss + 1) / 2`. `length_merge_adjacent`. | `BU.mergePairsBy_length` is the ceiling-half run-count law; mergePairsBy_length_lt gives strict decrease for at least two runs. | `EBU.ragged_run_count`; `EBU.empty_inner_runs_are_counted`. |
| C02-042 | `merge_all [] = []`; `merge_all [xs] = xs`; otherwise recurse on `merge_adj xss`. Termination uses C02-041 and `len xss >= 2`. | `BU.mergeAllBy` with nil/singleton/step laws repeats the actual pass and terminates by decreasing outer length. | `EBU.singleton_unsorted_run`; `EBU.ordinary_duplicate_sort`. |
| C02-043 | `msort_bu xs = merge_all (map singleton xs)`. | `BU.sortBottomUpBy` maps each input occurrence to a singleton run and calls mergeAllBy. Nil/singleton laws expose the boundaries. | `EBU.ordinary_duplicate_sort`; `EBU.arbitrary_comparator_preserves_occurrences`. |
| C02-044 | Book abbreviation `mset_mset`: sum all inner multisets, equivalently multiset of `flatten xss`. | `BU.multiset_flatten_eq_sum` is the explicit flatten-to-sum-of-inner-multisets bridge. | `EBU.ragged_multiset_as_sum`, the explicit standard multiset-sum correspondence. |
| C02-045 | Intended unnumbered preservation: `MM (merge_adj xss) = MM xss`. `mset_merge_adj`. | `BU.mergePairsBy_flatten_perm` and mergePairsBy_multiset preserve the flattened input multiset. | `EBU.ragged_duplicate_occurrences`; `EBU.ragged_multiset_as_sum`. |
| C02-046 | Intended (2.17): `M (merge_all xss) = MM xss`. `mset_merge_all`. | `BU.mergeAllBy_perm` and mergeAllBy_multiset preserve the sum of initial run occurrences. | `EBU.singleton_unsorted_run` and `EBU.ordinary_duplicate_sort` are actual merge-all clients; the unrestricted generic theorem is `BU.mergeAllBy_multiset`. |
| C02-047 | Unnumbered correctness: `M (msort_bu xs) = M xs`. `mset_msort_bu`. | `BU.sortBottomUpBy_perm` and sortBottomUpBy_multiset preserve the source input multiset. | `EBU.arbitrary_comparator_preserves_occurrences`; `EBU.ordinary_duplicate_sort`. |
| C02-048 | Unnumbered preservation: if every input run is sorted, every run in `merge_adj xss` is sorted. `sorted_merge_adj`. | `BU.mergePairsBy_sorted_compatible_on` preserves per-run sortedness using input-local comparator compatibility. | `EBU.ragged_pass_value` includes ragged lengths and an empty inner run; `BU.mergePairsBy_sorted_compatible_on` is the generic preservation contract. |
| C02-049 | (2.18): if every run of `xss` is sorted, then `merge_all xss` is sorted. `sorted_merge_all`. | `BU.mergeAllBy_sorted_compatible_on` proves whole-result sortedness from individually sorted input runs. | `EBU.local_comparator_ordinary`; `EBU.singleton_unsorted_run` guards the input-run sortedness boundary. |
| C02-050 | Unnumbered correctness: `S (msort_bu xs)`. `sorted_msort_bu`. | `BU.sortBottomUpBy_sorted_compatible_on` and sortBottomUpOn_correct provide the ordinary source sorter correctness. | `EBU.local_comparator_ordinary`; `EBU.signed_record_correct`. |
| C02-051 | `Cmerge_adj` has zero empty/singleton cost and otherwise adds the first pair's `Cmerge` to the recursive pass cost. | `BUC.pairsRun`, `BUC.pairsComparisons_nil`, `BUC.pairsComparisons_singleton` and `BUC.pairsComparisons_step` perform actual measured merges and the subsequent pass recursion. | `EBC.ragged_observation`; `EBC.three_equal_first_pass`. |
| C02-052 | `Cmerge_all` has zero empty/singleton cost and otherwise adds `Cmerge_adj xss` to the cost of merging the next pass. | `BUC.allRun`, `BUC.allComparisons_nil`, `BUC.allComparisons_singleton`, `BUC.allComparisons_step` and `BUC.allRun_value` recurse on the actual measured pass result. | `EBC.all_two_runs`; `EBC.ordinary_three_run`; `EBC.empty_and_single_run`. |
| C02-053 | `Cmsort_bu xs = Cmerge_all (map singleton xs)`. | `BUC.run`, comparisons and comparisons_eq_all use the singleton initialization with no unstated map/entry charge in the comparison-only model. | `EBC.ordinary_three_equal`; `EBC.raw_occurrences_and_bounds`. |
| C02-054 | (2.19): if `len xss` is even and every run has length `m`, every run after `merge_adj` has length `2*m`. `length_merge_adj`. | `BU.mergePairsBy_uniform_length` proves output length 2m under an even input run count and uniform input length m. | `EBU.even_uniform_runs_double`; `EBU.odd_runs_do_not_all_double`. |
| C02-055 | (2.20): if all runs have length `m`, `Cmerge_adj xss <= m * len xss`. `C_merge_adj`. | `BUC.pairsComparisons_le_uniform` proves the m·run-count bound without an evenness assumption; pairsComparisons_le handles arbitrary ragged runs. | `EBC.odd_uniform_budget_and_leftover`; `EBC.four_empty_runs_zero`. |
| C02-056 | Lemma 2.5: all runs of length `m` and `len xss = 2^k` imply `Cmerge_all xss <= m*k*2^k`. `C_merge_all`. | `BUC.allComparisons_le_uniform_pow` proves m·k·2^k under uniform inner length m and outer length 2^k. | `EBC.single_run_power_zero`; `EBC.uniform_four_runs_bound`; `EBC.four_empty_runs_zero`. |
| C02-057 | Corollary 2.6: `len xs = 2^k` implies `Cmsort_bu xs <= k*2^k`. `C_msort_bu`. | `BUC.comparisons_le_of_length_pow` proves k·2^k for the actual singleton-initialized sorter; `EBC.sorter_power_zero` checks the exponent-zero boundary. | `EBC.sorter_power_zero`; `EBC.descending_families_isBigO` is a connected general-bound client, not a replacement for the power-of-two source theorem. |

### Natural-run values and worker laws

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-058 | Mutually recursive `runs`: empty gives no runs, singleton gives one singleton run, and a two-element prefix chooses descending iff the second element is strictly smaller. | `NR.runsBy` chooses descending exactly when the next key is strictly smaller; otherwise it enters ascending. `NR.runsBy_nil`, `NR.runsBy_singleton` and `NR.runsBy_cons_cons` expose the source cases. | `ENR.empty_payload`; `ENR.singleton`; `ENR.restart_boundary`; `ENR.ascending_ties`; `ENR.descending_reversal`. |
| C02-059 | `asc a f [] = [f [a]]`. On `b :: bs`, continue with accumulator `f compose (a :: ·)` and new head `b` when `not (b < a)`; otherwise emit `f [a]` and start `runs (b :: bs)`. | `NR.ascBy` and its equations implement the source ascending worker with Batteries.DList; `NR.ascSourceBy_nil` and `NR.ascSourceBy_cons` expose the raw lawful-function recurrence. Equal adjacent keys stay ascending. | `ENR.arbitrary_builder_restart`; `ENR.seededBuilder_law`. |
| C02-060 | `desc a acc [] = [a :: acc]`. On `b :: bs`, continue with `a :: acc` when `b < a`; otherwise emit `a :: acc` and start `runs (b :: bs)`. | `NR.descBy_nil` and `NR.descBy_cons` implement strict descent, accumulating by cons and emitting the reversed descending run at its stopping point. | `ENR.descending_reversal`; `ENR.weak_descending_value`. |
| C02-061 | Difference-list specification `D f`. Source support `ascP_Cons`, `ascP_comp_Cons`, `ascP_simp`: singleton-prefix functions satisfy it, composition with a singleton prefix preserves it, and `f [a] = f [] ++ [a]`. | `NR.DListLaw`, dListLaw_iff, dListLaw_cons, DListLaw.push, dListOfLaw and its application/toList/push laws connect raw source functions to Batteries.DList. dList_apply_eq and dList_push_apply expose the append-order laws. | `ENR.seededBuilder_law`; `ENR.arbitrary_builder_occurrences`; `ENR.arbitrary_builder_length`. |
| C02-062 | Mutual termination and induction for `runs`, `asc`, `desc`, including restarting `runs` on `b :: bs`. | The actual mutual definitions carry length-based termination measures; mutual perm/nonempty/length/sortedness proofs follow their source calls, including worker-to-runs restart. | `ENR.restart_boundary`; `ENR.arbitrary_builder_restart`; `ENR.weak_descent_with_ties` exercise actual worker/restart paths. Kernel termination belongs to the definitions. |
| C02-063 | `nmsort xs = merge_all (runs xs)`. | `NS.sortNaturalBy` and sortNaturalBy_eq_mergeAll are exactly mergeAllBy applied to the actual runsBy output. | `ENS.three_boundary`; `ENS.restart_boundary`; `ENS.odd_runs_value`. |
| C02-064 | (2.21): `D f` implies `MM (asc x f ys) = {x} + M (f []) + M ys`. Source `mset_asc`. | `NR.ascSourceBy_perm` gives arbitrary raw D-law prefix/current/tail occurrence preservation; ascBy_multiset and Multiset.coe_eq_coe expose the corresponding multiset sum using f [] as prefix. | `ENR.arbitrary_builder_occurrences`; `ENR.unsorted_builder_value`. |
| C02-065 | (2.22): `MM (desc x xs ys) = {x} + M xs + M ys`. `mset_desc`. | `NR.descBy_perm` and descBy_multiset preserve the arbitrary accumulator, current element and tail occurrences. Reverse in the permutation form does not alter the accumulator multiset. | `ENR.weak_descending_occurrences`; `ENR.weak_descending_value`. |
| C02-066 | (2.23): `MM (runs xs) = M xs`. `mset_runs`. | `NR.runsBy_perm` and runsBy_multiset preserve every input occurrence through the emitted run list. | `ENR.mixed_occurrences`; `ENR.mixed_shape`. |
| C02-067 | (2.24): `M (nmsort xs) = M xs`. `mset_nmsort`. | `NS.sortNaturalBy_perm` and sortNaturalBy_multiset compose runs preservation with the actual bottom-up merger. | `ENS.duplicate_occurrences`; `ENS.arbitrary_operations_preserve_occurrences`. |
| C02-068 | (2.25): every run in `runs xs` is sorted. `sorted_runs`. | `NR.runsBy_sorted_compatible_on` and runsOn_sorted prove every emitted run sorted, with input-local compatibility or lawful keys respectively. | `ENR.restart_blocks_sorted`; `ENR.restart_flatten_not_sorted`; `ENR.mixed_expected_blocks_sorted`. |
| C02-069 | Source support for C02-068: `D f`, sorted `f []`, and every member of `f [] <= a` imply every output of `asc a f ys` is sorted; sorted `xs` and `a <=` every member of `xs` imply every output of `desc a xs ys` is sorted. | `NR.ascBy_sorted_compatible_on`, descBy_sorted_compatible_on and ascSourceBy_sorted retain the actual prefix/accumulator sortedness and upper/lower-bound invariants. ENR's unsorted builder and missing-bound examples test their necessity. | `ENR.lawful_builder_does_not_imply_sorted`; `ENR.sorted_prefix_needs_upper_bound`; `ENR.weak_descending_sorted`; `ENR.weak_descending_not_stable`. |
| C02-070 | (2.26): `S (nmsort xs)`. `sorted_nmsort`. | `NS.sortNaturalBy_sorted_compatible_on` and sortNaturalOn_correct combine run sorting with mergeAllBy sorting. | `ENS.input_local_correct`; `ENS.tagged_correct`; `ENS.constant_key_fixed_point`. |

### Natural comparisons and general merge bounds

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-071 | Mutually recursive `Cruns`, `Casc`, `Cdesc`: no comparison for empty/singleton `runs` or empty worker tail; every tested adjacent pair costs one plus exactly the selected worker/restart branch. | `NRC.runsCountBy`, ascCountBy and descCountBy with all source equations; actual `NRC.runsRunBy`, `NRC.ascRunBy` and `NRC.descRunBy` and their spec/value/cost laws connect those scalar counts to selected-branch executions. | `ENRC.restart_boundary`; `ENRC.arbitrary_comparators_same_count`; `ENRC.unsorted_builder_zero_comparisons`. |
| C02-072 | `Cnmsort xs = Cruns xs + Cmerge_all (runs xs)`. | `NSC.run` and comparisons_eq_scan_add_merge sequence actual measured scanning into `BUC.allRun` on the returned runs; comparisons_eq_length_add_merge uses the exact scan count. | `ENSC.three_boundary_scan`; `ENSC.three_boundary_merge`; `ENSC.three_boundary`; `ENSC.restart_boundary`. |
| C02-073 | (2.27): `Cmerge_adj xss <= len (flatten xss)`. Source `C_merge_adj'`. | `BUC.pairsComparisons_le` proves pass comparisons ≤ total flattened input length for arbitrary run lists. | `EBC.ragged_observation`; `EBC.ragged_general_bound` composes the arbitrary-pass bound with the actual outer merger. |
| C02-074 | (2.28): `len (flatten (merge_adj xss)) = len (flatten xss)`. `length_concat_merge_adj`. | `BU.mergePairsBy_flatten_length`, equivalently mergePairsBy_sum_lengths, preserves the total length used in the comparison bound. | `EBU.ragged_total_length`; `EBU.ragged_sum_lengths`. |
| C02-075 | (2.29): for `n >= 2`, `L n = L ((n-1)/2 + 1) + 1`. Source uses `ceiling_log2_div2`. | `BUC.clog_two_source_half` and clog_two_ceil_half prove the source half-count recurrence for n ≥ 2. int_ceil_logb_two_nat and int_ceil_logb_two_source_half supply the exact totalized real-log/integer-ceiling correspondence. | `EBC.source_ceiling_zero_one`; `EBC.source_half_at_five`. |
| C02-076 | Lemma 2.7: `Cmerge_all xss <= len (flatten xss) * L (len xss)`. `C_merge_all'`. | `BUC.allComparisons_le_clog` and allComparisons_le_int_ceil give flattened-length times ceiling-log run count, including empty/one-run and empty-inner-run cases. | `EBC.ragged_general_bound`; `EBC.empty_and_single_run`; `EBC.four_empty_runs_zero`. |
| C02-077 | (2.30), asc component: under `D f`, `len (flatten (asc a f ys)) = 1 + len (f []) + len ys`. `length_concat_asc`. | `NR.ascBy_flatten_length` and ascSourceBy_flatten_length give current + represented prefix + tail length, retaining the raw D-law bridge. | `ENR.arbitrary_builder_length`; `ENR.arbitrary_builder_occurrences`. |
| C02-078 | (2.30), desc component: `len (flatten (desc a xs ys)) = 1 + len xs + len ys`. `length_concat_desc`. | `NR.descBy_flatten_length` gives current + accumulator + tail length for arbitrary accumulator. | `ENR.weak_descending_value`; `ENR.weak_descending_occurrences`. `NR.descBy_flatten_length` supplies the unrestricted exact length theorem. |
| C02-079 | (2.30), runs component: `len (flatten (runs xs)) = len xs`. `length_concat_runs`. | `NR.runsBy_flatten_length` preserves the source input length. | `ENR.mixed_shape`; `ENR.mixed_occurrences`. |
| C02-080 | (2.31), asc component: `D f` implies `len (asc a f ys) <= 1 + len ys`. `length_asc`. | `NR.ascBy_length_le` bounds the number of output runs by tail length + 1, independently of the builder prefix size; ascSourceBy is the exact raw-builder bridge. | `ENR.arbitrary_builder_run_bound`, retaining an arbitrary existing builder prefix. |
| C02-081 | (2.31), desc component: `len (desc a xs ys) <= 1 + len ys`. `length_desc`. | `NR.descBy_length_le` gives the same tail length + 1 run-count bound for arbitrary accumulator. | `ENR.weak_descending_value` is a concrete arbitrary-accumulator worker case; `NR.descBy_length_le` is the generic bound. |
| C02-082 | (2.31), runs component: `len (runs xs) <= len xs`. `length_runs`. | `NR.runsBy_length_le` proves run count ≤ input length, including empty input. | `ENR.mixed_shape`; `ENSC.constant_key_run_count`. |
| C02-083 | (2.32), asc component: `Casc a ys <= len ys`. `C_asc`. | `NRC.ascCountBy_le` and ascRunBy_cost_exact prove the printed upper bound and stronger exact tail-length identity. ascSourceRunBy_cost covers a raw D-law builder. | `ENRC.arbitrary_builder_restart`; `ENRC.unsorted_builder_zero_comparisons`. |
| C02-084 | (2.32), desc component: `Cdesc a ys <= len ys`. `C_desc`. | `NRC.descCountBy_le` and descRunBy_cost_exact give the upper bound and exact tail-length comparison identity. | `ENRC.weak_descending_zero_comparisons`; `ENRC.descending_reversal`. |
| C02-085 | (2.32), runs component: `Cruns xs <= len xs - 1`, with natural truncated subtraction. `C_runs`. | `NRC.runsCountBy_le`, runsCountBy_exact and runsRunBy_cost_exact give comparisons = length − 1 with truncated Nat subtraction. | `ENRC.arbitrary_comparators_same_count`; `ENRC.empty_payload`; `ENRC.singleton`. |
| C02-086 | Lemma 2.8: `len xs = n` implies `Cnmsort xs <= n + n * L n`. `C_nmsort`. | `NSC.comparisons_le_source`, comparisons_le_of_length, `NSC.comparisons_le_int_ceil` and `NSC.comparisons_le_int_ceil_of_length` state the exact source bound n + n·ceiling(log₂ n); the adaptive/clog variants are stronger intermediate statements. | `ENSC.arbitrary_operations_and_bounds`; `ENSC.integer_zero_one_bound`; `ENSC.odd_runs_adaptive_budget`. |
| C02-087 | Source support: nonempty input gives nonempty `runs`; worker outputs are nonempty under the appropriate `D` condition; logarithm is monotone on positive arguments. `runs_ne` and `log2_mono`. | `NR.runsBy_nonempty`, ascBy_nonempty, descBy_nonempty, ascBy_ne_nil, descBy_ne_nil and runsBy_eq_nil_iff supply positivity/nonempty facts. BUC's ceiling bridge and standard Nat.clog monotonicity support the final source bound. | `ENR.empty_is_not_one_run`; `ENSC.integer_zero_one_bound`; `EBC.source_ceiling_zero_one`. |
| C02-088 | Formalize the pp.21–22 best-case and difference-list mathematical claims. For a sorted nonempty input, prove `runs xs=[xs]`, zero merge comparisons, and the exact scan/comparison specialization; retain a separate declared operational model for constant-time builder composition and linear materialization of the actual ascending-run builders. | The umbrella is split across the actual NS/NSC best-case comparison execution, LB ordinary construction comparison, DL closure capture/application algebra, and NRO actual ascending builder/scanner/zero-or-one-run dispatch. C02-108–112 retain the distinct scopes and source recurrences. | `ENSC.ascending_zero_merge`; `EDL.expensive_capture`; `ENRO.comparison_counter_is_separate`; `ENRO.charged_identity_changes_worker_work`. See C02-108–112 for separate tariffs/statuses. |

### Ordinary uniqueness, keys and stability

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-089 | Theorem 2.9: `M ys = M xs`, `S xs`, and `S ys` imply `xs = ys`. Source `sorting_unique`. | List.Perm.eq_of_pairwise' under Std.Antisymm, together with Multiset.coe_eq_coe, supplies ordinary source uniqueness. `UQ.sorters_eq_at` is its direct chapter use; equality of ordinary outputs requires no totality or stability premise. | `EU.first_pivot_eq_floor`; `EU.reverse_eq_of_equal`; `EU.equality_order_boundary`. `EST.sorted_permutation_not_stable` guards keyed relations lacking antisymmetry. |
| C02-090 | Corollary 2.10: any two functions satisfying the sorting specification for every input are pointwise equal and hence equal as functions. | `UQ.sorters_eq_at` proves pointwise equality for arbitrary functions satisfying the ordinary pairwise/permutation contract at one input. `UQ.sorters_eq` uses the contracts for every input plus function extensionality. `UQ.sorters_eq_of_multiset` retains the printed multiset formulation. All quantify over arbitrary Type u and relation with Std.Antisymm; no totality, stability, decidable payload equality or default element is added. | `EU.first_pivot_eq_floor`; `EU.three_way_eq_floor`; `EU.floor_mixed_duplicates`; `EU.reverse_eq_of_equal`; `EU.equality_order_boundary`; `EU.constant_key_boundary`. |
| C02-091 | (2.33) and (2.34) are induction-case premises: equal multisets and sortedness of two nonempty lists. Account for them as proof steps, not independent new theorem requirements. | Displays (2.33) and (2.34) are premises in the proof of ordinary uniqueness; the standard theorem's proof is the reuse destination. | No separate theorem/example is required for two proof premises. C02-089's standard proof and `EU.equality_order_boundary` give the disposition without adding totality or stability. |
| C02-092 | Key-sort correctness preserves full-record multisets and sorts the mapped keys; stability preserves every filtered equal-key subsequence. | `ST.KeySorted`, Stable and StableSort; List.pairwise_map and `EIO.keyed_sort_observations` connect mapped-key sortedness, full-record multiset preservation and exact equal-key filtered subsequences. | `EIO.keyed_sort_observations`; `EST.sorted_permutation_not_stable`; `EST.transform_then_sort`; `EST.sort_then_transform`. |
| C02-093 | `insort1_key` and `insort_key` are the insertion recurrences with comparisons on keys, selecting the newly inserted earlier record on ties. | `S.insertionOn` plus `EIO.keyed_insert_equations` and keyed_sort_equations are the source keyed insertion and tail-first/right-fold sort definitions. | `EIO.keyed_insert_equations`; `EIO.keyed_sort_equations`; `EIO.equal_key_payloads`. |
| C02-094 | Keyed insertion correctness: `M (insort_key f xs) = M xs` and (2.35) sorted `map f (insort_key f xs)`. Source `mset_insort_key`, `sorted_insort_key`. | `EIO.keyed_insert_observations` and keyed_sorted_iff; `IO.pairwise_orderedInsert_iff` and law-free pairwise_of_orderedInsert; `EIO.keyed_sort_observations` for whole-sort multiset/mapped sortedness. | `EIO.keyed_insert_observations`; `EIO.keyed_sorted_iff`; `EIO.keyed_sort_observations`. |
| C02-095 | (2.36): if `f a <= f x` for every `x` in `xs`, then `insort1_key f a xs = a :: xs`. `insort1_is_Cons`. | `IO.orderedInsert_eq_cons_of_forall` proves immediate insertion from the source all-members premise; `EIO.all_members_without_sorted_input` tests an unsorted tail. | `EIO.all_members_without_sorted_input`; `EIO.tied_head_ignores_inversion`. |
| C02-096 | (2.37): if `not P x`, filtering after inserting `x` equals filtering before insertion. `filter_insort1_key_neg`. | `IO.filter_orderedInsert_of_neg` proves the negative filter law under p a = false, for any decidable insertion relation; `EIO.signed_negative_step` connects the actual sorted-tail proof use. | `EIO.negative_filter_unsorted`; `EIO.negative_extreme_relations`; `EIO.signed_negative_step`. |
| C02-097 | (2.38): if keys of `xs` are sorted and `P x`, filtering after inserting `x` equals inserting `x` into the filtered list. `filter_insort1_key_pos`. | `IO.filter_orderedInsert_of_pos` and `EIO.keyed_filter_of_pos` retain p a = true, transitivity, and sortedness under the same relation. `EIO.positive_filter_needs_sorted_input` checks the omitted-hypothesis boundary. | `EIO.keyed_filter_of_pos`; `EIO.positive_filter_needs_sorted_input`; `EIO.positive_filter_discards_stopping_head`. |
| C02-098 | Lemma 2.11: `filter (key = k) (insort_key key xs) = filter (key = k) xs`. `sort_key_stable`. | `S.insertionOn_spec` and `EIO.keyed_sort_observations` provide exact equal-key filtering. `EIO.signed_tail_fixed`, signed_negative_step and signed_positive_step connect the displayed helper argument to actual recursive tails. | `EIO.signed_tail_fixed`; `EIO.signed_negative_step`; `EIO.signed_positive_step`; `EIO.stability_is_not_arbitrary_filter`. |

### Exercises

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-099 | Exercise 2.1, optimal case: sorted `xs` of length `n` has `Tinsort xs = 2*n + 1`. Establish the corresponding global lower bound to justify “optimal.” | `IC.sortRun_cost_of_pairwise` attains 2·length + 1 on sorted input; sortRun_cost_lower is the global lower bound. `EIC.sorted_with_duplicates` and best_is_global are connected clients. | `EIC.sorted_with_duplicates`; `EIC.best_is_global`; `EIC.empty_cost`. |
| C02-100 | Exercise 2.1, worst case: `Tinsort (reverse (range n)) = (n+1)*(n+2)/2`. Establish the triangular global upper bound to justify “worst,” stronger than Lemma 2.1. | `IC.reverse_range_opposite`, sortRun_double_cost_of_opposite and sortRun_cost_reverse_range attain (n+1)(n+2)/2 on reverse(range n); sortRun_double_cost_le and sortRun_cost_le give the global upper bound. | `EIC.descending_worst`; `EIC.worst_is_global`; `EIC.small_rank_with_sort_budget` is the existing consequential sorting-cost client. |
| C02-101 | Exercise 2.2: define accumulating `quicksort2 xs ys` using only cons, with no append in its recursive implementation; prove `quicksort2 xs ys = quicksort xs ++ ys`. | `Q.quickSortAccBy` is the append-free suffix worker; quickSortAccBy_eq_append holds for every suffix and arbitrary comparator. `Q.quickSortAccOn_cons`, `Q.quickSortAccOn_eq_append` and `Q.quickSortAccOn_correct` give the source keyed form. `QC.accumulatorRun_exact`, `QC.accumulatorRun_eq_append` and `QC.accumulatorRun_cost_independent` connect its actual measured execution. | `EQ.mixed_accumulator_value`; `EQ.arbitrary_payload_suffix`; `EQ.sorted_suffix_is_not_enough`; `EQC.empty_worker`; `EQC.duplicate_worker`. |
| C02-102 | Exercise 2.3: `partition3 pivot xs` gives `<`, `=`, `>` filtered lists; `quicksort3` recursively sorts only the strict parts and places pivot plus equal list between them. Prove both sortedness and multiset preservation. | `TQ.threeWayQuickSort` implements three tail filters, recursing only on strict less/greater, retaining one held pivot plus the entire equal block. `TQ.threeWayQuickSort_cons`, `TQ.threeWayQuickSort_cons_partition`, `TQ.threeWayQuickSort_perm`, `TQ.threeWayQuickSort_multiset`, `TQ.threeWayQuickSort_sorted`, `TQ.threeWayQuickSort_correct` and `TQ.threeWayQuickSort_replicate`, with ETQ's independent cases, cover the exercise. | `ETQ.empty_input`; `ETQ.singleton_input`; `ETQ.all_equal_family`; `ETQ.mixed_multiplicities`; `ETQ.absent_pivot_child_decrease`; `ETQ.omitted_equal_block_boundary`. |
| C02-103 | Exercise 2.4, both parts: use the supplied `Tquicksort` recurrence, prove exact quadratic cost on sorted inputs, and prove the same polynomial is a global upper bound. | `QC.exerciseCost_cons_source` and `QC.exerciseCost_cons_on` preserve the supplied two-filter tariff; exerciseCost_le proves 2n²+2n+1 globally and costs_of_sorted attains it, including weakly sorted duplicate inputs. Literal appendCost/literalCost are separately executed and bounded. | `EQC.ascending_costs`; `EQC.descending_range_attains_bound`; `EQC.payload_exercise_bound`; `EQC.duplicate_family`; `EQC.right_associated_appends`; `EQC.left_associated_appends`. |
| C02-104 | Exercise 2.5: define alternating, accumulating `halve`, matching `halve [2,3,4] ([0],[1]) = ([4,2,0],[3,1])`; define the displayed two-base-case `msort2`; prove sortedness and multiset preservation. | `AL.halve` is the actual alternating accumulator pass. halve_perm, halve_lengths, halve_balance, halve_empty_balance and halve_strict give occurrence/length/balance/decrease laws. sortAlternatingBy and sortAlternatingOn_correct use its returned halves. `EAL.source_halve_example` is [2,3,4] with ([0],[1]) giving ([4,2,0],[3,1]). | `EAL.source_halve_example`; `EAL.unbalanced_initial_piles`; `EAL.recursive_halves`; `EAL.duplicate_source_value`; `EAL.source_variant_not_stable`. |
| C02-105 | Exercise 2.6: define tail-recursive `merge_adj2 acc xss` without append, and `merge_all2`, `msort_bu2`; prove `M (msort_bu2 xs) = M xs` and sortedness. | `BU.mergePairsRevBy` is the append-free tail pass; mergeAllRevBy and sortBottomUpRevBy repeat it and prove ordinary correctness. `BUC.pairsRevComparisons_eq` proves exact per-pass equality; `BUC.allRevComparisons_le_clog`, `BUC.allRevComparisons_le_uniform_pow` and the `BUC.revComparisons` bounds prove the complete requested complexity. | `EBU.tail_duplicate_sort`; `EBU.tail_sort_need_not_be_stable`; `EBC.same_pass_costs_different_totals`; `EBC.descending_families_isBigO`. |
| C02-106 | Exercise 2.6 support, also accidentally printed in §2.5: `len (merge_adj2 acc xss) = len acc + (len xss + 1)/2`; `MM (merge_adj2 acc xss) = MM acc + MM xss`; `M (merge_all2 xss) = MM xss`. | `BU.mergePairsRevBy_eq_reverse_append`, `BU.mergePairsRevBy_length`, `BU.mergePairsRevBy_flatten_perm`, `BU.mergePairsRevBy_flatten_length` and `BU.mergePairsRevBy_multiset` account for arbitrary accumulator; mergeAllRevBy_multiset covers repeated merging. `BUC.pairsRevRun_value`, `BUC.pairsRevRun_eq` and `BUC.pairsRevComparisons_eq` concern the actual pass. | `EBU.arbitrary_accumulator_run_count`; `EBU.unsorted_accumulator_multiset`; `EBC.accumulator_cost_independent`; `EBC.nonempty_accumulator_observation`. |
| C02-107 | Exercise 2.7: adapt a stated selection of non-insertion algorithms to keys; prove correctness and stability. | Selected non-insertion algorithm: `TD.sortFloorBy` with the source contiguous floor-left split and left-tie merge. `TD.sortFloorOn_correct`, `TD.sortFloorOn_stable` and `TD.sortFloorOn_spec` give ordinary/keyed correctness and exact equal-key stability. `TD.sortFloorOn_eq_sortOn` is a separate value bridge. No stability is asserted for alternating or reversed-pass variants. | `ETD.payload_expected_spec`; `ETD.stable_across_split`; `ETD.signed_record_value`; `EIO.equal_key_payloads` preserves the chosen insertion comparison boundary. |

### Explicit best-case and operational clarification

| ID | Source item | Exact source correspondence | Connected examples and boundaries |
| --- | --- | --- | --- |
| C02-108 | Sorted-input best case, pp.21–22: for nonempty sorted xs, `runs xs=[xs]`, `Cmerge_all(runs xs)=0` and `Cnmsort xs=length xs-1`. Empty input has zero comparisons. | `NR.runsOn_of_sorted` gives the single run for nonempty sorted input. NRC's three exact counts and runsRunBy_of_sorted give scan n−1. `NSC.mergeComparisons_of_sorted`, run_of_sorted, comparisons_of_sorted and comparisons_lower give zero merge work, exact best count and global lower bound; empty/singleton laws retain zero. | `ENSC.ascending_zero_merge`; `ENSC.ascending_range_exact`; `ENSC.repeated_payload_exact`; `ENSC.empty_payload`; `ENSC.singleton_payload`. |
| C02-109 | Repeated append versus cons/reverse, p.22: appending n singleton values to an initially empty ordinary-list accumulator has append-call subcost `n*(n+1)/2`; the full fixed-overhead builder therefore has quadratic worst-case time. Prepending those values and applying the verified accumulator reverse has linear work and the same ordered result. | `LB.appendSubRun_empty_cost` gives n(n+1)/2; appendLoopRun_cost and appendBuildRun_cost expose loop/wrapper entries. `LB.consReverseBuildRun_value` and `LB.consReverseBuildRun_cost` give the same ordered result with 2n+3 work; `LB.realizations_agree`, `LB.appendBuildRun_quadratic_lower`, `LB.appendBuildRun_quadratic_upper` and `LB.consReverseBuildRun_linear_upper` provide the resource comparison. ELB checks order, duplicates, nonempty seeds and empty payloads. | `ELB.ordered_duplicates`; `ELB.order_is_restored`; `ELB.nonempty_seed`; `ELB.same_value_different_cost`; `ELB.uniform_bounds`. |
| C02-110 | Difference-list append, p.22: creating the composed builder has constant local work independent of the represented list lengths, and its value is function composition with the correct append order. | `DL.createCompose_eq` gives constant capture work independently of both stored callbacks' application costs; `DL.compose_value` and `DL.compose_rep` give correct composition/append order. `EDL.expensive_capture` and ordered_composition separate creation from invocation. | `EDL.expensive_capture`; `EDL.ordered_composition`; `EDL.standard_composition_value`. |
| C02-111 | Difference-list materialization, p.22: applying a finite builder built from identity, singleton-prefix and composition to a suffix has work bounded linearly in its construction representation, with exact value equal to its represented prefix appended to that suffix. | `DL.Rep`, `DL.AppCost`, `DL.buildFrom` and `DL.build_appCost` give finite closure construction/application laws. `NRO.ascOpsBy_buildFrom` and runsOpsBy_buildAscending connect the actual source worker to the actual stored callback construction; buildAscending_rep, buildAscending_appCost, buildAscending_apply, buildAscending_counts_add_three and buildAscending_counts relate its construction/application measure to the emitted prefix, retaining arbitrary suffix values. Existing EDL padded/doubled examples separate output length, construction history and unfolded invocation occurrences. | `EDL.materialize_eq`; `EDL.no_bound_from_output_length`; `EDL.four_shared_closure_extensions_materialized`; `ENRO.source_builder_with_suffix`; `ENRO.source_builder_two_applications`; `ENRO.arbitrary_callback_continuation`. |
| C02-112 | The actual runs/asc/desc construction has `W_runs xs<=A*length xs+B` in the chosen closure/scanner model, with fixed constants, hence the single-run natural-sort execution has linear operational work as well as C02-108's linear comparisons. | `NRO.runsOpsBy`, `NRO.ascOpsBy` and `NRO.descOpsBy` instrument the actual scanner, closure creation and invocation, descending conses, emitted outer-run construction and branch/entry work. runsOpsBy_work_le gives ≤6n+1; ascOpsBy_work_le requires AppCost f k and gives ≤k+6m+5; descOpsBy_work_le gives ≤6m+5 for an arbitrary existing accumulator. singleRunOpsBy binds the actual returned list to baseMergeOps on the explicit run-count≤1 domain, with value/spec and ≤6n+2. Nil/singleton executions are 2/4; ascending n≥2 is 6n−4, descending nonempty strict-chain execution is 3n+1. | `ENRO.generic_scanner_contracts`; `ENRO.arbitrary_payload_correct`; `ENRO.empty_payload_execution`; `ENRO.singleton_payload_execution`; `ENRO.ascending_three_execution`; `ENRO.descending_three_execution`; `ENRO.multiple_runs_outside_dispatch`; `ENRO.comparison_counter_is_separate`. |

## Printed corrections and necessary boundaries

| Printed item or potential ambiguity | Retained disposition and connected evidence |
| --- | --- |
| §2.5 prints accumulator-style names before Exercise 2.6 introduces them. | Ordinary pass/repeated-pass laws remain C02-041/045/046; the actually printed accumulator length/multiset laws are separately preserved in C02-106. `BU.mergePairsBy_length`, `BU.mergeAllBy_multiset`, `BU.mergePairsRevBy_eq_reverse_append` and arbitrary-accumulator examples distinguish both algorithms. No undefined operation becomes an axiom. |
| §2.7 infers mutual comparison of distinct values from failure of linearity. | That describes failure of antisymmetry; non-totality alone is insufficient. Ordinary pairwise/permutation uniqueness uses `Std.Antisymm`. `EU.equality_order_boundary`, `EU.constant_key_boundary` and `EST.sorted_permutation_not_stable` retain the distinction for keyed records. |
| Source floor-left split versus the library's different odd split. | The book recurrence has its own `TD.sortFloorBy` execution and `TDC.run`. On `[0,1,2]`, source/library counts are 2/3; on `[2,1,0]` they are 3/2. `ETC.same_values_different_comparisons` prevents transferring cost from mere sorted-value equality. |
| Odd numbers of uniform-length runs. | The leftover run retains its old length. Uniform doubling requires even run count; the pass comparison bound does not. `EBU.odd_runs_do_not_all_double` and `EBC.odd_uniform_budget_and_leftover` retain both domains. |
| Ceiling logarithm at zero/one and numeric coercions. | `Nat.clog 2`, real `Real.logb 2` and integer ceiling have explicit bridges. The half-count recurrence retains n≥2; `EBC.source_ceiling_zero_one` and `ENSC.integer_zero_one_bound` keep the totalized zero/one values. |
| Exercise 2.1 index convention. | `List.range n` has n values. Its reverse attains `(n+1)*(n+2)/2`; the prose list from n down to 0 has n+1 values and must not be assigned the same length silently. |
| Exercise 2.4's supplied tariff omits append traversal. | T retains exactly the exercise recurrence and coefficients 2,2,1. F additionally measures both source appends in their actual right association. `EQC.right_associated_appends` and `EQC.left_associated_appends` show why association and observation matter. |
| Difference-list value law versus application work. | Raw D-law worker semantics remain general. Work bounds require the declared finite construction or `AppCost` hypothesis. Empty represented output can have arbitrarily long composition history; `EDL.no_bound_from_output_length`, `EDL.expensive_capture` and `ENRO.charged_identity_changes_worker_work` retain this boundary. |
| Linear natural best case versus all-input operations. | Comparison scanning is always n−1, and sorted inputs avoid merge comparisons. The separate operational proof bounds the full scanner and actual zero/single-run dispatch. `ENRO.multiple_runs_outside_dispatch` prevents claiming the dispatch theorem covers a general operational merge. |
| Quicksort average assertions omitted from the exposition's analysis. | Both actual probability claims remain mandatory C02-024 content. Their distinct-key conditions, actual finite integrals, source recurrences, zero/one domains and duplicate quadratic families are retained. External cited papers are references, not whole-paper formalization goals. |
| Stability of reordered variants. | Exercise 2.7 selects the contiguous floor-left sorter with left-tie merge. `EAL.source_variant_not_stable` and `EBU.tail_sort_need_not_be_stable` prevent promoting ordinary correctness of reordered variants to stability. |

The source's displays (2.1)–(2.38), Lemmas 2.1–2.5, Corollary 2.6,
Lemmas 2.7–2.8, Theorem 2.9, Corollary 2.10, Lemma 2.11 and all seven exercises
are accounted for by the table. Displays (2.33)–(2.34) have the explicit
proof-premise disposition in C02-091. The source mutual-worker invariants and
nonempty/log side conditions are included even where the exposition omits them.

## Public exposure and validation boundary

`SquareApplications.lean`, the existing complete public entrypoint, includes
23 Chapter 2 example imports: the 21 example modules present as source at C,
plus `Examples.UniformQuickSortMean` and `Examples.RandomQuickSortGrowth`.
It preserves the existing imports for stable sorting, insertion costs, ordinary
merge, list/library/call/notation foundations, three-way partition, difference
lists and permutation Minimum/Order/Tail. Boundary modules remain reachable
through their existing main example imports. `ProofAudit.lean` already imports
`SquareApplications`; the chapter is exposed to that audit through this existing
dependency.

The source-only documentation reconciliation found all 112 IDs exactly once
and in order, and all 448 distinct explicit alias-qualified declaration
references in their exact source files. The public-entrypoint and audit import
closure contains 1,029 project source modules out of 1,085 tracked Lean files.
The remaining 56 tracked Lean files are exactly the unchanged historical,
experiment and script files outside those roots at accepted Chapter 1.
These are source/import counts, not checked-module or declaration-audit counts.
Static checks do not establish Lean elaboration, kernel auditing or a complete
candidate check. Historical focused and printed-type evidence is retained only
with explicit matching source identity; selected statement outputs do not
establish coverage of every public declaration in their source files.

Acceptance first requires the exact shared foundation and every included
shared unit's applicable gates in the recorded dependency order, including
XU01 before XU02 before XU03. The complete immutable Chapter 2 candidate then
requires all public coverage, matching checked statements and the README's
applicable normal-versus-fresh validation. Preserve the closed complete check,
exhaustive axiom audit and matching verification record; obtain independent
Standards and Spec outcomes with no unresolved findings; then run immediate
qualified `./check.sh --verify-candidate HEAD` before the authorized local
fast-forward. Local tickets stay local; no GitHub mutation or push follows
from this note. Chapter 3 and the remaining book scope retain their own
complete obligations and acceptance gates.

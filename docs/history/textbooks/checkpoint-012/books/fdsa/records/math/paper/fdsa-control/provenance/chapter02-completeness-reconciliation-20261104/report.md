# Chapter 2 completeness reconciliation at dfaf681

Date: 4 November 2026.

## Outcome and scope

All **112 obligations, C02-001 through C02-112**, are mapped below to their actual source destinations, checked standard-library reuse, authored statements, or explicit remaining gaps. This is a coverage reconciliation by the retained quicksort implementation author, with a read-only helper inventory of C02-089–107. It is **not** an independent Standards or Spec review, a new review hierarchy, a compiler run, an exhaustive proof audit, or acceptance.

The principal additional mathematical omission, beyond the known probability and operational work, is **C02-090: the general equality of arbitrary ordinary correct sorting functions**. The existing selected-algorithm equalities do not discharge that universally quantified corollary. Ordinary uniqueness itself, C02-089, is already supplied by the standard library under the weaker antisymmetry premise; it needs an explicit source/reuse disposition, together with C02-091's proof-step accounting.

The major known mathematical continuations remain C02-024's two distinct expectation/average claims and C02-111–112's connection from the actual ascending builders to complete scanner operational work. C02-088 remains partial because it includes those operational claims. The repeated ordinary-list construction claim C02-109 and the local closure-creation claim C02-110 already have substantive focused-checked destinations and should not be overlooked.

Public integration and the complete chapter reconstruction map are still outstanding. The exact snapshot also contains failed natural-sort composition proof scripts. A later, separately identified successor now passes all four natural-sort targets; that result is recorded in the final addendum and is not credited backward to different source bytes.

### Immutable identities

| Item | Exact identity |
| --- | --- |
| Assessed cumulative development snapshot | dfaf68114d1dda4e15628c94c3d988c3f5457c49 |
| Accepted Chapter 1 and full Chapter 2 review base, R | 07e480f6ec9958d4975bb90151005b84f2907614 |
| Pending shared foundation candidate used by development | f17cc6b1a2bf44215b16202ed0fcee2b5c130761 |
| Read-only author checkout | conaled-ch02-three-way, work/fdsa-ch02-three-way |
| Unchanged author HEAD | d4208023c1c30f5f15773b1f50a4d11db0a29e2c |
| Original 107-obligation inventory digest retained by the frozen requirements | edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d |
| Current 112-obligation inventory | 42,539 bytes; SHA-256 a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2 |
| Frozen requirements | 12,034 bytes; SHA-256 f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36 |
| Explicit scope clarification | research/scope-reconciliation.md; SHA-256 21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87 |
| Reuse plan | research/chapter02-reuse-plan.md; SHA-256 ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a |
| Merge-sort proof plan | research/mergesort-proof-plan.md; SHA-256 fa19bd92a19f06087da321bc7b4a18f337883bf3be63fe96b0e2da9b43cb2010 |
| Active-scope record | reviews/chapter02-active-scope.md; SHA-256 07bf70884d0076b64dd29642165cbcc267e1f4b33da5e00ac25e7da919a86a6b |
| Pinned primary book | July 27, 2026 edition; 1,742,029 bytes; SHA-256 9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645 |
| Supplied Chapter 2 text extraction | 34,713 bytes; SHA-256 6ce61b4bd1af76ec56bf4007be27f41c4c2bda12853292cc8d48cf3f1bd22cd4 |

Source reads used Git objects at the assessed snapshot, not a mutable central checkout. The inventory has exactly 112 unique obligation rows. The historical “Chapter 1 remains unaccepted” sentence in the originally frozen requirements is historical context; it does not undo R's recorded acceptance.

The report is the only filesystem artifact written for this assignment. No source file, ref, handoff, global tracker, dependency, cache, compiler output, or acceptance state is changed. The source/ref/build/cache hold remains in force.

## How to read the mapping

**Reuse** means a named existing theorem or definition already supplies the mathematics. **Focused** means the mapped source bytes match a secured successful module result, with any enclosing failed aggregate explicitly retained. **Authored/blocked** means the statement and proposed proof are present, but this snapshot lacks the required successful module result. **Partial** means a substantive part exists while a required mathematical connection is still absent. **Gap** identifies a missing required witness. **Explanatory** is used only where the frozen inventory permits a proof-step or notation disposition.

None of these labels accepts a Chapter 2 obligation. All rows still require their proper place in the final public candidate, the applicable complete check and exhaustive audit, both independent review axes, and immediate candidate verification.

The source abbreviations below make the 112-row table readable. A declaration written as “Q.quickSortBy_perm” means the exact declaration name quickSortBy_perm in Q's listed namespace and file. Example names are in the corresponding Examples namespace. Standard library names retain their List, Multiset, Nat, Int, or Real namespace.

| Alias | Exact snapshot source | Namespace |
| --- | --- | --- |
| S | Applications/Sorting/Sort.lean | Applications.Sorting |
| ST | Applications/Sorting/Stable.lean | Applications.Sorting |
| IO | Applications/Sorting/InsertionObservations.lean | Applications.Sorting |
| EIO | Examples/InsertionObservations.lean | Examples.InsertionObservations |
| IC | Applications/Resources/InsertionSort.lean | Resources.InsertionSort |
| EIC | Examples/InsertionCosts.lean | Examples.InsertionCosts |
| Q | Applications/Sorting/QuickSort.lean | Applications.Sorting |
| EQ | Examples/QuickSort.lean | Examples.QuickSort |
| QC | Applications/Resources/QuickSort.lean | Resources.QuickSort |
| EQC | Examples/QuickSortCosts.lean | Examples.QuickSortCosts |
| M | Applications/Sorting/Merge.lean | Applications.Sorting |
| SM | Applications/Sorting/SourceMerge.lean | Applications.Sorting |
| MC | Applications/Resources/ListMerge.lean | Resources.ListMerge |
| EMC | Examples/MergeCosts.lean | Examples.MergeCosts |
| TD | Applications/Sorting/TopDown.lean | Applications.Sorting |
| ETD | Examples/TopDownSorting.lean | Examples.TopDownSorting |
| TDC | Applications/Resources/TopDownSorting.lean | Resources.TopDownSorting |
| BU | Applications/Sorting/BottomUp.lean | Applications.Sorting |
| EBU | Examples/BottomUpSorting.lean | Examples.BottomUpSorting |
| BUC | Applications/Resources/BottomUpSorting.lean | Resources.BottomUpSorting |
| EBUC | Examples/BottomUpCosts.lean | Examples.BottomUpCosts |
| NR | Applications/Sorting/NaturalRuns.lean | Applications.Sorting |
| ENR | Examples/NaturalRuns.lean | Examples.NaturalRuns |
| NRC | Applications/Resources/NaturalRunComparisons.lean | Resources.NaturalRunComparisons |
| NS | Applications/Sorting/Natural.lean | Applications.Sorting |
| NSC | Applications/Resources/NaturalSorting.lean | Resources.NaturalSorting |
| AL | Applications/Sorting/Alternating.lean | Applications.Sorting |
| EAL | Examples/AlternatingSorting.lean | Examples.AlternatingSorting |
| TQ | Applications/Sorting/ThreeWayQuickSort.lean | Applications.Sorting |
| ETQ | Examples/ThreeWayQuickSort.lean | Examples.ThreeWayQuickSort |
| P | Applications/Sequences/Partition.lean | Sequences.Partition |
| RP | Applications/Resources/RandomQuickSort.lean | Resources.RandomQuickSort |
| ERP | Examples/RandomQuickSort.lean | Examples.RandomQuickSort |
| LB | Applications/Resources/ListBuildCosts.lean | Resources.ListBuildCosts |
| ELB | Examples/ListBuildCosts.lean | Examples.ListBuildCosts |
| DL | Applications/Resources/DifferenceListCosts.lean | Resources.DifferenceListCosts |
| EDL | Examples/DifferenceListCosts.lean | Examples.DifferenceListCosts |

Standard insertion and ordinary uniqueness reuse is in the pinned Mathlib/Data/List/Sort.lean. Multiset.coe_eq_coe is in Mathlib/Data/Multiset/Defs.lean. List.Pairwise and its nil/cons/append/map observations are the existing Lean/Mathlib interfaces, not a new chapter-specific sorting predicate.

## Validation ledger

All provenance paths in this report are relative to fdsa-control. The source files assigned to each historical component below were compared byte-for-byte with dfaf681. Matching source bytes permit reuse of that component's historical evidence; they do not turn its whole historical candidate check into a check of the cumulative snapshot.

| Evidence key | Secured evidence and exact scope | Current interpretation |
| --- | --- | --- |
| R | Accepted 07e480f6ec9958d4975bb90151005b84f2907614. ST, S, SM and Examples/StableSorting.lean match R exactly. | Existing accepted interfaces and clients may be reused. This does not accept new Chapter 2 source. |
| F | chapter02-foundation-focused-attempt3/result.json, candidate f17cc6b1a2bf44215b16202ed0fcee2b5c130761: six focused targets, exit 0, 4.528108022 s, clean unchanged HEAD. Log SHA-256 c7ad375385228d3bd1fc17d6b781de382147639eac4ecd2ec7b9618b4ac3de60. | IC, EIC and ListCalls source match. Both shared-foundation independent source assessments report zero concrete findings but retain blocked overall outcomes pending full validation. The focused record's inherited verification-file presence is not a full verification of this foundation. |
| V | chapter02-values-focused-attempt5/result.json, b1677172ef85e40865fe8f292660c1bcfd6e5a0c: IO, EIO, TD and ETD all pass, exit 0, clean unchanged HEAD. Log SHA-256 4cf4f468133e536a67a4ccafeb419e2668007eddd50430f1bb764fc225c36596. | All four source files match. Existing insertion/top-down implementation handoffs supply source assessments; later focused evidence supersedes their historical “uncompiled” state only for these bytes. |
| QV | chapter02-quicksort-focused-20261104-attempt3/result.json, 840252e63026bba5eab109f2b16468deef7670ec: Q and EQ pass, exit 0. Log SHA-256 180c8d88e0df68f41ef5941dcb78f99d9ddd97097e7469f0842d4cbd8e610538. The corresponding statements record also exits 0, log SHA-256 e752dc669d2987d02b11270211f978fd5bb575b4566233fbfbfbe3b7e81bc440. | Both files match; retained author readback covers source recurrence, generality and arbitrary suffix. |
| XM | ordinary-merge-focused-20261104-attempt3/result.json, 72a0951aee406f7db67998d2a3bf8810f4e1bccc: M, MC and EMC pass, exit 0, 31.375937590 s. Log SHA-256 2898f1aef4e952cffdcc64fc4ac449bea3d105dc90f02f2706b8d97772c5f5a1. Its 17-name type inspection exits 0. | All three files match. Independent XM01 Standards and Spec source assessments are complete with zero concrete findings, overall blocked pending complete integrated validation. |
| TC | chapter02-top-down-costs-focused-20261104-attempt3/result.json, 7fb7c3ed47b5b1ae6c378227928f7da7d67f1cb0: TDC and Examples/TopDownCosts.lean pass, exit 0, 51.550620786 s. Log SHA-256 c2e18c5ccdac8983e39d96cc66094803bf6083f344ec96095b81433b6f1935d3. Its 32-name inspection exits 0. | Both source files and Growth match. The summary records the author's elaborated-statement assessment, not independent final approval. |
| BV | chapter02-bottom-up-focused-20261104-attempt5 and chapter02-bottom-up-alternating-focused-summary.json, 98696d86162bd93c1cba46719eeb65bf6cabe65a: BU, EBU, AL and EAL pass, exit 0, 17.480759210 s. Log SHA-256 cab1074b263d717c9f70b2cdfba694fddd43f282b853f74bfcbb83ebc7e63983. Combined 126-name inspection exits 0. | All four files match. Recorded readbacks distinguish 87 BottomUp author-assessed and 39 Alternating root-assessed declarations. |
| BC | chapter02-bottom-up-costs-focused-20261104-attempt4/result.json, 6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b: BUC and EBUC pass, exit 0, 142.193826109 s. Log SHA-256 44df874a8351b38a24f564fe4a7ebfe0b3ff9289fdf393b367a8e654fc76a6a2. All 105 type checks pass; type log SHA-256 b77970fe06b930f34286bcdb0e9a9ce1bdfbffceb2cdaf7f213cdf501137493d. | Both files match. chapter02-bottom-up-costs-types-20261104/author-readback.md assesses all 76 resource and 29 example declarations, zero concrete author findings. |
| NV | chapter02-natural-runs-focused-20261104-attempt4/result.json, ff9749d1ccbcb0949486f67d6273e28c262280e0: NR and ENR pass, exit 0, 10.001259646 s. Log SHA-256 96a4eb0e28f302521d3974ac4add552739593d58ad2d01c8dedf5e0a476eddce. Statement inspection exits 0, log SHA-256 bcde796041ddae8ec96f0e13e3231501cf9170f8cded41dc9565b54a8fc1af31. | Both files match. Source/author statement assessment retained. |
| MS | chapter02-measured-sorting-focused-20261104-attempt2 at 841413dc6b1e332ba07063fb62e66dea0802ab37 individually passes QC, EQC, NRC and Examples/NaturalRunComparisons.lean. **Aggregate exit 1** from ListBuildCosts; log SHA-256 a8367b26cf50c6f2ad762e19d54d4455338f60b9615a09bb42c0688d17850f68. | These individual successful targets are credited accurately; the failed aggregate is not changed to a pass. |
| LBV | LB passes after its proof repair; ELB passes in chapter02-list-builder-partition-focused-20261104-attempt1 at 1ffb61fceaf7c893e25a35339f6e1fce8531021d. **Aggregate exit 1** from Resources.Partition; log SHA-256 198c25aeb96b9670b00a42d3febe92ef326019af210a954a66a35f95394a4154. | Both final list-builder source files match. Their pass is an individual-target result, not the aggregate outcome. |
| MT | chapter02-measured-sorting-types-20261104 at 1ffb61fceaf7c893e25a35339f6e1fce8531021d: all 174 checks pass, exit 0, 45.322615910 s. Log SHA-256 607eba97643a8361295857fb0777248e018534e0a7a78ed7d49760834f3ae325. | Matching QC/EQC, NRC/examples and LB/ELB bytes. Complete author readbacks cover 83 quicksort and 91 natural-scan/list-builder declarations, zero concrete findings. These are declaration inspections, not whole-project audit counts. |
| TQV | chapter02-variants-xd01-focused-20261104-attempt1 at 4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9 individually passes TQ and ETQ; **aggregate exit 1** from unrelated XD01/random examples. Log SHA-256 bd000490148fe78ad1f67dfd0f1eb38c05aa9ecd3212ea58ac038e15622947fa. Its combined 84-name partition/three-way inspection exits 0. | TQ and ETQ match. Complete 36-declaration author readback is three-way-author-readback.md in the type provenance; the other 48 partition/legacy declarations have a separate root readback. No independent final approval is inferred. |
| N0 | chapter02-natural-xd01-focused-20261104-attempt1 at e2db54211dfe3b2efd76904f1797a9460567ebbc, **exit 1**, 27.319240105 s, clean unchanged HEAD. Log SHA-256 057996ba9c497d0821e21cb47efad8b7eda3a2a8db26b7f112259adf77e0983f. | All four natural composition files in dfaf681 match this attempt. NS itself built; Examples/NaturalSorting failed, NSC failed, and its dependent examples were not established. The 105-declaration root readback is explicitly source-only. Do not give these bytes the later successor's module result. |
| XR | chapter02-xd01-random-focused-20261104-attempt4 at **dfaf681**: DL, EDL, RP and ERP all pass, exit 0, 9.201865451 s, clean unchanged HEAD. Log SHA-256 514c8e71be97d10be7bb0c181e2dc3605423186b0adbfc085c122f63bee0896a. | Exact snapshot evidence. Attempt 3's wrong resource-module target and aggregate failure are retained; corrected invocation attempt 4 is the successful record. |
| XT | chapter02-xd01-random-types-20261104 at **dfaf681**: all 134 checks pass, exit 0, 13.325960255 s. Log SHA-256 5027831298792411bde1622e6ad00aef816a0f0f41c97e372139eb8a47afe182. | Complete root readback of the 72 XD01 declarations is recorded in xd01-root-readback.md/json, zero findings. The 62 random declarations have successful explicit type output; no expectation theorem follows from that output. |

The root's qualified native kit, exact pins and one-thread profile apply to these retained executions. No new validation command was run for this report. The pending full foundation check and all later full-candidate gates remain separate.

## All 112 obligations

### Specification and insertion: C02-001–016

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-001 | Standard LinearOrder, LE/LT and their reflexive/transitive/antisymmetric/total laws; S.sortOn_correct and the book specializations of Q.quickSortOn_correct, TD.sortFloorOn_correct. Generic operations retain weaker input-local or relation-specific laws. | Reuse R, focused V/QV. Record the standard order correspondence in the final chapter map; no new carrier or blanket stronger comparator premise is needed. |
| C02-002 | ST.KeySorted id is List.Pairwise (· ≤ ·); List.pairwise_nil and List.pairwise_cons give exactly the source nil and head/all-tail recursion. The source proofs repeatedly use that interface. | Reuse R and checked clients. Explicit correspondence belongs in the map; adjacent-only sortedness is not substituted. |
| C02-003 | Ordinary contracts use KeySorted plus List.Perm; Multiset.coe_eq_coe converts the source multiset equality without losing duplicates. S.sortOn_correct, Q.quickSortOn_correct, TD.sortFloorOn_correct and EIO.keyed_sort_observations are concrete destinations. | Reuse/focused R/V/QV. The always-empty illustration is explanatory: sortedness alone cannot preserve a nonempty input's multiset. No replacement sorting-spec structure is required. |
| C02-004 | List.orderedInsert, orderedInsert_nil and orderedInsert_cons; EIO.keyed_insert_equations specialize the source non-strict left-tie test. | Reuse plus focused V. Exact source recurrence retained. |
| C02-005 | List.insertionSort is the right fold of orderedInsert; insertionSort_nil and insertionSort_cons, exposed by EIO.keyed_sort_equations. | Reuse plus focused V. Recursive insertion consumes the actual recursively sorted tail. |
| C02-006 | List.perm_orderedInsert and Multiset.coe_eq_coe; EIO.keyed_insert_observations explicitly proves the full-record inserted multiset equality. | Focused V over standard reuse. Multiplicity is retained. |
| C02-007 | List.perm_insertionSort; S.insertionOn_spec.perm and EIO.keyed_sort_observations expose source multiset preservation. | R/V. No support-only substitute. |
| C02-008 | List.mem_orderedInsert and EIO.keyed_insert_observations give membership iff equality with the new element or membership in the input. | Reuse/focused V. Exact support law present. |
| C02-009 | IO.pairwise_orderedInsert_iff; separately IO.pairwise_of_orderedInsert gives the law-free converse, even for a separately observed relation. EIO.keyed_sorted_iff is the mapped-key source form. | Focused V. Totality/transitivity support the forward direction; antisymmetry and payload equality are unnecessary. |
| C02-010 | List.pairwise_insertionSort, S.insertionOn_spec.sorted and EIO.keyed_sort_observations. | R/V. Whole insertion-sort sortedness is present with full occurrence preservation separately. |
| C02-011 | IC.insertRun defining nil/cons equations count one entry, including the terminal call; insertRun_value ties that execution to canonical insertion. | Focused F. Foundation acceptance still pending; no copied cost executor is introduced. |
| C02-012 | IC.sortRun and sortRun_cons_cost sequence the actual returned sorted tail into insertRun, charging the source sort entry. | Focused F. Not a recurrence evaluated at the unsorted tail. |
| C02-013 | IC.insertRun_cost_bounds proves 1 ≤ cost ≤ input length + 1 for arbitrary decidable insertion relation. | Focused F; no sorting or global order premise. |
| C02-014 | List.orderedInsert_length; EIO.keyed_insert_observations includes the source length-plus-one statement. | Reuse/focused V. |
| C02-015 | List.perm_insertionSort.length_eq and IC.sortRun_length after erasure. | Reuse and focused F. Applies to the actual sort result. |
| C02-016 | IC.sortRun_quadratic proves the printed bound (length + 1)^2; EIC.source_quadratic applies it. Stronger triangular bounds remain separate. | Focused F. The whole source cost obligation remains subject to the foundation/full chapter gates. |

### Two-way quicksort: C02-017–024

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-017 | Q.quickSortBy, quickSortBy_nil/cons/singleton; Q.quickSortOn_cons specializes the first held pivot, strict-less tail filter and complementary greater-or-equal tail filter. Termination is by tail-filter length; the literal append association is retained. | Focused QV. No pivot-in-tail or distinctness premise. |
| C02-018 | Q.quickSortBy_perm plus EQ.source_multiset gives exact occurrence/multiset preservation for every comparator and input. | Focused QV. |
| C02-019 | EQ.source_filter_multiset uses Multiset.filter_coe for the exact list-to-multiset filter correspondence. | Focused QV. This required helper has an explicit checked source client. |
| C02-020 | EQ.source_complementary_multiset retains the input-local complement hypothesis; EQ.source_key_partition specializes strict-less/greater-or-equal for lawful keys. | Focused QV. Duplicate occurrences are partitioned, not removed. |
| C02-021 | EQ.source_sorted_append gives the exact Pairwise/KeySorted append iff: both pieces sorted and every left element precedes every right element. | Focused QV; only the relation needed to state the observation is imposed. |
| C02-022 | Q.mem_quickSortBy and EQ.source_support give equality of support; quickSortBy_length supplies the size consequence separately. | Focused QV. Does not replace permutation. |
| C02-023 | Q.quickSortBy_sorted_compatible_on uses transitivity plus compatibility only on members of the actual input; quickSortOn_correct is the lawful-key source specialization. | Focused QV. No unnecessary laws on arbitrary payloads. |
| C02-024 | Deterministic prerequisites: QC.run, exerciseCost_eq_partitionMass, exerciseCost_le, literalCost_le_twice, costs_of_sorted, costs_of_strict_descent and costs_replicate. Random execution: RP.uniformIndex, run/runOn, exerciseLaw_cons, support-finiteness and correctness/bounds; ERP checks exact small probability masses and all-equal quadratic cost. | **Partial**, focused MS/MT/XR/XT. Neither the uniform-permutation average theorem nor the conditional uniform-occurrence-pivot expected O(n log n) theorem is present. Required mean/recurrence/rank or equivalent bridges, the uniform-input execution transport, and the asymptotic proof remain. Finite masses and support bounds are not expectations. Preserve distinct-key hypotheses, separate probability models and any separately claimed pivot-selection/removal overhead. |

### Ordinary merge and floor-left top-down sorting: C02-025–039

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-025 | SM.sourceMerge defining equations, sourceMerge_eq_merge and mergeBy_source connect the source non-strict left-tie merge to canonical List.merge; MC.run_value and EMC.source_value connect measured execution to that same source value. | Reuse R plus focused XM. |
| C02-026 | TD.sortFloorBy, sortFloorBy_of_length_le, sortFloorBy_step, nil and singleton laws implement take/drop at floor(length/2), preserving the source ≤1 base. ETD.source_three_split checks the odd split. | Focused V. The standard library's different odd split is not substituted. |
| C02-027 | SM.sourceMerge has a sum-of-lengths decrease. TD.sortFloorBy proves both source half lengths strictly decrease only in the length > 1 branch. | R/V. Checked definitions carry the required termination arguments. |
| C02-028 | List.merge_perm_append and M.mergeBy_perm; MC.run_value plus EMC.result_multiset yield the source sum of input multisets. | R/XM. Exact source/value bridge present. |
| C02-029 | The same permutation yields union membership; EMC.result_mem states the actual result's membership iff, with MC.run_value and SM.sourceMerge_eq_merge supplying the source form. | Focused XM. No order premise. |
| C02-030 | TD.sortFloorBy_perm and Multiset.coe_eq_coe; ETD.full_multiset retains repeated values under an arbitrary comparator. | Focused V. Generic permutation covers all inputs, not only the concrete fixture. |
| C02-031 | M.sublist_merge_left/right and pairwise_of_merge provide the law-free converse. M.merge_sorted_compatible_on_iff supplies the input-local iff; EMC.source_key_sorted_iff explicitly states the source/key specialization. | Focused XM. The converse is implemented, not merely planned. |
| C02-032 | TD.sortFloorBy_sorted_compatible_on and sortFloorOn_correct give source sortedness with raw local compatibility and a lawful-key specialization. | Focused V. |
| C02-033 | MC.run, comparisons, comparisons_nil_left/right and comparisons_cons_cons give actual selected-branch merge comparison equations. The separate entries projection is not charged to this source counter. | Focused XM. Comparison and function-entry metrics are distinguished. |
| C02-034 | TDC.run and comparisons_step sequence both measured source children, then MC.run on their actual returned sorted lists. run_value separately proves erasure. | Focused TC. No recurrence on unsorted halves or value-only cost transfer. |
| C02-035 | List.merge_perm_append.length_eq and EMC.result_length; SM/MC erasure gives the source merge length sum. | R/XM. |
| C02-036 | TD.sortFloorBy_length and TDC.run_length give the source sorter length. | Focused V/TC. |
| C02-037 | MC.comparisons_le proves comparisons ≤ left length + right length for all inputs, with no sortedness premise. | Focused XM. This is the prescribed loose source bound, distinct from entries_le. |
| C02-038 | TDC.comparisons_le_of_length_pow proves C ≤ k·2^k when length = 2^k; comparisons_le_clog proves the stronger all-length ceiling-log statement. Examples/TopDownCosts.power_zero_boundary retains k = 0. | Focused TC and 32-name statement inspection. |
| C02-039 | TDC.comparisons_le_real_log_of_length_pow is the source real-log corollary with the power-of-two premise retained. The general comparisons_isBigO uses the separately proved growth bridge. | Focused TC. No rounding or zero-domain premise is hidden by coercion. |

### Ordinary bottom-up sorting: C02-040–057

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-040 | BU.mergePairsBy and its nil/singleton/step equations implement adjacent pairs and retain the final odd run unchanged. | Focused BV. |
| C02-041 | BU.mergePairsBy_length is the ceiling-half run-count law; mergePairsBy_length_lt gives strict decrease for at least two runs. | Focused BV. Ordinary and accumulator-style source names are distinguished. |
| C02-042 | BU.mergeAllBy with nil/singleton/step laws repeats the actual pass and terminates by decreasing outer length. | Focused BV. |
| C02-043 | BU.sortBottomUpBy maps each input occurrence to a singleton run and calls mergeAllBy. Nil/singleton laws expose the boundaries. | Focused BV. |
| C02-044 | BU.multiset_flatten_eq_sum is the explicit flatten-to-sum-of-inner-multisets bridge. | Focused BV. No set approximation. |
| C02-045 | BU.mergePairsBy_flatten_perm and mergePairsBy_multiset preserve the flattened input multiset. | Focused BV. |
| C02-046 | BU.mergeAllBy_perm and mergeAllBy_multiset preserve the sum of initial run occurrences. | Focused BV. |
| C02-047 | BU.sortBottomUpBy_perm and sortBottomUpBy_multiset preserve the source input multiset. | Focused BV. |
| C02-048 | BU.mergePairsBy_sorted_compatible_on preserves per-run sortedness using input-local comparator compatibility. | Focused BV. Empty and ragged runs are allowed. |
| C02-049 | BU.mergeAllBy_sorted_compatible_on proves whole-result sortedness from individually sorted input runs. | Focused BV. |
| C02-050 | BU.sortBottomUpBy_sorted_compatible_on and sortBottomUpOn_correct provide the ordinary source sorter correctness. | Focused BV. No universal stability claim is inferred. |
| C02-051 | BUC.pairsRun and pairsComparisons_nil/singleton/step perform actual measured merges and the subsequent pass recursion. | Focused BC, complete author/type assessment. |
| C02-052 | BUC.allRun, allComparisons_nil/singleton/step and allRun_value recurse on the actual measured pass result. | Focused BC. |
| C02-053 | BUC.run, comparisons and comparisons_eq_all use the singleton initialization with no unstated map/entry charge in the comparison-only model. | Focused BC. |
| C02-054 | BU.mergePairsBy_uniform_length proves output length 2m under an even input run count and uniform input length m. | Focused BV. Evenness is explicit; odd-leftover counterexamples remain in the examples. |
| C02-055 | BUC.pairsComparisons_le_uniform proves the m·run-count bound without an evenness assumption; pairsComparisons_le handles arbitrary ragged runs. | Focused BC. |
| C02-056 | BUC.allComparisons_le_uniform_pow proves m·k·2^k under uniform inner length m and outer length 2^k. | Focused BC. m = 0 and k = 0 are retained. |
| C02-057 | BUC.comparisons_le_of_length_pow proves k·2^k for the actual singleton-initialized sorter; EBUC.sorter_power_zero checks the exponent-zero boundary. | Focused BC. Real-log/asymptotic bounds are additional checked consequences, not replacements for this exact source form. |

### Natural-run values and worker laws: C02-058–070

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-058 | NR.runsBy with nil/singleton/cons_cons equations chooses descending exactly when the next key is strictly smaller; otherwise it enters ascending. | Focused NV. The source mutual recurrence and restart behavior are preserved. |
| C02-059 | NR.ascBy and its equations implement the source ascending worker with Batteries.DList; ascSourceBy_nil/cons expose the raw lawful-function recurrence. Equal adjacent keys stay ascending. | Focused NV. Arbitrary D-law source builders are retained. |
| C02-060 | NR.descBy_nil/cons implements strict descent, accumulating by cons and emitting the reversed descending run at its stopping point. | Focused NV. Weak descent with ties is not treated as one reversed run. |
| C02-061 | NR.DListLaw, dListLaw_iff, dListLaw_cons, DListLaw.push, dListOfLaw and its application/toList/push laws connect raw source functions to Batteries.DList. dList_apply_eq and dList_push_apply expose the append-order laws. | Focused NV. These are semantic identities; no arbitrary-builder runtime follows from D alone. |
| C02-062 | The actual mutual definitions carry length-based termination measures; mutual perm/nonempty/length/sortedness proofs follow their source calls, including worker-to-runs restart. | Focused NV. Existing Lean mutual recursion/induction machinery is the correspondence; no additional induction framework is required. |
| C02-063 | NS.sortNaturalBy and sortNaturalBy_eq_mergeAll are exactly mergeAllBy applied to the actual runsBy output. | **Focused core N0**. NS built even though its enclosing attempt failed; its example file at this snapshot did not pass. |
| C02-064 | NR.ascSourceBy_perm gives arbitrary raw D-law prefix/current/tail occurrence preservation; ascBy_multiset and Multiset.coe_eq_coe expose the corresponding multiset sum using f [] as prefix. | Focused NV. Arbitrary lawful builders, not only builders generated from empty input, are covered. |
| C02-065 | NR.descBy_perm and descBy_multiset preserve the arbitrary accumulator, current element and tail occurrences. Reverse in the permutation form does not alter the accumulator multiset. | Focused NV. No sorted accumulator is needed for occurrence laws. |
| C02-066 | NR.runsBy_perm and runsBy_multiset preserve every input occurrence through the emitted run list. | Focused NV. |
| C02-067 | NS.sortNaturalBy_perm and sortNaturalBy_multiset compose runs preservation with the actual bottom-up merger. | **Focused core N0**; complete natural composition examples at dfaf681 remain blocked. |
| C02-068 | NR.runsBy_sorted_compatible_on and runsOn_sorted prove every emitted run sorted, with input-local compatibility or lawful keys respectively. | Focused NV. They do not falsely assert that concatenating the runs is already globally sorted. |
| C02-069 | NR.ascBy_sorted_compatible_on, descBy_sorted_compatible_on and ascSourceBy_sorted retain the actual prefix/accumulator sortedness and upper/lower-bound invariants. ENR's unsorted builder and missing-bound examples test their necessity. | Focused NV. Arbitrary semantic workers retain their generality; stability is not asserted for arbitrary descending accumulators with equal keys. |
| C02-070 | NS.sortNaturalBy_sorted_compatible_on and sortNaturalOn_correct combine run sorting with mergeAllBy sorting. | **Focused core N0**. The pure correctness module passed; its independent examples and measured extension at this snapshot did not. |

### Natural comparisons and general merge bounds: C02-071–088

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-071 | NRC.runsCountBy, ascCountBy and descCountBy with all source equations; actual runsRunBy/ascRunBy/descRunBy and their spec/value/cost laws connect those scalar counts to selected-branch executions. | Focused MS/MT. Comparison-only tariff, including zero base cases, is explicit. |
| C02-072 | NSC.run and comparisons_eq_scan_add_merge sequence actual measured scanning into BUC.allRun on the returned runs; comparisons_eq_length_add_merge uses the exact scan count. | **Authored/blocked N0** at dfaf681. A complete module result is missing for these exact proof bytes; successor evidence is separate below. |
| C02-073 | BUC.pairsComparisons_le proves pass comparisons ≤ total flattened input length for arbitrary run lists. | Focused BC. No uniform-length, nonempty-run or evenness premise. |
| C02-074 | BU.mergePairsBy_flatten_length, equivalently mergePairsBy_sum_lengths, preserves the total length used in the comparison bound. | Focused BV. |
| C02-075 | BUC.clog_two_source_half and clog_two_ceil_half prove the source half-count recurrence for n ≥ 2. int_ceil_logb_two_nat and int_ceil_logb_two_source_half supply the exact totalized real-log/integer-ceiling correspondence. | Focused BC. The zero/one ceiling cases have checked examples; positivity is retained only where the recurrence needs it. |
| C02-076 | BUC.allComparisons_le_clog and allComparisons_le_int_ceil give flattened-length times ceiling-log run count, including empty/one-run and empty-inner-run cases. | Focused BC. |
| C02-077 | NR.ascBy_flatten_length and ascSourceBy_flatten_length give current + represented prefix + tail length, retaining the raw D-law bridge. | Focused NV. |
| C02-078 | NR.descBy_flatten_length gives current + accumulator + tail length for arbitrary accumulator. | Focused NV. |
| C02-079 | NR.runsBy_flatten_length preserves the source input length. | Focused NV. |
| C02-080 | NR.ascBy_length_le bounds the number of output runs by tail length + 1, independently of the builder prefix size; ascSourceBy is the exact raw-builder bridge. | Focused NV. ENR.arbitrary_builder_run_bound checks a nonempty seed. |
| C02-081 | NR.descBy_length_le gives the same tail length + 1 run-count bound for arbitrary accumulator. | Focused NV. |
| C02-082 | NR.runsBy_length_le proves run count ≤ input length, including empty input. | Focused NV. |
| C02-083 | NRC.ascCountBy_le and ascRunBy_cost_exact prove the printed upper bound and stronger exact tail-length identity. ascSourceRunBy_cost covers a raw D-law builder. | Focused MS/MT. Builder construction/materialization is deliberately outside this comparison count. |
| C02-084 | NRC.descCountBy_le and descRunBy_cost_exact give the upper bound and exact tail-length comparison identity. | Focused MS/MT. No order premise is needed for the comparison count itself. |
| C02-085 | NRC.runsCountBy_le, runsCountBy_exact and runsRunBy_cost_exact give comparisons = length − 1 with truncated Nat subtraction. | Focused MS/MT. Empty and singleton count zero. |
| C02-086 | NSC.comparisons_le_source, comparisons_le_of_length and comparisons_le_int_ceil/of_length state the exact source bound n + n·ceiling(log₂ n); the adaptive/clog variants are stronger intermediate statements. | **Authored/blocked N0** at dfaf681. Required integer/real coercions are present in source; validation of those exact module bytes is not established. See the separate passing successor. |
| C02-087 | NR.runsBy_nonempty, ascBy_nonempty, descBy_nonempty, ascBy_ne_nil, descBy_ne_nil and runsBy_eq_nil_iff supply positivity/nonempty facts. BUC's ceiling bridge and standard Nat.clog monotonicity support the final source bound. | NV/BC helpers focused. Their final NSC application is authored/blocked N0 at this snapshot; zero is handled separately rather than hidden behind a positive-log premise. |
| C02-088 | Best-case value/scan ingredients: NR.runsOn_of_sorted, NRC.runsRunBy_of_sorted and exact counts. Composition/comparison claims occur in NSC; ordinary building and closure creation are LB/DL. | **Partial**. C02-108's comparison composition is authored here and checked at the later successor; C02-109/110 have focused destinations. C02-111/112's actual source-builder/operational connection is still absent. The umbrella cannot be closed from comparison correctness alone. |

### Ordinary uniqueness, keys and stability: C02-089–098

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-089 | List.Perm.eq_of_pairwise' under Std.Antisymm, together with Multiset.coe_eq_coe, supplies ordinary source uniqueness. ETD.source_three_value and the QV/BV/TQV examples are checked applications. | **Reuse**, with focused clients. Explicitly document this ordinary theorem and multiset bridge in the chapter map. ST.StableSort.unique has a different keyed/stability contract and is not a replacement. |
| C02-090 | S.sortOn_eq_insertionOn and TD.sortFloorOn_eq_sortOn cover only selected algorithms. No declaration at dfaf681 states both pointwise and function equality for arbitrary ordinary correct sorters f and g. | **Gap: general Corollary 2.10 witness missing.** Derive it from C02-089 plus function extensionality, retaining ordinary sortedness/permutation or multiset specifications and no unjustified stability premise. |
| C02-091 | Displays (2.33) and (2.34) are premises in the proof of ordinary uniqueness; the standard theorem's proof is the reuse destination. | **Explanatory**. Add an explicit disposition with C02-089; do not create two unnecessary public theorems or turn proof premises into extra sorting assumptions. |
| C02-092 | ST.KeySorted, Stable and StableSort; List.pairwise_map and EIO.keyed_sort_observations connect mapped-key sortedness, full-record multiset preservation and exact equal-key filtered subsequences. | R/V. Payloads need no order or decidable equality. |
| C02-093 | S.insertionOn plus EIO.keyed_insert_equations and keyed_sort_equations are the source keyed insertion and tail-first/right-fold sort definitions. | R/V. Non-strict tie direction preserved. |
| C02-094 | EIO.keyed_insert_observations and keyed_sorted_iff; IO.pairwise_orderedInsert_iff and law-free pairwise_of_orderedInsert; EIO.keyed_sort_observations for whole-sort multiset/mapped sortedness. | Focused V over accepted interfaces. All specified observations are present, including the converse. |
| C02-095 | IO.orderedInsert_eq_cons_of_forall proves immediate insertion from the source all-members premise; EIO.all_members_without_sorted_input tests an unsorted tail. | Focused V. No sorted-input or global-law requirement. |
| C02-096 | IO.filter_orderedInsert_of_neg proves the negative filter law under p a = false, for any decidable insertion relation; EIO.signed_negative_step connects the actual sorted-tail proof use. | Focused V. No sortedness premise is added. |
| C02-097 | IO.filter_orderedInsert_of_pos and EIO.keyed_filter_of_pos retain p a = true, transitivity, and sortedness under the same relation. EIO.positive_filter_needs_sorted_input checks the omitted-hypothesis boundary. | Focused V. Totality and antisymmetry are not required for this helper. |
| C02-098 | S.insertionOn_spec and EIO.keyed_sort_observations provide exact equal-key filtering. EIO.signed_tail_fixed, signed_negative_step and signed_positive_step connect the displayed helper argument to actual recursive tails. | R/V. Existing stability reuse does not erase the independently implemented C02-095–097 obligations. |

### Exercises: C02-099–107

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-099 | IC.sortRun_cost_of_pairwise attains 2·length + 1 on sorted input; sortRun_cost_lower is the global lower bound. EIC.sorted_with_duplicates and best_is_global are connected clients. | Focused F. Terminal and recursive calls are counted at the actual execution. |
| C02-100 | IC.reverse_range_opposite, sortRun_double_cost_of_opposite and sortRun_cost_reverse_range attain (n+1)(n+2)/2 on reverse(range n); sortRun_double_cost_le and sortRun_cost_le give the global upper bound. | Focused F. Preserve the documented indexing convention: range n contains n values. Strict opposite ordering, not arbitrary repeated descent, attains the full traversal family. |
| C02-101 | Q.quickSortAccBy is the append-free suffix worker; quickSortAccBy_eq_append holds for every suffix and arbitrary comparator. quickSortAccOn_cons/eq_append/correct give the source keyed form. QC.accumulatorRun_exact/eq_append/cost_independent connect its actual measured execution. | Focused QV/MS/MT. No sorted-suffix premise; empty-suffix equality alone is not substituted. |
| C02-102 | TQ.threeWayQuickSort implements three tail filters, recursing only on strict less/greater, retaining one held pivot plus the entire equal block. Its cons/cons_partition/perm/multiset/sorted/correct/replicate laws and ETQ's independent cases cover the exercise. | Focused TQV. Shared P.partition3_eq_filters is a value bridge, not a cost identity. No Nodup, pivot-in-tail, positivity, finite-type or inhabitance premise. |
| C02-103 | QC.exerciseCost_cons_source/cons_on preserve the supplied two-filter tariff; exerciseCost_le proves 2n²+2n+1 globally and costs_of_sorted attains it, including weakly sorted duplicate inputs. Literal appendCost/literalCost are separately executed and bounded. | Focused MS/MT. Both source append occurrences and their right association are preserved in the separate metric. |
| C02-104 | AL.halve is the actual alternating accumulator pass. halve_perm, halve_lengths, halve_balance, halve_empty_balance and halve_strict give occurrence/length/balance/decrease laws. sortAlternatingBy and sortAlternatingOn_correct use its returned halves. EAL.source_halve_example is [2,3,4] with ([0],[1]) giving ([4,2,0],[3,1]). | Focused BV. No false stability or invented numerical time formula. Arbitrary starting accumulators remain in the splitter laws. |
| C02-105 | BU.mergePairsRevBy is the append-free tail pass; mergeAllRevBy and sortBottomUpRevBy repeat it and prove ordinary correctness. BUC.pairsRevComparisons_eq proves exact per-pass equality; allRevComparisons_le_clog/uniform_pow and revComparisons bounds prove the complete requested complexity. | Focused BV/BC. Complete ordinary/reversed tree totals can differ; same complexity does not assert equality of those totals or stable tail sorting. |
| C02-106 | BU.mergePairsRevBy_eq_reverse_append and its length/flatten_perm/flatten_length/multiset laws account for arbitrary accumulator; mergeAllRevBy_multiset covers repeated merging. BUC.pairsRevRun_value/eq and pairsRevComparisons_eq concern the actual pass. | Focused BV/BC. Source's premature accumulator-style names are explicitly separated from C02-041/045/046's ordinary pass. |
| C02-107 | Selected non-insertion algorithm: TD.sortFloorBy with contiguous floor-left split and left-tie merge. sortFloorOn_correct/stable/spec prove correctness and stability; ETD.arbitrary_payload_order, stable_across_split and full_multiset connect the source algorithm to exact observations. | Focused V. TD.sortFloorOn_eq_sortOn is a value bridge. The selected exercise is substantively implemented; final documentation must name the choice and must not infer stability for alternating/reversed variants. |

### Explicit best-case and operational clarification: C02-108–112

| ID | Actual destination and source correspondence | Validation and remaining work |
| --- | --- | --- |
| C02-108 | NR.runsOn_of_sorted gives the single run for nonempty sorted input. NRC's three exact counts and runsRunBy_of_sorted give scan n−1. NSC.mergeComparisons_of_sorted, run_of_sorted, comparisons_of_sorted and comparisons_lower give zero merge work, exact best count and global lower bound; empty/singleton laws retain zero. | **Partial validation at dfaf681:** NV/MS/MT ingredients pass; NSC is authored/blocked N0. The later natural successor passes all four modules. Linear eventual comparison statements retain the n = 0/1 boundaries and do not imply complete scanner operational work. |
| C02-109 | LB.appendSubRun_empty_cost gives n(n+1)/2; appendLoopRun_cost and appendBuildRun_cost expose loop/wrapper entries. consReverseBuildRun_value/cost gives the same ordered result with 2n+3 work; realizations_agree and quadratic_lower/upper/linear_upper provide the resource comparison. ELB checks order, duplicates, nonempty seeds and empty payloads. | Focused LBV/MT. Source-described ordinary append/cons/reverse construction is covered. No machine-runtime or arbitrary-extensionally-equal-builder claim. |
| C02-110 | DL.createCompose_eq gives constant capture work independently of both stored callbacks' application costs; compose_value/compose_rep give correct composition/append order. EDL.expensive_capture and ordered_composition separate creation from invocation. | Focused XR/XT; complete 72-declaration XD01 root readback. Creating the composed closure does not execute its stored functions in the declared model. |
| C02-111 | DL.empty/singleton/compose AppCost and Rep laws give the closure-entry recurrence and exact suffix semantics; buildFrom/build_appCost prove linear application work for their finite push construction. EDL.materialize_eq, no_bound_from_output_length, padded and doubled preserve the construction-size/output-size/shared-history boundaries. | **Partial**. The missing positive connection is the required relation between actual asc-generated builders and this construction/application measure. The D-law alone cannot supply that connection. Do not equate the number of distinct captured closures with unfolded invocation occurrences, or require a duplicate builder carrier solely to express the proof. |
| C02-112 | Reusable prerequisites are NR's actual workers, NRC's exact comparison trace, DL's creation/application algebra and LB's construction comparison. No complete operational runs/asc/desc execution with the required source-builder invariant and fixed linear bound is present at dfaf681. | **Gap within the known operational continuation.** Implement/count scanner steps, actual ascending creation and materialization, descending cons construction, emitted-run list construction, and empty/single-run merge dispatch in the declared distinct model; prove W_runs ≤ A·length+B and the corresponding single-run natural execution bound. Preserve arbitrary-worker semantic generality through explicit builder-cost hypotheses. |

## Required dispositions and concrete remaining work

### 1. General ordinary sorter equality

The missing C02-090 statement should quantify over arbitrary f and g on lists. Its hypotheses are the source's universal ordinary correctness contracts: each result is pairwise sorted and preserves the input permutation/multiset. Ordinary antisymmetry suffices for pointwise uniqueness once these hypotheses hold. Function extensionality then yields f = g.

Neither ST.StableSort.unique nor the selected equalities sortOn_eq_insertionOn and sortFloorOn_eq_sortOn has that exact scope. They should remain useful theorems, but cannot be substituted for the missing corollary. This report does not author or claim to check the new proof.

C02-089 does not require reimplementing the standard uniqueness theorem. The final map should explicitly identify List.Perm.eq_of_pairwise', Multiset.coe_eq_coe, and the book's linear-order specialization. C02-091's displays should be recorded as proof premises of that theorem. Preserve the already recorded correction that failure of linearity alone does not imply distinct mutually comparable elements: antisymmetry is the relevant uniqueness property. Existing Examples.StableSorting.sorted_permutation_not_stable retains the independent equal-key payload/stability distinction.

### 2. Existing consequential clients should be retained and named

The frozen request for a useful sorting/rank connection already has a checked foundation destination: EIC.sorted_result_has_rank consumes the actual measured sorted value and the existing Selection.pairwise_ranked contract; repeated_value_rank and small_rank_with_sort_budget provide concrete and bounded clients. The budget explicitly counts sorting, without claiming an indexing or full-selection cost.

The selected floor-left stable sorter has arbitrary-payload ordering and equal-key filter clients, and its exact value bridge reaches the existing standard sorter and signed-record client. These connections should be explicit in the final source map. No new rank wrapper is demanded solely because sortFloorOn does not occur by name in RankSelection, and no complete selector cost is inferred from the insertion budget.

### 3. Public module and coverage integration

A read-only import-graph traversal at dfaf681 from SquareApplications and ProofAudit confirms that the following 15 chapter example modules are not reachable from those public roots:

| Unreachable chapter example module | Unreachable chapter example module | Unreachable chapter example module |
| --- | --- | --- |
| Examples.InsertionObservations | Examples.QuickSort | Examples.QuickSortCosts |
| Examples.TopDownSorting | Examples.TopDownCosts | Examples.BottomUpSorting |
| Examples.BottomUpCosts | Examples.AlternatingSorting | Examples.NaturalRuns |
| Examples.NaturalRunComparisons | Examples.NaturalSorting | Examples.NaturalSortingCosts |
| Examples.ListBuildCosts | Examples.ThreeWayQuickSort | Examples.RandomQuickSort |

Examples.InsertionCosts, Examples.MergeCosts, Examples.DifferenceListCosts and Examples.ThreeWayPartition are reachable. Focused command success does not remove the requirement to integrate the other chapter modules into the intended public/full-audit surface. This report does not edit those roots.

docs/research/fdsa-reconstruction-map.md still describes Chapter 2 chiefly through the shared insertion groundwork. It has no complete mapping for these 112 obligations, and its shared XD01/XM01/XQ01 sections retain historical “uncompiled” or “source draft with no compilation” wording after component-focused passes. Reconcile that wording with actual evidence while retaining the distinction between focused checks and acceptance. Preserve the source name correction for ordinary versus accumulator bottom-up passes, floor-versus-ceil split distinction, totalized log boundaries, order/antisymmetry correction, and semantic-versus-cost boundaries.

The local inventory's old “all queued” language is a research-status statement, not evidence that source is missing. Conversely, adding this reconciliation report is not an authorized acceptance or ticket-status update.

### 4. No gap is closed merely by favorable development evidence

The passing components require a final coherent public candidate. The exact foundation dependency must first complete its own applicable gates, with both independent axes reconciling its terminal evidence. A changed dependency or source candidate requires the appropriate revalidation; this report does not substitute later shared potential-accounting prefixes for the recorded foundation.

For the final Chapter 2 candidate, preserve exact compiler/Lake/dependency pins and the qualified native launcher profile; use the README's actual normal-versus-fresh trigger rules. Obtain the complete guarded check, both integrity phases, public coverage, exhaustive transitive axiom audit, matching candidate verification record, full independent Standards and Spec outcomes without unresolved findings, and immediate verify-candidate before the exact local integration. Only the permitted axiom union may be accepted. Focused/type runs here are not full check or audit records.

No Github mutation or push, chapter transition, tracker closure, or accepted-branch update follows from this report. Save and expose the final acceptance checkpoint only after all required gates pass. R's existing acceptance remains intact throughout.

## Separate later natural-sort successor evidence

During this reconciliation, root completed the natural composition proof repair and its four-target focused check on **0ec9954479b081664bd4504c90fb66fba5fd22c8**. This is **outside the assessed dfaf681 snapshot**.

The closed record is provenance/chapter02-natural-sorting-focused-20261104-attempt5/result.json, with full.log and the native terminal record. The command requests Applications.Sorting.Natural, Examples.NaturalSorting, Applications.Resources.NaturalSorting and Examples.NaturalSortingCosts. It exits **0** in **56.931649113 seconds**, with unchanged clean HEAD. The complete log is **3,298 bytes**, SHA-256 **93dd85d55c2705109a0fd804e942737a29fd69342088d8e9286b600cadbe7d30**. It records successful completion; the last example target builds in 45 seconds and earlier targets are reused through the qualified build. Replayed module-system import advisories remain disclosed.

The exact four-file cumulative diff from dfaf681 was read. The pure core is unchanged; the resource signature fixes the intended Nat family index, and the remaining edits repair proofs while preserving source algorithms and expected outputs.

| Source at 0ec9954 | Relationship to dfaf681 | Successor SHA-256 |
| --- | --- | --- |
| Applications/Sorting/Natural.lean | Byte-identical | e4b27eb275e9509b205da7ae25dd7829e664eb47617cb1602e6114eb5d264493 |
| Examples/NaturalSorting.lean | Proof corrections | 69cc14a5f40421076a3af3f8066c0bf2b20678d11f4cbc5e3eefab8454fdbf57 |
| Applications/Resources/NaturalSorting.lean | Explicit intended Nat index in size_isBigO_comparisons | bfca759cd0f1014d39824bdcb124a3a0b33d1459be2cc4635739965382a50e7a |
| Examples/NaturalSortingCosts.lean | Proof corrections | 4b6c3fd9c359b31b01f13c5bdeee6b9fc7ccd82ab172f7d6bb5491410379441a |

This resolves the stated component compilation gap at that successor for the natural comparison composition and its examples. It does not retroactively validate the different failed scripts in dfaf681; all earlier failures remain. It also does not supply C02-111/112's distinct complete operational model, C02-024's expectations, C02-090's missing generic witness, complete public integration, final independent reviews, or full acceptance.

## Final assessment and hold

The report accounts for every required ID exactly once in the obligation tables. The source-specific deterministic sorting, occurrence, sortedness, stability-helper and exercise witnesses are substantially present, with the **single additional explicit theorem gap C02-090**, the known **C02-024/C02-111/C02-112 continuations**, and the stated documentation/integration/gate work preserved. The natural comparison composition has a separately secured later focused pass.

Only this dedicated report is written. The author worktree remains at d4208023c1c30f5f15773b1f50a4d11db0a29e2c with clean tracked source. **HOLD all source/ref/build/cache and further control writes pending root's next bounded instruction.**

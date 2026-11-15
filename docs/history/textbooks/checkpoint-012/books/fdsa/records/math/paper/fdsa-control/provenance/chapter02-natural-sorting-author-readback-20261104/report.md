# Natural composition: complete author source/type readback

Recorded 2026-11-04T06:41:18.199631+00:00.

**Outcome: complete author statement assessment of all 105 declarations; zero
new concrete statement findings.** This is the author readback within the
existing implementation/review loop, not an independent Standards or Spec
axis, an exhaustive axiom audit, or chapter acceptance. C02-110–112 operational
work remains mandatory and has only an approved preparation plan at this point.

## 1. Exact candidate and secured evidence

Checked central candidate: `0ec9954479b081664bd4504c90fb66fba5fd22c8`.
Held author candidate: `33a7c616bbb5d4a774ec614838d7670c61083ec4`, clean index/worktree.
All four reviewed source files have identical bytes at those commits and in
the held author checkout. Their surrounding source trees are not claimed
identical; the dependency distinction is recorded below.

The four-target focused attempt5 closed with actual exit **0** in
**56.93164911299937 seconds**, unchanged clean central HEAD. Its complete
3,298-byte full.log has SHA-256
`93dd85d55c2705109a0fd804e942737a29fd69342088d8e9286b600cadbe7d30`.
The separate type inspection closed with actual exit **0** in
**157.81176944300023 seconds**, again unchanged clean central HEAD. Its complete
79,992-byte full.log has SHA-256
`136335c62dbd1bd67c9f0ce77c69056b47f4e37b5b42e67ea91b233c1a71e50a`.
Both terminal records and native result/log records are secured in their
respective provenance directories and were read. The native runs used one
Lean thread through the unchanged qualified launcher. Their recorded successful
terminal outcomes do not constitute a full candidate check or verification.

The inspection program has SHA-256
`59d413591ef58c6569fcf39575669aaafcb21d4cf7783f05a88935de0a97b9ac`.
It checks every named declaration with universes, explicit arguments and full
names displayed. All 105 complete declaration blocks were read, including
expanded key-order instances, casts and real-valued asymptotic function domains.
The read was in six bounded groups of 16,22,19,18,15,15 declarations, with no
truncated type block. These blocks exactly equal the four subsequently secured
per-module sections, verified by name order and bytes:

| Type section in chapter02-natural-sorting-types-20261104 | Declarations | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `1-Applications-Sorting-Natural-types.txt` | 16 | 8605 | `6860b7a605f19d4c5242f4ae3a03ddeef5bb8af5b96f91e0d467596e3b407f18` |
| `2-Examples-NaturalSorting-types.txt` | 22 | 15877 | `cca8a24401b569edfa5d48cdd18c2d6da4c60fd56a61b4663e61d2a6ab19f752` |
| `3-Applications-Resources-NaturalSorting-types.txt` | 37 | 26499 | `39ccc0ec89a913b5d8bbe4ae834e4cb877fee488f1e2786784323f63b1b29b6e` |
| `4-Examples-NaturalSortingCosts-types.txt` | 30 | 28650 | `82c0c64f879ece1ef1f298dd0e581054dd3eccf668b4d5d48989bb31a8dfb6d9` |

The original inspection preparation inventory identifies historical candidate
4f5f703; it is not silently relabeled. The current-source-at-inspection.json
record identifies the actual 0ec995 source, including the final proof-only
id_eq normalization. The complete frozen chapter requirements, current
112-obligation clarification and pre-code natural-sort plan were compared
with the actual source and types; historical acceptance wording in the frozen
requirements does not undo accepted Chapter 1.

## 2. Source and dependency identity

| Reviewed source | Declaration count | SHA-256 |
| --- | ---: | --- |
| `Applications/Sorting/Natural.lean` | 16 | `e4b27eb275e9509b205da7ae25dd7829e664eb47617cb1602e6114eb5d264493` |
| `Examples/NaturalSorting.lean` | 22 | `69cc14a5f40421076a3af3f8066c0bf2b20678d11f4cbc5e3eefab8454fdbf57` |
| `Applications/Resources/NaturalSorting.lean` | 37 | `bfca759cd0f1014d39824bdcb124a3a0b33d1459be2cc4635739965382a50e7a` |
| `Examples/NaturalSortingCosts.lean` | 30 | `4b6c3fd9c359b31b01f13c5bdeee6b9fc7ccd82ab172f7d6bb5491410379441a` |

The complete project import closure of these four modules contains 22 source
files. Twenty-one are byte-identical between author and checked central,
including every value/resource core. The sole differing file is
`Examples/BottomUpCosts.lean`: author SHA-256
`a242d7219d9221b0c085ff2107a40f9532d995bc5326de5a1c7cdcfaa4263aa1`, checked central
SHA-256 `12572e3395c681b18f266374732eb63b059a13eb0f76aef25400aefa8d54a136`.
Its complete diff was read: two zero-run-length power witnesses use rfl, and
the two single-run-zero bounds use restricted zero-product simplification.
Those edits affect proof bodies only. The reused all_two_runs declaration and
its statement/proof are unchanged. The author dependency tree itself has not
been compiled by this assessment; subsequent alignment must retain the checked
central corrections.

Lean toolchain, Lake manifest and lakefile.toml are byte-identical. Shared
scanner, comparison and merger core identities are:

| Source | SHA-256 at both candidates |
| --- | --- |
| `Applications/Sorting/NaturalRuns.lean` | `123c711b5f0cf05074155f3a0d9ae076aa80a8be482e7e6fc77626aa9db6fb1d` |
| `Applications/Resources/NaturalRunComparisons.lean` | `920e1832416afcdc47a0c2301c2e27c7cd5f0c614a209c8dea21fc2561d809b0` |
| `Applications/Sorting/BottomUp.lean` | `4df83022174bc4e5becfb441617624d57695158d69dc7241209ca077dc2c7791` |
| `Applications/Resources/BottomUpSorting.lean` | `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826` |
| `Applications/Resources/ListMerge.lean` | `df38ab6fd95baca45be4c5f7e6cd86f4e168fbff0ab21899783c8b52a41d1975` |

No dependency, cache, environment, source, Git ref or index was modified during
this assessment. No additional compiler was launched.

## 3. Retained compiler findings and correction history

The complete current four source files and all three root correction diffs
were read, together with the actual failed logs/results of attempts2,3,4.
Author correction1 is retained under its original provenance. The progression
is ce28f2f -> 6e332c5 -> 5679b4f -> 33a7c616 on the author branch.

C02-NAT-ELAB-001–004 repair keyed-goal elaboration, arbitrary Pairwise proof,
implicit relation binders and the intended Nat asymptotic index. Root's
C02-NAT-ELAB-005–009 repair the analogous cost-example comparator aliases,
keep integer-ceiling examples connected to their public theorem with narrow
normalization, and supply the missing arbitrary Pairwise/singleton-length
witnesses and implicit range binders. C02-NAT-ELAB-010 required both an explicit
comparator goal and id_eq in the restricted simplification. The failed attempt
between those two steps remains failed in the record. None of these source
corrections changes an algorithm, numeric expectation or hypothesis.

All 30 cost-example headers remain exactly as originally authored. Across all
105 original source declaration headers, the sole annotation change is the
explicit intended Nat binder in size_isBigO_comparisons; the other repairs are
proof-only. The earlier uses-sorry diagnostic was compiler recovery after the
ill-typed declaration, not an introduced source admission. The successful
four-target attempt and type inspection establish that these recorded
elaboration failures no longer occur on central0ec995. They do not waive
independent review of the complete corrected scope.

## 4. Per-declaration assessment

Every row below was compared against the entire actual elaborated type, the
current definition/proof and the frozen intended contract. The judgment for
every row is **matches; no concrete finding**. Types alone do not show bodies:
actual execution, branch choice and public-theorem connection judgments also
use the four complete source reads. Names in each table are relative to the
stated namespace. The 105 declarations comprise 99 theorems and six ordinary
definitions/abbreviations; these are not whole-project audit counts.

### Applications.Sorting — 16 declarations

| Declaration | Actual contract and source connection assessed |
| --- | --- |
| `sortNaturalBy` | Arbitrary payload universe and independent Boolean scanner/merger operations; source body composes actual runsBy with mergeAllBy. |
| `sortNaturalBy_eq_mergeAll` | Unconditional equality to the same scanner-to-merger composition; no correctness premise. |
| `sortNaturalBy_nil` | Empty input returns empty for arbitrary operations, without a payload inhabitant. |
| `sortNaturalBy_singleton` | One arbitrary payload is returned unchanged; no comparison-law premise. |
| `sortNaturalBy_perm` | Full List.Perm over payloads for every input and arbitrary operations. |
| `sortNaturalBy_multiset` | Equality of full payload multisets, without DecidableEq on payloads. |
| `sortNaturalBy_length` | Exact original length, derived from full permutation. |
| `mem_sortNaturalBy` | Both directions of membership for every payload; no replacement of occurrence preservation by support alone. |
| `sortNaturalBy_sorted_compatible_on` | Independent payload/key universes; only LE and Std.IsPreorder on keys, with separate scanner/merge compatibility restricted to input members. |
| `sortNaturalBy_of_runs_eq_singleton` | Actual runsBy equality to [ys] is the interface premise; arbitrary merger returns that ys. |
| `sortNaturalBy_of_ascending_chain` | Nonempty input and adjacent lt(next,current)=false yield the unchanged list. |
| `sortNaturalBy_of_descending_chain` | Nonempty input and adjacent true comparisons yield the reverse, retaining arbitrary comparator operations. |
| `sortNaturalOn` | Definition needs decidable LT and LE operations on keys only; source body scans strict < and merges left-tie <=. |
| `sortNaturalOn_correct` | Linear order is on keys; result combines KeySorted with full payload permutation, with no payload instances. |
| `sortNaturalOn_of_sorted` | Sorted-input fixed point covers all lengths, including empty; no extra nonempty premise. |
| `sortNaturalOn_of_strictly_descending` | Only decidable LT/LE operations and reverse-direction strict Pairwise premise; no unnecessary key-order axioms or payload requirements. |

### Examples.NaturalSorting — 22 declarations

| Declaration | Actual contract and source connection assessed |
| --- | --- |
| `natCompare` | Nat-to-Nat Boolean comparator; source definition is decide(a <= b). |
| `empty_payload` | Concrete Empty payload domain has empty output; absurd comparators require no inhabitant. |
| `singleton_payload` | Arbitrary payload universe and value; constant Nat key returns the same singleton. |
| `ascending` | Actual natural sort maps [0,1,2] to [0,1,2]. |
| `descending` | Actual natural sort maps [2,1,0] to [0,1,2]; the alias repair changed only proof elaboration. |
| `three_boundary_runs` | Actual scanner returns [[1,3],[2]] on [3,1,2]. |
| `three_boundary` | The same input is fully sorted to [1,2,3], distinguishing scanning from merging. |
| `restart_boundary` | Input [1,3,2,4] crosses an ascending restart and returns [1,2,3,4]. |
| `odd_runs` | Actual scanner produces three unequal runs [[1,3],[2,4],[0]]. |
| `odd_runs_value` | Complete natural sort of that five-element input returns [0,1,2,3,4]. |
| `duplicate_occurrences` | Two occurrences of 2 remain; DecidableEq is only the concrete Nat counting instance. |
| `tagged_exact` | Three arbitrary payloads retain full records and the stated equal-key order; no distinctness/equality assumption. |
| `tagged_correct` | Every list of Nat-keyed arbitrary payloads gets sorted keys and full record permutation. |
| `mixed_records` | Concrete Int/String records return D,B,C,A with keys 1,2,2,3. |
| `weak_descent_with_ties` | Concrete tied input returns 2C,3A,3B, preserving the specified ascending tie branch. |
| `weak_descent_is_not_reversal` | That same tied input does not return 2C,3B,3A; strictness boundary is visible. |
| `nonnegativeCompare` | Boolean comparator on the existing Record type; source restricts the ordinary comparison by its guard. |
| `nonnegative_merge_compatible` | Both implication directions are required only for members of mixedRecords. |
| `input_local_correct` | Sortedness uses the actual two guarded operations on mixedRecords, without a global compatibility assumption. |
| `arbitrary_operations_preserve_occurrences` | Arbitrary Boolean operations still give full permutation, exact length and membership equivalence. |
| `constant_key_fixed_point` | Every List alpha is fixed by constant-key sorting; no payload inhabitance, order or equality premise. |
| `range_fixed_point` | For every natural n, range n is a fixed point, including n=0. |

### Resources.NaturalSorting — 37 declarations

| Declaration | Actual contract and source connection assessed |
| --- | --- |
| `run` | Existing Measured(List alpha) Nat; source body binds actual runsRunBy output into BottomUpSorting.allRun. |
| `comparisons` | Natural-number second projection of that same measured run, with independent Boolean operations. |
| `run_nil` | Exact pair ([],0) for arbitrary operations and payload type. |
| `run_singleton` | Exact pair ([a],0), retaining arbitrary payload and operations. |
| `run_value` | First projection equals the actual pure natural sorter. |
| `run_perm` | Measured returned value preserves full payload permutation without order assumptions. |
| `run_length` | Measured returned list has exactly the original length. |
| `run_multiset` | Measured returned value has exactly the original multiset; no payload DecidableEq. |
| `run_correct` | Source strict/non-strict key comparators yield KeySorted plus full payload permutation under a linear key order. |
| `comparisons_nil` | The empty-input comparison count is exactly zero. |
| `comparisons_singleton` | The singleton comparison count is exactly zero. |
| `comparisons_eq_scan_add_merge` | Exact source count is runsCountBy plus allComparisons on the actual runsBy result. |
| `comparisons_eq_length_add_merge` | Exact scan summand is truncated Nat length-1, including empty input. |
| `run_exact` | Whole measured pair combines the actual sorted value and length-1 plus merge count on actual detected runs. |
| `comparisons_lower` | Unconditional Nat length-1 lower bound; no positive-length or order premise. |
| `comparisons_le_adaptive` | Unconditional upper bound (n-1)+n*clog2(actual run count), without uniform-run-length assumptions. |
| `comparisons_le_clog` | Run-count invariant yields (n-1)+n*clog2(n), still for all lengths and operations. |
| `comparisons_le_source` | Retains the printed weaker n+n*clog2(n) rather than silently replacing it. |
| `comparisons_le_of_length` | Explicit n : Nat and length=n premise give the same source bound. |
| `comparisons_le_adaptive_int_ceil` | The entire truncated Nat subtraction is cast to Int; actual run count is cast to Real before logb and Int.ceil. |
| `comparisons_le_int_ceil` | Source integer-ceiling bound has no hidden positivity premise and covers zero/singleton inputs. |
| `comparisons_le_int_ceil_of_length` | Length-indexed integer-ceiling form retains n : Nat and only the stated length equation. |
| `run_of_runs_eq_singleton` | Actual singleton run-list premise gives returned ys and exactly length-1 comparisons, with arbitrary merger. |
| `run_of_ascending_chain` | Nonempty adjacent-false chain gives unchanged value and exact length-1 count. |
| `run_of_descending_chain` | Nonempty adjacent-true chain gives reverse value and exact length-1 count. |
| `mergeComparisons_of_sorted` | Sorted nonempty keyed input needs zero merge comparisons for every supplied merger operation. |
| `run_of_sorted` | Sorted nonempty input gives the original value and length-1 under the strict key scanner, for arbitrary merger. |
| `comparisons_of_sorted` | Sorted comparison equality covers empty input separately; no nonempty premise in this count law. |
| `mergeComparisons_of_strictly_descending` | Only LT/DecidableLT on keys, strict Pairwise and nonempty input; merge count is zero. |
| `run_of_strictly_descending` | Same minimal strict interface gives reverse value and length-1; no key LE/order axiom is added. |
| `length_le_twice_comparisons` | The positive lower estimate n <= 2*C has the necessary n>=2 premise. |
| `comparisons_le_two_clog` | C <= 2*n*clog2(n) explicitly assumes n>=2 for the later growth argument. |
| `comparisons_isBigO` | Nat-indexed length-n input families, real-valued observations and Nat atTop; O(n logb2 n) follows from the numerical bound. |
| `comparisons_isBigO_of_bounded_runs` | Natural run-budget r bounds actual runs for every n; length-n families then have comparison O(n). |
| `size_isBigO_comparisons` | Actual elaboration is Nat atTop with direction n=O(C(inputs n)); the explicit Nat repair preserves that intended direction. |
| `sorted_comparisons_isBigO` | Length-indexed sorted families have comparison O(n); key linear order and sorted-family premise remain visible. |
| `sorted_comparisons_isTheta` | Both eventual directions give comparison Theta(n) for sorted families, without a false positive bound at n=0 or 1. |

### Examples.NaturalSortingCosts — 30 declarations

| Declaration | Actual contract and source connection assessed |
| --- | --- |
| `empty_payload` | Actual Empty-payload computation returns ([],0); no default element or hidden entry charge. |
| `singleton_payload` | Every arbitrary payload/comparator singleton returns ([a],0). |
| `ascending` | Sorted [0,1,2] returns the same list with exactly 2 comparisons. |
| `ascending_zero_merge` | The actual detected runs of that input require exactly 0 merge comparisons. |
| `descending` | Strict [2,1,0] returns [0,1,2] with exactly 2 comparisons. |
| `three_boundary_scan` | Actual scanner pair is ([[1,3],[2]],2). |
| `three_boundary_merge` | The actual merger on those same runs returns ([1,2,3],2). |
| `three_boundary` | Binding the actual two phases yields ([1,2,3],4). |
| `restart_merge` | Merging [1,3] and [2,4] returns [1,2,3,4] with 3 comparisons. |
| `restart_boundary` | The complete restart input has total comparison count 6. |
| `odd_runs_scan` | Five-element input yields the exact three runs and scan count 4. |
| `odd_runs_merge` | Two actual merge passes return [0,1,2,3,4] with combined merge count 4. |
| `odd_runs` | Complete comparison count is 8, retaining the five-element returned value. |
| `odd_runs_adaptive_budget` | The same actual count satisfies budget 14; proof consumes the general adaptive theorem. |
| `mixed_records_merge` | Actual two-run record merger returns D,B,C,A with merge count 3. |
| `mixed_records` | Actual strict scanner plus left-tie merger returns D,B,C,A with total count 6. |
| `weak_descent_merge` | Tied [3A,3B] and [2C] merge to 2C,3A,3B with count 1. |
| `weak_descent_with_ties` | Complete tied input returns 2C,3A,3B with total count 3. |
| `weak_descent_not_best_case` | That count is strictly greater than the one-run length-three minimum 2. |
| `empty_inner_runs` | Existing allRun accepts [[],[2],[],[1,3]] and returns ([1,2,3],2). |
| `arbitrary_payload_correct` | Every Nat-keyed arbitrary payload list gets sorted returned keys and full record permutation. |
| `arbitrary_operations_and_bounds` | For arbitrary operations, full permutation/length and unconditional lower/adaptive upper bounds all survive together. |
| `integer_zero_one_bound` | Concrete Int-cast consequences are C([])<=0 and C([7])<=1; proofs retain the public integer-ceiling theorem. |
| `repeated_payload_exact` | For every natural n and arbitrary supplied payload/merger, the always-false scanner has exact n-1 comparisons. |
| `constant_key_run_count` | Every arbitrary-payload list has at most one run under the false scanner, including empty input. |
| `repeated_payload_bounded_runs` | Real-valued comparison O(n) is instantiated through the proved actual run-budget theorem. |
| `repeated_payload_linear` | The repeated family has comparison Theta(n), with arbitrary payload and merger and Nat index. |
| `ascending_range_exact` | For every natural n, actual range sorting has exact n-1 comparison count. |
| `ascending_range_linear` | The same range family has comparison Theta(n) at Nat atTop. |
| `periodic_family_isBigO` | Length-n range-modulo-three family gets O(n logb2 n) from the general bound; no probability or distinct-key assumption. |

## 5. Cross-cutting conclusions and continuation boundary

The pure sorter is the actual runsBy/mergeAllBy composition. Occurrence laws
preserve full payload multiplicity, and keyed correctness is obtained from
component invariants rather than assuming the requested sorted result. Generic
payloads retain independent universes and no equality/order/default/inhabitance
instances. The source interface uses strict scanning and left-tie merging;
strict-descending value/count results keep their weaker domains. Concrete tie
orders do not become a universal stability claim.

The measured sorter binds actual returned runs to allRun and proves erasure
separately from the exact count. Its unconditional lower bound, adaptive
run-count bound, all-length consequence and weaker printed bound agree with
the source observation. The integer bound casts the truncated natural scan
count as a whole. All growth statements elaborate over Nat atTop with Real
observations; the inverse theorem has the intended n=O(C) direction, and the
positive comparison lower estimate remains restricted to n>=2. Sorted/strict
one-run laws and empty input retain their exact distinct cases.

Independent expected cases still show scan2+merge2=4 on [3,1,2], scan3+merge3=6
on [1,3,2,4], and scan4+(merge3+merge1)=8 on [1,3,2,4,0]. The last input also
uses the general adaptive budget14. Sorted [0,1,2] costs2 with zero merging;
tied weak descent costs3 rather than the one-run minimum2. Empty-inner runs
remain supported by the shared merger. Arbitrary payloads, duplicates,
input-local compatibility and range/replicate/modulo families are retained.

No builder creation/application, control, allocation or machine-runtime work
is inferred from these comparison equations. The approved operational plan
under chapter02-natural-operations-preparation-20261104 remains the next
mandatory implementation slice. Full integrated candidate validation/audit,
independent Standards and Spec reviews and immediate candidate verification
remain outstanding. Accepted R and the exact pending foundation candidate are
unchanged by this report. After saving this report and the authorized handoff
receipt, all writes are HELD pending root's alignment/implementation release.

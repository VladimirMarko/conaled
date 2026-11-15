# Bottom-up comparison source and elaborated-type author readback

Date: 2026-11-04. Assessor: the assigned bottom-up implementation author.

**Outcome: complete author assessment of all 105 public declarations, with zero
concrete source/statement findings.** The 76 resource declarations, all 29
connected example declarations, their complete corresponding source/proofs and
the resource module's private uniform-flatten-length helper were read. The
assessment covers the exact successful focused/type-check candidate below.
It is not an independent Standards or Spec review, a whole-project audit, or
acceptance of this component or Chapter 2.

## Exact scope and identity

- Accepted chapter/review base remains
  `07e480f6ec9958d4975bb90151005b84f2907614`.
- Successful central development candidate:
  **`6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b`**.
- Held author branch `work/fdsa-ch02-bottom-up`:
  **`a6f950d7d5dc4aef521445250f9bfbd59166291d`**.
- The two assessed files at that author tip equal the checked central files
  byte-for-byte, verified through `git show` of the immutable central commit.
  The author checkout's tracked source and index are clean.
- The reused `Sorting/BottomUp`, `Examples/BottomUpSorting`, resource
  `ListMerge`, `Measured` and `Growth` files were also compared between these
  two commits; every comparison matched. No candidate or dependency was edited.

| Assessed source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/BottomUpSorting.lean` | 512 | 23,175 | `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826` |
| `Examples/BottomUpCosts.lean` | 243 | 11,973 | `12572e3395c681b18f266374732eb63b059a13eb0f76aef25400aefa8d54a136` |

The exact 105-name inspection source is
`../chapter02-bottom-up-costs-statement-source-20261104/Statements.lean`, with
`pp.universes` and `pp.explicit` enabled and `#check @...` for every name.
It is 5,757 bytes, SHA-256
`f9486a8f64d9786814f2ffc67dfb158ab13bf1d392585c27ca83b35cadd34c2e`.
Its `groups.json` is 5,614 bytes, SHA-256
`47fba785d1bd77a271735366ffb1fcac26d03645701c2e62ab2f9f722f022c0a`.

| Complete elaborated output read | Public declarations | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| `BottomUpSorting-types.txt` | 76 | 462 | 36,106 | `884d6bbda53f4fc20a87cdd67fee61d2c75bb70f45847c132a5a8178cf6c4e98` |
| `BottomUpCosts-types.txt` | 29 | 450 | 33,228 | `877824e5b42c065dd44cc851006c47d84ea3452eaef42a66d937479e1f89520b` |

In addition to reading every statement, a read-only inventory comparison
confirmed that the public names extracted from each source, its ordered
`groups.json` list and every declaration heading in the corresponding output
agree exactly. Both output sections occur contiguously in the complete closed
type log. Thus the assessment does not substitute a successful headline or a
small sample for the full source/type inventory. These are public declaration
counts, including definitions and projections, not whole-project audit counts.

## Closed validation evidence and its limits

The two-target focused record is
`../chapter02-bottom-up-costs-focused-20261104-attempt4/`. It ran the qualified
native kit with one Lean thread and requested
`Applications.Resources.BottomUpSorting` and `Examples.BottomUpCosts`.

- Recorder start: `2026-11-04T06:00:55.123569+00:00`.
- Recorder completion: `2026-11-04T06:03:17.317696+00:00`.
- Actual exit **0**, elapsed **142.193826109 seconds**.
- Final HEAD equals the checked candidate; final source status is clean.
- Complete log: **2,968 bytes**, SHA-256
  `44df874a8351b38a24f564fe4a7ebfe0b3ff9289fdf393b367a8e654fc76a6a2`.
- The log replays the already successfully built resource module and records
  `Built Examples.BottomUpCosts (126s)`, followed by successful completion.
  Its 2,087 Lake jobs include dependencies and are not a count of new book
  modules. Replayed module-system import advisories remain disclosed.
- The saved native record independently reports exit 0, no timeout and no
  recorder error, with native elapsed time 142.088419038 seconds.

The 105-declaration inspection in this directory used the same candidate and
qualified one-thread native environment:

- Recorder start: `2026-11-04T06:03:42.970508+00:00`.
- Recorder completion: `2026-11-04T06:05:34.557043+00:00`.
- Actual exit **0**, elapsed **111.586157087 seconds**.
- Final HEAD is unchanged and final source status is clean.
- Complete log: **69,695 bytes**, SHA-256
  `b77970fe06b930f34286bcdb0e9a9ce1bdfbffceb2cdaf7f213cdf501137493d`.
- The saved native record independently reports exit 0, no timeout and no
  recorder error, with native elapsed time 111.491027445 seconds.

The full-log digest above was recomputed from the actual bytes and matches
`result.json`. A task-message transcription used `e9a1ce` in that digest; the
saved record and bytes consistently contain `e9a9ce`. This report uses the
verified digest. There is no candidate/source or saved-evidence mismatch.

Neither successful record contains a candidate-verification record. These
focused results do not establish a full ordinary check, exhaustive axiom audit,
independent review outcome or immediate pre-integration verification. No new
compiler/checker/cache activity was performed for this author readback.

## Requirements and source correspondence assessed

The frozen `reviews/chapter02-requirements.md` was read in full. Its current
12,034 bytes retain SHA-256
`f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36`.
The active-scope record was read, with the current source inventory's applicable
bottom-up, general merge-all and Exercise 2.6 rows. The source inventory remains
`a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2`.
The complete chapter still has all 112 recorded obligations; this assessment
does not alter the frozen 107-row requirements or their explicit C02-088 /
C02-108–112 reconciliation.

The exact comparison recurrences, uniform bounds, general run-count bound and
Exercise 2.6 passage were also read in the recovered pinned Chapter 2 text.
The controlling book is the July 27, 2026 edition, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The bottom-up readiness section and its independently calculated three-equal-run
example were read in `research/mergesort-cost-readiness.md`; the current file
has SHA-256 `e36333a7e913fe0b11a1950f23c10a5fcb5975f37adb8c8d5405db2fe61a09a5`.
The Chapter 2 reconciliation explicitly preserves the separate natural-builder
operational model and does not add those charges to this comparison tariff.

| Frozen obligation | Assessed destination and preserved meaning |
| --- | --- |
| C02-051 | `pairsRun` and its comparison projections/equations: zero empty/singleton pass cost; actual first-pair merge comparisons plus the remaining pass. |
| C02-052 | `allRun`, its actual-bind equation, erasure and scalar recurrence: recurse on the runs returned by the measured pass. |
| C02-053 | `run` and `comparisons_eq_all`: one singleton for each input occurrence; initialization is uncharged. |
| C02-055 | `pairsComparisons_le_uniform`: all input runs have length `m`; evenness is unnecessary for the comparison budget. |
| C02-056 | `allComparisons_le_uniform_pow`: uniform length `m` and exact outer count `2^k`, with `m=0` and `k=0` allowed. |
| C02-057 | `comparisons_le_of_length_pow`: exact input length `2^k` yields `k*2^k`; the empty input is handled by separate base laws. |
| C02-073 | `pairsComparisons_le`: arbitrary run lengths and counts, including empty inner runs; bound by flattened payload length. |
| C02-074 reuse | The checked value-layer total-length preservation is used in the general bound; it is not replaced with a same-value count inference. |
| C02-075 | Both natural halving recurrences and both integer-ceiling bridges; recurrence domain is `2≤n`, and the convention bridge includes zero/one. |
| C02-076 | `allComparisons_le_clog` and `_le_int_ceil`: total payload length times ceiling log of outer run count, with explicit empty/singleton branches and no hidden positivity premise. |
| C02-105/106 comparison portion | Actual append-free accumulator pass, arbitrary-accumulator pass-count equality, full pair correspondence and separately proved complete reversed-pass bounds. No equality of complete costs or keyed stability is asserted. |

The already checked value layer supplies C02-054's evenness-dependent doubling,
ordinary and reversed correctness, arbitrary-accumulator occurrence/length
laws and decreasing run counts. The real-log and asymptotic corollaries are
proved consequences of these actual count bounds through existing Mathlib and
`Resources.Growth`; they do not claim machine running time. The natural scanner,
natural-sort composition, builder operational model and other Chapter 2 work
remain separate integration obligations.

## Statement and execution assessment

All generic interfaces retain `{α : Type u}` at arbitrary universe and a plain
Boolean comparator. The elaborated types introduce no payload order,
`DecidableEq`, inhabitant or finiteness class. Numeric observations live in
`Nat` independently of the payload universe. The raw value-erasure, occurrence
and cost results hold for arbitrary comparators and arbitrary runs. Sortedness
is used only through an existing input-local value contract in its particular
connected example; it is not silently added as a cost premise.

`pairsRun` executes `Resources.ListMerge.run` and selects only its comparison
component with `Resources.reweight Prod.fst`. The entry-count component is not
mistaken for the chapter tariff. Its actual returned list is prepended to the
actual returned tail runs. `allRun` captures the same measured pass pair and
recurses on its first projection. Its public step theorem exposes precisely
`bind (pairsRun ...) (allRun cmp)`. Definitional reduction of the existing
`Resources.bind` justifies that form; no synthetic comparison execution or
unrelated pure recursive argument replaces the measured result.

The repeated-execution termination proof uses the outer run count after
erasure and the strict ceiling-half decrease for at least two runs. The
general comparison proof uses the pass budget, preserved flattened length and
the ceiling-log halving recurrence. It separates the number of runs `r` from
the total number of payload elements `N`; arbitrarily many empty runs are
permitted. The private `flatten_length_uniform` helper was read with its
structural proof and only its stated uniform-length premise. It converts the
general bound into the printed `m*k*2^k` result without imposing evenness or
positivity on `m`.

The accumulator execution uses the returned merged run, cons and recursion.
Its implementation contains neither append nor reverse. The accumulator is
not itself merged during a pass, explaining why the cost is independent of
its contents, length and ordering. The scalar count equality is proved from
the actual per-pair recurrences; the full pair theorem then combines that
count proof with the separately proved reversed-value law. `allRevRun` uses
an empty accumulator on each pass, permitting the same decreasing outer-count
argument. Its complete budget has its own recurrence/induction; no proof
substitutes ordinary total costs after changing the run order.

Only head comparisons are charged. Dispatch, singleton initialization,
outer-list traversal/construction, comparator implementation, allocation,
sharing and compiler tail-call behavior remain outside the declared tariff.
The append-free source property is checked directly rather than inferred from
a comparison bound. This assessment does not infer an operational complexity
theorem about those excluded operations.

The integer-ceiling bridge is quantified over every natural input, including
zero and one under the totalized real logarithm. The source halving formula
retains `2≤n`; it is not extended across invalid small cases. The unrounded
real-log inequalities retain the exact power-of-two premise. The `IsBigO`
theorems quantify over an actual family `inputs` with `(inputs n).length = n`;
their proof uses the existing eventual real-log bound. The descending-range
client supplies a nonvacuous family satisfying that premise for every `n`.

All corresponding proofs were read. Static inspection found no `sorry`,
`admit`, new axiom, `native_decide`, unsafe or partial definition in these two
files. The remaining tactics produce ordinary checked terms. This static
observation is not a replacement for the mandatory exhaustive candidate audit.

## Complete resource declaration readback: 76 of 76

Every name in this table has prefix `Resources.BottomUpSorting`. Each row was
checked against both the complete explicit type and the corresponding source
definition/proof. All rows have outcome **no finding**.

| # | Public declaration | Contract and proof assessment |
| ---: | --- | --- |
| 1 | `pairsRun` | Universe-polymorphic measured adjacent-pair execution, using actual merge output and additive Nat comparisons. |
| 2 | `pairsComparisons` | Direct second projection of that execution, with no second scalar algorithm. |
| 3 | `pairsRun_nil` | Empty outer list returns empty runs at zero cost by the defining branch. |
| 4 | `pairsRun_singleton` | An arbitrary sole run is retained at zero cost. |
| 5 | `pairsRun_step` | Actual merge, actual tail pass and uncharged cons are sequenced in the displayed order. |
| 6 | `pairsRun_value` | Structural erasure to canonical `mergePairsBy`, using `ListMerge.run_value`. |
| 7 | `pairsComparisons_nil` | Exact zero comparison projection for empty outer input. |
| 8 | `pairsComparisons_singleton` | Exact zero projection for any sole run. |
| 9 | `pairsComparisons_step` | First pair's actual merge comparisons plus the recursive pass count. |
| 10 | `pairsComparisons_le` | Arbitrary-comparator pass budget is flattened length; proof uses the existing merge bound. |
| 11 | `pairsComparisons_le_uniform` | Uniform input lengths alone give `m * runCount`; private flatten helper has the same premise. |
| 12 | `clog_two_ceil_half` | `2≤n` implies the ceiling-half recurrence through pinned `Nat.clog_of_two_le`. |
| 13 | `clog_two_source_half` | Same necessary domain, with the source's natural truncated-subtraction half. |
| 14 | `int_ceil_logb_two_nat` | Exact integer-ceiling/natural-clog equality for every natural `n`, with explicit cast normalization. |
| 15 | `int_ceil_logb_two_source_half` | Integer-ceiling source recurrence preserves `2≤n`; neither cast moves the natural division into reals. |
| 16 | `allRun` | Repeated actual measured passes, well-founded by outer run count. |
| 17 | `allComparisons` | Second projection of the repeated measured execution. |
| 18 | `allRun_nil` | Empty outer input returns `([],0)`. |
| 19 | `allRun_singleton` | Returns the arbitrary sole run unchanged with no merge work. |
| 20 | `allRun_step` | Public `bind` continuation receives precisely the measured pass value. |
| 21 | `allRun_value` | Erasure follows the same decreasing run-list recursion as `mergeAllBy`. |
| 22 | `allRun_perm` | Full occurrence permutation of the original flattened runs, without order laws. |
| 23 | `allComparisons_nil` | Exact empty-outer-list zero cost. |
| 24 | `allComparisons_singleton` | Exact zero cost for a sole run of any length. |
| 25 | `allComparisons_step` | Actual pass cost plus recursively measured cost on its erased actual result. |
| 26 | `allComparisons_le_clog` | `N * Nat.clog 2 r` for all outer lists; explicit two base cases and decreasing recursive bound. |
| 27 | `allComparisons_le_int_ceil` | Casts the same count/bound into integers using the proved source convention, without positivity assumptions. |
| 28 | `allComparisons_le_uniform_pow` | Both uniform length and exact power-of-two run-count premises are retained; `m=0`, `k=0` remain admissible. |
| 29 | `run` | Initializes singleton runs from every original occurrence, then invokes measured repeated merging. |
| 30 | `comparisons` | The initialized execution's second projection. |
| 31 | `run_nil` | Empty initialized sorter returns `([],0)`. |
| 32 | `run_singleton` | Any singleton payload is returned at zero comparisons. |
| 33 | `run_value` | Exact erasure to `sortBottomUpBy`, not another library sort recurrence. |
| 34 | `run_perm` | Full payload permutation for arbitrary comparator. |
| 35 | `comparisons_eq_all` | Source counter identity after singleton initialization is definitional. |
| 36 | `comparisons_le_clog` | All-length `n * Nat.clog 2 n` via singleton flatten/length laws. |
| 37 | `comparisons_le_of_length_pow` | The source `k*2^k` upper bound retains the exact input-length premise. |
| 38 | `comparisons_le_real_log_of_length_pow` | Real-cast count bounded by `n*log₂ n` under that same power premise; casts/powers are explicit. |
| 39 | `comparisons_isBigO` | Uniform actual-input family with length `n`; existing Growth bridge yields real `O(n log₂ n)`. |
| 40 | `pairsRevRun` | Actual merge output is consed onto an arbitrary accumulator; no append/reverse appears in the definition. |
| 41 | `pairsRevComparisons` | Second projection retains both arbitrary accumulator and input-run arguments. |
| 42 | `pairsRevRun_nil` | Returns the complete arbitrary accumulator with zero new comparisons. |
| 43 | `pairsRevRun_singleton` | Prepends the leftover run to that accumulator, at zero comparisons. |
| 44 | `pairsRevRun_step` | Actual measured pair merge supplies the next accumulator head. |
| 45 | `pairsRevRun_value` | Erasure to the actual append-free `mergePairsRevBy`, with arbitrary accumulator. |
| 46 | `pairsRevComparisons_nil` | Empty input count is zero regardless of accumulator. |
| 47 | `pairsRevComparisons_singleton` | Sole leftover count is zero regardless of accumulator. |
| 48 | `pairsRevComparisons_step` | Exact merge count plus the tail count with the actual merged list in the accumulator. |
| 49 | `pairsRevComparisons_eq` | All accumulators give the ordinary pass count; independent recurrence induction justifies the equality. |
| 50 | `pairsRevRun_eq` | Whole pair is `(ordinaryReturnedRuns.reverse ++ acc, ordinaryPassCount)`; `Prod.ext` combines separate value and count proofs. |
| 51 | `pairsRevComparisons_le` | Bound uses the input runs' total length, correctly excluding the unmerged accumulator. |
| 52 | `pairsRevComparisons_le_uniform` | Uniform bound likewise concerns only the input runs and requires no accumulator invariant. |
| 53 | `allRevRun` | Repeated measured reversed passes use empty accumulators and their actual next runs. |
| 54 | `allRevComparisons` | Direct second projection of that distinct repeated algorithm. |
| 55 | `allRevRun_nil` | Empty repeated execution returns `([],0)`. |
| 56 | `allRevRun_singleton` | An arbitrary sole run is returned unchanged, with zero comparisons. |
| 57 | `allRevRun_step` | Actual reversed-pass result is the continuation argument in the public bind equation. |
| 58 | `allRevRun_value` | Exact erasure to `mergeAllRevBy`, preserving the reversed tree. |
| 59 | `allRevRun_perm` | Full occurrence permutation of the original flattened runs. |
| 60 | `allRevComparisons_nil` | Zero empty-outer-list cost. |
| 61 | `allRevComparisons_singleton` | Zero arbitrary-sole-run cost. |
| 62 | `allRevComparisons_step` | Its own actual pass cost plus count on `mergePairsRevBy cmp [] ...`. |
| 63 | `allRevComparisons_le_clog` | Separate decreasing induction for the reversed merge tree proves the same `N*clog r` upper bound. |
| 64 | `allRevComparisons_le_int_ceil` | Same totalized integer-ceiling correspondence for the reversed count. |
| 65 | `allRevComparisons_le_uniform_pow` | Exact uniform and power-of-two premises yield `m*k*2^k`, without equality to ordinary totals. |
| 66 | `revRun` | Initializes singleton occurrences and calls the actual reversed repeated execution. |
| 67 | `revComparisons` | Direct second projection of `revRun`. |
| 68 | `revRun_nil` | Empty initialized reversed sorter returns `([],0)`. |
| 69 | `revRun_singleton` | Singleton initialized reversed sorter returns that payload at zero cost. |
| 70 | `revRun_value` | Exact erasure to `sortBottomUpRevBy`; no stable-sort replacement. |
| 71 | `revRun_perm` | Full payload permutation without comparator laws. |
| 72 | `revComparisons_eq_all` | Definitional singleton-initialization counter identity for the reversed algorithm. |
| 73 | `revComparisons_le_clog` | All-length initialized reversed bound is `n * Nat.clog 2 n`. |
| 74 | `revComparisons_le_of_length_pow` | Exact power-of-two input length gives the source-form upper bound, including `k=0`. |
| 75 | `revComparisons_le_real_log_of_length_pow` | Real-log corollary retains the same power premise and this algorithm's count. |
| 76 | `revComparisons_isBigO` | Same length-indexed family interface and existing Growth bridge, for the reversed count separately. |

## Complete connected-example readback: 29 of 29

Every name below has prefix `Examples.BottomUpCosts`. All complete elaborated
statements and proofs were assessed, including their independently stated
expected values/counts and applications of public contracts. All rows have
outcome **no finding**.

| # | Public declaration | Expected observation and assessed connection |
| ---: | --- | --- |
| 1 | `empty_and_single_run` | Both actual repeated algorithms return empty/any sole run at zero comparisons; no sortedness premise is smuggled into the base law. |
| 2 | `unsorted_single_run` | `[[2,1]]` returns `[2,1]` at zero cost and is not sorted, exposing the separate run invariant. |
| 3 | `ragged_observation` | Input `[[1,3],[2],[],[0,4],[2,5]]` yields `[[1,2,3],[0,4],[2,5]]` with cost 2. The first pair contributes 2, the empty-side pair 0, and the odd leftover 0. |
| 4 | `nonempty_accumulator_observation` | Completed ragged runs are reversed before the exact accumulator `[[99],[],[42,43]]`; the expected cost remains 2. |
| 5 | `accumulator_cost_independent` | Two arbitrary accumulators have equal pass counts on the same inputs; uses both public per-pass equality instances. |
| 6 | `three_equal_first_pass` | Ordinary `[[0],[0],[0]]` produces `[[0,0],[0]]` with cost 1 using actual merge equations. |
| 7 | `three_equal_reversed_first_pass` | Reversed pass produces `[[0],[0,0]]` with cost 1 through the full pair correspondence. |
| 8 | `all_two_runs` | Any two runs perform exactly one comparison-projected measured merge; the final singleton dispatch is uncharged. |
| 9 | `all_reversed_two_runs` | The same two-run identity for the reversed algorithm, without order assumptions. |
| 10 | `ordinary_three_run` | A generic first measured merge of `[a]` and `[b]` supplies the next merge's left operand; `[c]` is its right operand. |
| 11 | `reversed_three_run` | The same first returned list instead becomes the next merge's right operand, with `[c]` on the left. |
| 12 | `ordinary_three_equal` | Exact ordinary result `[0,0,0]`, total 3: one initial comparison, then two left-tie comparisons. |
| 13 | `reversed_three_equal` | Same unlabelled value but total 2: one initial comparison, then one left-tie comparison. |
| 14 | `same_pass_costs_different_totals` | Conjoins equal first-pass counts, equal unlabelled sorted values and unequal complete actual counts. |
| 15 | `ordinary_tagged_equal` | Arbitrary-universe payloads remain `first,middle,last`, with cost 3; no payload equality/order class is required. |
| 16 | `reversed_tagged_equal` | Same input returns `last,first,middle`, with cost 2; exact tagged occurrences expose changed order. |
| 17 | `measured_tail_not_stable` | Distinct concrete string tags refute stable equal-key filtering after measured reversed sorting, via the existing value counterexample. |
| 18 | `raw_occurrences_and_bounds` | Both outputs permute all input occurrences and satisfy their own all-length budgets for arbitrary comparator. |
| 19 | `local_comparator_values` | Existing nonnegative-domain comparator evidence supplies sorted measured values for both algorithms through erasure; no global compatibility assertion is added. |
| 20 | `odd_uniform_budget_and_leftover` | Three singleton runs satisfy pass budget 3 while the odd leftover refutes unconditional length doubling. |
| 21 | `four_empty_runs_zero` | Generic four-empty-run input has exact zero comparison totals. Both public uniform-power bounds are instantiated with `m=0`, `k=2`. |
| 22 | `single_run_power_zero` | Any sole run, however long, instantiates both public bounds at `k=0`. Restricted zero-product simplification keeps those theorem applications meaningful. |
| 23 | `uniform_four_runs_bound` | Four length-two runs receive budget 16 for each actual merge tree, with checked uniform-length and run-count witnesses. |
| 24 | `ragged_general_bound` | Arbitrary comparator on the five ragged runs receives budget `7*clog₂ 5 = 21` for each tree, without uniformity. |
| 25 | `source_ceiling_zero_one` | The public natural/integer ceiling bridge gives both totalized boundary values 0. |
| 26 | `source_half_at_five` | Applies the source recurrence at 5 to obtain `clog₂ 5 = clog₂ 3 + 1`, including its domain witness. |
| 27 | `sorter_power_zero` | Both initialized sorters on `[9]` use their public power-of-two theorem at exponent zero. |
| 28 | `empty_payload` | For every comparator on `Empty` and every `List Empty`, both measured sorters return `([],0)`; no inhabitant/default is required. |
| 29 | `descending_families_isBigO` | The family `reverse (List.range n)` supplies length exactly `n` and connects both actual comparison functions to their public real-log asymptotic bounds. |

The two three-input generic sequencing lemmas ensure the exact totals are
connected to the public measured executions, not to an unrelated hand counter.
The tagged equal-key examples impose no distinctness premise on arbitrary
payload parameters; the separate concrete string-tag example supplies the
nonvacuous instability witness. No universal stability theorem is inferred
from the ordinary three-input example.

## Preserved failures and correction history

All prior records remain unchanged. In particular, the comparison work did not
pass on its first draft, and the successful pair does not retroactively make
any enclosing failed check successful.

| Actual record | Candidate and terminal outcome | Bottom-up meaning |
| --- | --- | --- |
| `chapter02-bottom-up-partition-focused-20261104-attempt1` | `ccaee94222b78ac57e9a8ea23c6e86c056a19a23`, exit 1, 57.535265859 s | Eight resource proof-elaboration diagnostics; corrected in author `1e4b34b...`, preserving every definition/statement. |
| `chapter02-extended-sorting-focused-20261104-attempt1` | `5d7a479549f5acd64a9e5adb418ab48780c238ef`, exit 1, 290.051303003 s | Resource module built in 87 s; four example diagnostics remained. The aggregate also had independent other-target failures. |
| `chapter02-bottom-up-costs-focused-20261104-attempt3` | `d19a22d8654dde54b7a781b455ab3e3f37bf8589`, exit 1, 28.317976846 s | After author `6e0f7f4...`, only the two generic singleton-length `decide` witnesses remained. |
| `chapter02-bottom-up-costs-focused-20261104-attempt4` | `6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b`, exit 0, 142.193826109 s | Both named cost targets pass after root's exact two-witness repair. |
| `chapter02-bottom-up-costs-types-20261104` | Same `6d91b822...`, exit 0, 111.586157087 s | All 105 explicit public declarations printed successfully and assessed in this report. |

The attempt-3 closed log is 5,338 bytes, SHA-256
`4ef07061c0ff20c58adf95b51146d4a54619b7196edc0120c18e5b7f6315080b`.
Its only bottom-up errors were `[xs].length = 2^0` witnesses using `decide`
at example lines 183 and 185. Root's held-tree successor
`a6f950d7d5dc4aef521445250f9bfbd59166291d`, directly after
`6e0f7f41540299b12ce09c91db408f83d20f9948`, changes precisely those two witnesses
to `rfl`. Its complete diff was read; all expected cases, public theorem
applications and resource source bytes are preserved. Earlier value-layer
failures and its separate successful 87-declaration author assessment remain
in the existing implementation handoff.

## Findings, pending gates and hold

**Concrete mathematical/source/type findings: 0.** No repair is requested by
this readback. The actual elaborated contracts preserve their intended
quantifiers, satisfiable premises, occurrence multiplicities, tie branches,
actual-result recursion, observation projections and source boundaries. The
comparison-only bounds have no unintended ordering, evenness or positivity
assumption. No claim of equal complete ordinary/reversed costs, universal
reversed stability or uncharged-operation runtime was introduced.

Independent Standards and Spec review, complete candidate validation and
exhaustive axiom audit, public-root/coverage integration, immediate candidate
verification and accepted-tip integration remain pending. This author report
does not alter the separate foundation candidate or infer a terminal result
for its still-unclosed full check. The accepted Chapter 1 evidence and all
original Chapter 2 obligations remain preserved.

Only this dedicated report and the author's existing implementation handoff
are written for this task. No Lean source, Git ref, candidate, dependency,
compiler output or cache is changed. The unrelated partial ZIP stays explicitly
untracked and unchanged at 23,068,672 bytes, SHA-256
`c6795852cc57d6210e2fbe7d509a10c4e3caf5cfe3fce4d9c32983ba45193711`.
After the handoff, **HOLD all author source/ref/control writes** until root's
next instruction.

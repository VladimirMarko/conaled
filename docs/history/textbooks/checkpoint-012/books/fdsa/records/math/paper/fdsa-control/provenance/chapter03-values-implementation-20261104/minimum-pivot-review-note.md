# C03-078: measured minimum-pivot paths — author statement and case assessment

Candidate: `eaea222672013a67c4e84cf7bf8adae418be0cf6`.
Tree: `f059c9e0920a244f331565fda94116fc1f847dc5`.
Stage parent: `17901d09d155b93de6490dfa40ca17f988107b94`.
Whole Chapter 3 review base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`.
This is an uncompiled implementation candidate. No author Lean/Lake, emitted-type
capture, whole-project audit, independent Chapter 3 reviews, immediate verification
or acceptance is claimed. Root owns the qualified one-thread compiler.

## Scope and source

The frozen inventory remains all **83** canonical obligations, SHA-256
`eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed`.
This slice addresses C03-078, the deterministic minimum-pivot paragraph on book
p35. The authoritative requirement corrects the paragraph's missing rank and
distinctness qualifications. Its exact path assertion is for a distinct input
of length `n`, valid zero-based rank `k<n`, and sufficient administrative fuel.
It requires `k+1` active invocations, `k` recursive edges and scan volume
`(k+1)*n-k*(k+1)/2`; only largest-rank specialization is uniformly quadratic.
The pinned book is the already recovered local source, not a new web edition.

Three new source modules contain 52 public declarations and no named private
helpers. All previous 15 files, 350 public declarations and seven named private
helpers are preserved byte for byte. Their identities are in the starting-state
record. This gives 18 owned source files, 402 public names and seven named private
helpers in the cumulative author branch. Generated declarations remain in the
eventual full-module/audit scope.

The generic source is deliberately small: an existing `Measured` pair carrying
an optional value and list of active sizes, a result-prepending operation, and
a fuelled execution that erases to the accepted three-way selector. There is no
new class hierarchy, unrelated shared prefix or change to existing entrypoints.
The probability branch was considered in coordination with root; its checked
occurrence-index sampler does not charge construction of a minimum or balanced
pivot, so it cannot serve this deterministic policy exercise directly.

## Actual execution and observation meanings

`Resources.SelectionPolicy.runWith` executes, at every nonempty active state:

1. The measured input-length traversal, whose returned size enters the trace.
2. The supplied measured pivot constructor. Both its returned pivot and charge
   are used; the execution does not substitute a predicted pivot or assign its
   cost afterward.
3. The accepted measured one-pass three-way partition, using its returned
   lower/equal/greater buckets.
4. Measured lengths of the returned lower and equal buckets. Both are charged
   before branch dispatch, including a lower branch.
5. Either the actual recursive result or the measured positional lookup into
   the equal bucket, plus one selector entry for this invocation.

Primitive arithmetic, comparisons, pattern matching, tuple construction and
trace bookkeeping have zero observation in this declared source-call model.
Trace recording is not claimed to be free physical allocation or runtime work.
The input-size traversal is intentionally included, so this is a declared
instrumented realization; its exact coefficient is not asserted to be the
book's uninstrumented implementation time. Fuel has exactly the administrative
role of the accepted `Applications.Selection.runWith`. It is supplied separately
and the sufficient-fuel theorem proves it cannot truncate the claimed values.
The exact valid minimum-path induction additionally reaches an equal branch,
never an empty or fuel-zero extension. No unpaid minimum search is assumed.

The trace contains active positive input sizes, including the final equal-branch
invocation. Empty/fuel-zero extensions have an empty active trace and one source
entry. Thus the valid path's edge count is trace length minus one. This is a
linear call chain: each nonfinal active invocation makes exactly one strict-child
call, and the final active invocation makes none. The exact path proof establishes
those facts through the actual branch equations. There is no claim that this
edge interpretation applies to an invalid-rank trace ending in an empty call.

For a distinct nonempty minimum-pivot state of size `m`, the lower bucket has
size zero, the equal bucket has size one, and the greater bucket has size `m-1`.
The minimum construction costs `m+1`. The measured input length and partition
also cost `m+1` each. The lower/equal lengths cost one and two, and this selector
entry costs one. A recursive step therefore costs `3*m+7`; the terminal equal
lookup adds one. Summing actual returned charges gives
`T = 3*W + 7*(k+1) + 1`, where `W` is the sum of actual active sizes. This identity
is separate from the book's exact scan-volume formula.

## Complete public-claim assessment

The exhaustive raw headers, lexical contexts, imports and source hashes are in
`minimum-pivot-inventory-v2.json`. These are source statements, not emitted
types. Contexts may contain variables that Lean will omit from declarations
which do not depend on them. The explicit-`@` program lists every public name;
actual type capture remains pending. The complete claim assessment is grouped
below without omitting any name.

### Shared execution: eight public declarations

| Names in `Resources.SelectionPolicy` | Domain and intended contribution |
|---|---|
| `Observed`, `prepend` | Universe-polymorphic payload and preservation of the actual child value/trace/charge. These operations require no element ordering. `prepend` adds one observed active size and this step's charge; it does not invent a child execution. |
| `runWith` | Any `LinearOrder α` and any measured optional pivot constructor, every natural fuel and zero-based rank, every list including empty and duplicates. The source uses actual primitive results in all three branches. No `Inhabited α` or default element is required. |
| `runWith_zero`, `runWith_nil` | Total optional extensions: none, empty active trace and charge one. They are not active valid source states. |
| `runWith_step` | A nonempty list and the actual pivot result `some p` suffice for the exact source equation. It does not assume pivot membership, rank validity or distinctness; policies outside the termination contract still have this finite-step equation. Every primitive traversal/lookup cost remains visible. |
| `runWith_value` | Erasure to the accepted source selector at the same fuel and rank, without pivot validity. Thus policy failure and invalid ranks are preserved as well as all three branch values. This is value preservation, not cost transport between arbitrary policies. |
| `runWith_correct` | An input-occurrence policy and fuel at least input length give exactly sorted optional indexing. Distinctness and valid-rank premises are deliberately absent: invalid ranks still return none and duplicates retain occurrence semantics. |

### Actual minimum specialization and analysis: 21 public declarations

| Names in `Resources.MinimumPivot` | Domain and intended contribution |
|---|---|
| `run`, `policy_valid`, `run_value` | Specialize to checked `Resources.FixedRank.select0Run`, whose value is the actual minimum and whose source cost is `n+1`. The valid-policy proof is discharged by the existing minimum theorem. Value correctness covers every list and rank with sufficient fuel, independently of duplicate patterns. |
| `minimum_bucket_sizes` | Distinctness plus a successful actual minimum result yield lower size0, equal size1, greater size plus one equal to input length, and distinctness of the actual greater filter. Membership and positive input length follow from the successful minimum. These are justified intermediate facts, not assumed path lengths. |
| `run_zero_rank` | Every distinct nonempty input stops after its first minimum pivot for any positive fuel. Actual result is the computed minimum, trace `[n]`, charge `3*n+8`. No full-length fuel assumption is necessary for this immediate terminal case. |
| `run_succ_rank` | At a distinct nonempty state with actual minimum `p`, a positive rank takes the actual greater bucket and subtracts one. The exact `3*n+7` step tariff includes minimum construction. This step equation also holds for invalid positive ranks; the recursive observations theorem separately restricts to valid ranks. |
| `sizes`, `sizes_length` | A natural-number reference list `n,n-1,...,n-k`, using total natural subtraction. Length is always `k+1`; mathematical positivity/sum statements carry `k<n`. The reference list alone is not used as evidence of an execution. |
| `run_observations`, `run_trace` | Under `Nodup`, `k<n`, and `n≤fuel`, induction through actual minimum choices and actual greater buckets proves the recorded trace equals `sizes n k`, and proves its accumulated charge. Recursive hypotheses preserve distinctness, valid rank and enough fuel using the proved bucket-size equation. |
| `active_calls`, `recursive_edges` | The actual valid trace has `k+1` entries and `k` inter-invocation edges. The terminal equal branch is counted as an active invocation. Singleton/zero-rank cases have zero edges. |
| `sizes_sum_double`, `sizes_sum`, `sizes_sum_bounds` | For every natural `n,k` with `k<n`, the doubled subtraction identity implies the ordinary natural-division formula and bounds `n≤W≤(k+1)*n`. No floor/real coercion, parity assumption or asymptotic approximation replaces the exact formula. |
| `scan_exact` | Transfers that arithmetic to the trace of the actual minimum execution. Scan volume is the sum of active input lengths, counting occurrences, not a comparison or source-call counter. |
| `cost_exact` | Transfers the induction's accumulated source charges to actual trace sum: `3*W+7*(k+1)+1`. The final extra one is the terminal lookup. |
| `fixed_rank_linear` | For each valid fixed `k`, all distinct inputs satisfy `n≤T≤(10*(k+1)+1)*n`. The upper coefficient may depend on the fixed rank but not on the input length, order or values. This does not assert a single linear constant for growing ranks. |
| `largest_scan_double`, `largest_scan` | For any distinct nonempty list and sufficient fuel, rank `n-1` gives `2W=n(n+1)` and `W=n(n+1)/2`. Nonemptiness prevents natural subtraction from silently turning an empty largest rank into zero. |
| `largest_cost_quadratic` | For the same largest-rank family, `n²≤2T` and `T≤11n²`, explicit positive uniform constants witnessing quadratic growth in this actual source tariff. It does not generalize to every rank or repeated input. |

### Connected consumers: 23 public declarations

`Examples.MinimumPivot.input` is the independently chosen unsorted list
`[3,1,4,2]`; `input_nodup` discharges the exact-path premise. Kernel reduction
examples check actual returned values, traces and charges, while separate
consumer theorems invoke the general public results. A finite calculation alone
does not replace any universal result.

| Consumer names | Expected mathematics and connection |
|---|---|
| `middle_execution`, `middle_trace`, `middle_calls`, `middle_edges`, `middle_scan`, `middle_cost` | Fuel4/rank2 returns3, trace `[4,3,2]`, three active calls, two edges, scan9 and actual charge49. The trace, entry, edge, scan and charge claims separately consume `run_trace`, `active_calls`, `recursive_edges`, `scan_exact` and `cost_exact`. The full execution also reduces the implemented constructor/partition/lookup. |
| `largest_execution`, `largest_scan_connected` | Same unsorted input/rank3 returns4, trace `[4,3,2,1]`, charge59, scan10. The scan specialization uses the universal triangular theorem. |
| `minimum_execution`, `minimum_is_not_four_calls` | Same input/rank0 returns1 after one active invocation with charge20. The inequality against four calls uses the universal active-call theorem, demonstrating the rank qualification in the corrected book statement. |
| `duplicate_execution`, `duplicates_are_not_four_calls` | Four copies of7/rank3 return7 immediately, trace `[4]`, charge26. The measured equal-block length and sequential lookup are both paid. The trace has one active call, so an unqualified distinctness-free four-call assertion is false. The exact distinct-input formula is not applied here. |
| `singleton_execution`, `singleton_edges` | Integer singleton `[-4]` returns−4, trace `[1]`, charge11; the general edge theorem gives zero edges. This exercises a different ordered type and the one-entry/zero-edge distinction. |
| `empty_execution`, `invalid_value` | Empty input/fuel0 uses the optional extension. Rank4 on the four-element input returns none through the universal erasure/correctness result and sorted-length correspondence. No cost or valid-path theorem is applied to the invalid rank. |
| `range_worst_scan`, `range_worst_calls`, `range_worst_edges`, `range_worst_quadratic` | For every `n : Nat`, `range(n+1)` is distinct and nonempty, largest rank is `n`, fuel is `n+1`, and the general exact/quadratic results apply. Sizes grow without bound, so these are an infinite-family witness including its singleton start. |
| `fixed_third_linear` | For every distinct `List Int` with at least three entries, zero-based rank2 has `n≤T≤31n`, obtained from the generic fixed-rank theorem. The four-element concrete middle example makes this premise visibly satisfiable. |

## Preparation findings and validation status

Before the first commit, read-only API checks corrected two guesses: pinned
`List.nodup_range` has an implicit natural parameter, and the pinned minimum
lemma is `Nat.zero_min`, not `Nat.min_zero_left`. The zero-rank proof now uses
an explicit definitional arithmetic target. These are preparation refinements,
not claimed compiler failures. Their record is `minimum-pivot-precommit.json`.

After generating the lexical inventory, full header readback exposed
**C03-MINIMUM-PREP-001**: the naive first-`:=` delimiter truncated the statement
of `runWith_step` at its internal `let t := ...`. The original inventory and its
receipt are preserved. The separate v2 inventory restores the full unchanged
statement, with an exact original/corrected header diff in
`minimum-pivot-preparation-correction.json`. All 52 names, source bytes, candidate
and explicit type input remain unchanged. This is a preparation-method finding,
not a mathematical/source failure and not a relabeled type execution.

Static staging checked the three-file scope, absence of prohibited proof tokens,
and whitespace; prior15 source hashes were checked exactly. These checks do not
establish Lean elaboration, axiom closure or intended mathematical correctness.
All three focused targets are requested from root. Until actual terminal evidence
arrives, the entire new slice is uncompiled. The universal arithmetic proofs and
exact source-normalization proofs require that real compiler check; no tactic or
API outcome has been invented.

## Remaining work and integration boundary

C03-080 will reuse this executor, prove its actual positive trace obeys the
halving relation under a pivot contract, connect actual charged step costs to
the trace, and discharge the contract for a concrete measured balanced pivot
when the exact nested selector is checked. Root authorized only the exact two
HalvingTrace files at `45d120ce0f5bacbaac76cbceeca13ee3ff494dff`; none is copied or
imported in this slice. No halving-policy claim is marked complete here.

C03-055 and the actual algorithm side of C03-058 still wait for the checked
nested-selector API. Root separately owns the scalar generalized-group part of
C03-058; it is not duplicated. All 83 chapter obligations, actual type capture,
full candidate check/audit, both independent review axes, immediate verification
and integration remain in the original loop.

Requested future integration imports are these three modules, normally reached
through `Examples.MinimumPivot`. No shared entrypoint or reconstruction-map
file was edited concurrently. Documentation integration should identify this
explicit tariff and the rank/distinctness qualifications rather than suggesting
the scan formula itself is a raw runtime-cost theorem.

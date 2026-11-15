# Fixed-rank exercise slice: source assessment and handoff

Candidate: `fd490573dc6a0ad2ed4a6f3d449e03d9d1b0bb2f`.
Stage base: `bc26994a828eb958fe930c0e46039f9c5addc864`.
Whole Chapter 3 review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

This is an **uncompiled development candidate** for C03-047–051. No Lean/Lake
command, actual-type capture, full candidate build/audit, independent review,
or Chapter 3 acceptance has been performed by this author. The static source
assessment below does not replace those gates. The complete frozen Chapter 3
scope remains all 83 obligations; C03-053–058 remain assigned for later slices,
and C03-052 remains with the query author.

## Source scope and fixed baseline

Only these three new files differ from the stage base:

| Module | Public declarations | Private declarations |
|---|---:|---:|
| `Applications.Selection.FixedRank` | 36 | 1 |
| `Applications.Resources.FixedRank` | 23 | 0 |
| `Examples.FixedRankSelection` | 27 | 0 |

All six previously focused-passing value/chunk/pivot source files were checked
against `fixed-rank-starting-state.json` and remain byte-identical. No accepted
branch, shared root, reconstruction map, canonical controls, dependency or
tooling files changed. This slice requires no absent XR or pending median
worker import. All source-header declarations, including the private helper,
are recorded in `fixed-rank-inventory.json`. The explicit-argument program
`FixedRankStatements.lean` queues exactly all 86 public names using `#check @`.

## Intended algorithms and statement assessment

### Minimum: C03-047

`minimumLoop best xs` consumes one input tail at each recursive call and updates
the accumulator to `min best x`. `select0` returns `none` on empty input and uses
the first occurrence as the initial accumulator otherwise. Neither definition
requires a global inhabitant or sentinel. `minimumLoop_spec` proves membership
in the observed candidate plus remaining list and a lower bound against every
occurrence. The optional-value, minimum, occurrence-rank, pivot-membership and
nonempty-existence statements all follow from that actual loop. Their domains
and quantifiers preserve duplicates and do not impose `Nodup`.

`minimumLoopRun` is a separate instrumentation of the actual minimum loop,
with a tail-position recursive call and accumulated cost. Its erasure equals
`minimumLoop`; its cost is `spent + length xs + 1`. `select0Run` charges its own
entry and therefore costs exactly `length xs + 1` for every input. This supplies
fixed constants A=1, B=1 directly. The value equality between `select0` and
`selectFixed 0` is never used to transport their costs.

### Bounded sorted prefix and general fixed rank: C03-049, C03-051

`boundedInsert m x acc` performs ordered insertion and then takes the first
`m` entries. `prefixLoop` traverses the original input exactly once in tail
position. Its accumulator can be traversed by insertion and taking, but after
each step has length at most `m`. The private truncation lemma holds for every
list, including unsorted ones. `ordered_cons_eq_insert` uses the already proved
canonical merge-sort/insertion-sort value correspondence.

The invariant identifies the accumulator with the first `m` sorted occurrences
of the observed history. The `reverse` in its statement describes that history;
the algorithm performs no reversal. Starting with an empty accumulator gives
`takeSort m xs = take m (ordered xs)` and its exact length. `selectFixed k` uses
width `k+1` and zero-based sequential lookup at `k`. Its optional value is the
canonical sorted optional index for **all** ranks. It succeeds exactly at the
existing duplicate-aware `RankedAt` relation, equivalently the two strict count
bounds, and fails exactly when `length xs ≤ k`. Valid-rank existence is proved,
so the success contract is not a vacuous implication. The shared public
selector is related at one-based rank `k+1`; its failure convention is unchanged.

The measured construction executes the existing measured ordered insertion,
then measured take on that actual result, then the next input-tail iteration.
It finally executes the existing measured sequential lookup. Every explicitly
named function entry is charged once; primitive comparisons, min/max,
constructors and matches have zero observation under the declared source
tariff. The exact bounded-insertion cost is insertion's actual count plus
`min m (length acc + 1) + 2`. If `length acc ≤ m`, this is at most `2*m+3`.
The outer entry adds one per occurrence. `takeSortRun` consequently has bound
`(2*m+4)*n+2`, and the selector has the uniform bound

```
TselectFixed k xs ≤ 2*k*n + 6*n + k + 4,  where n = length xs.
```

The four witnesses are explicitly 2, 6, 1, 4 and precede both rank and input
quantifiers. The bound is proved for all inputs, including invalid ranks; its
valid-rank existential specialization matches the exercise. The linear term
survives at k=0. No wall-clock, allocation, compiler tail-call or native-runtime
claim is made. The universe/type and `LinearOrder` assumptions are explicit in
the source context; their elaborated forms remain pending the queued capture.

### Specialized second occurrence: C03-048, C03-050

`select1` initializes two candidates with min/max, then `secondLoop` updates
them in a single pass. When a new value is at most the lower candidate, the
previous lower candidate becomes the upper one, including equality. Thus two
equal minima remain distinct occurrences. Empty and singleton inputs return
`none`.

The proof first establishes exact one-step and recursive-loop identities
between the width-two bounded-prefix implementation and this specialized
implementation. These identities do not assume the final rank contract.
`select1_eq_selectFixed` is then proved, and only afterward are its canonical
value, occurrence correctness, failure and existence theorems derived. This
respects the exercise's requested proof order. No separate source-cost theorem
for `select1` is claimed; C03-051 instruments the general fixed-rank algorithm.

## Retained cases and connections

The examples' expected values and counts follow from ordinary sorted-occurrence
arithmetic and the declared recursive-entry tariff. They are not selected to
match compiler output. The cases consume public results; concrete `decide`
calls remain kernel proofs once elaborated and do not use native evaluation.

| Case names | Independent expectation and public connection |
|---|---|
| `minimum_example`, `minimum_duplicate`, `minimum_empty` | Minimum of [8,1,5] and [4,1,1] is 1; empty input fails. Use the minimum and failure equivalences. |
| `minimum_execution`, `minimum_empty_execution` | Three occurrences cost 4 and empty input costs 1. Use `select0Run_exact` and the semantic examples. |
| `duplicate_prefix`, `zero_width_prefix` | First three sorted entries of [4,1,7,1] are [1,1,4]; width zero is empty for every input. Use `takeSort_value` and independently established sorted permutation. |
| `prefix_with_history` | Starting from the retained history [2,5], reading 4,1 keeps [1,2]. Uses the general accumulator invariant with nonempty prior history. |
| `two_loop_correspondence` | Starting candidates 1,4 and observing another 1 exercises the exact specialized/general loop identity. |
| `second_duplicate`, `second_distinct`, `second_singleton` | Second occurrences are 1 in [4,1,1] and 2 in [3,1,2]; [7] has no second occurrence. Use the actual algorithm equivalence, strict counts and failure theorem. |
| `second_exists` | Any list with two explicitly supplied occurrences satisfies the length premise and returns a ranked occurrence. Uses `select1_spec` with a discharged, satisfiable premise. |
| `fixed_zero_is_minimum`, `fixed_last_occurrence`, `fixed_invalid_rank` | First rank gives the minimum, last valid rank gives 7, and rank equal to length fails. Use the value correspondence and rank/count/failure results. |
| `book_index_two_is_public_rank_three` | Rank 2 in [4,1,7,1] has value 4 and corresponds to public rank 3. Uses `selectFixed_eq_selectWith` with established head-pivot validity. |
| `bounded_insert_at_head`, `bounded_insert_after_accumulator` | Width-two insertion before [1,2] costs 5; inserting after both entries costs 7. Use exact bounded-step cost plus the existing insertion head/all-not cost laws, and its value erasure. |
| `bounded_step_for_rank` | With width k+1 the per-step upper bound is 2*k+5, including k=0. Specializes the accumulator-length hypothesis and discharges the arithmetic. |
| `measured_rank_and_bound` | For arbitrary ordered payloads, independent strict-count hypotheses yield both the selected value and uniform source bound. Composes erasure, count correctness and measured cost. |
| `fixed_zero_execution`, `fixed_zero_bound` | On [4,1,1], three width-one steps total 19 calls; the uniform bound specializes to 22. Connects semantic erasure to the minimum and checks the actual source count separately. |
| `minimum_and_fixed_costs_differ` | On the same input the minimum algorithm costs 4 and the general rank-zero algorithm costs 19, despite equal values. Explicitly prevents an invalid cost transport from value equality. |
| `fixed_second_execution`, `duplicate_second_with_bound` | On [4,1,1], width-two rank one returns 1 with actual cost 22, below the uniform bound 29. Uses the specialized algorithm correspondence and the value/cost application. |
| `uniform_constants_include_minimum` | The same four witnesses precede all natural ranks and lists; the rank-zero boundary remains covered. Specializes the existential theorem to Nat. |

## Validation and integration preparation

Static checks established that only the three assigned new files were present,
the prior six sources remained unchanged, the new sources contained none of the
forbidden proof constructs, and `git diff --cached --check` exited zero. Full
source readbacks were `a51d03` and `7df0c6`; the static preflight was `1d926f` and
commit/precommit readback was `7cdcd8`. These checks do not establish elaboration
or acceptance. The original whole-scope requirements and all earlier records
are retained without relabeling any execution.

Requested focused targets, in dependency order:

1. `Applications.Selection.FixedRank`
2. `Applications.Resources.FixedRank`
3. `Examples.FixedRankSelection`

The integration owner should add the three module imports to the shared public
entry point and map C03-047–051 to these results in the reconstruction record
when composing the complete Chapter 3 candidate. I have not edited those shared
files. Root remains the sole compiler owner. Any actual elaboration/lint failure
must receive a preserved log, concrete correction, successor candidate and
unchanged full-scope statement assessment. All actual-type, full candidate
check/audit, both independent review axes and immediate verification gates
remain mandatory before acceptance.

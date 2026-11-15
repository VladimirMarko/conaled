# Natural-sort composition: static author assessment

Recorded 4 November 2026. Development base:
`5d7a479549f5acd64a9e5adb418ab48780c238ef`.

This records source/derivation review of all **105 public declarations** in the
four new owned files: 16 pure core, 22 value-example declarations, 37 measured
core, and 30 cost-example theorems. There are 99 theorem declarations, six
operation/fixture definitions or abbreviations, and no private source claims.
The exact declaration names, source statements, per-claim assessments and
connected cases are in `static-declarations.json`. Every source declaration
has exactly one record. This is not elaborated-type inspection, a compiler
pass, an exhaustive proof audit or either independent final review axis.

## Mathematical and architectural assessment

No concrete mismatch was found between the intended frozen source contracts
and the written statements/derivations. All four files were read completely.
Payload universes remain arbitrary, and key universes are independent. The
Boolean scanner and merge operations are supplied separately for law-free
value and count results. No payload order/equality/default/inhabitance class
is added. Sortedness observes keys and retains the existing weaker input-local
preorder/compatibility interface; the source specialization uses a linear key
order. The raw scanner/worker contracts and every checked existing source
file remain unchanged.

The pure operation is exactly `mergeAllBy cmp (runsBy lt xs)`. Permutation
composes the actual flattened-run and merge-all witnesses; multiset, length
and support derive from it. Input-local sortedness transports membership via
that permutation and composes the sorted-run and sorted-merge contracts,
without assuming the requested final result. Source key scanning uses strict
`<`, whereas merging selects the left record on `<=`. The general one-run
and chain laws need no merger order assumptions. Strict-descending value
laws retain only the operations and supplied strict relation, not a payload
order or unnecessary global order axiom.

The measured operation is the actual bind of `runsRunBy` into `allRun`.
Erasure follows from both component projections. The counter equation is
separate: actual scan count plus the actual merger count on its returned run
list. The known exact scanner count gives natural `n-1` and an unconditional
lower bound. No closure creation/application, key-evaluation, list constructor,
entry/dispatch, allocation or machine-runtime charge is introduced.

The adaptive upper bound uses total flattened length n and actual run count r:
`C <= (n-1)+n*Nat.clog 2 r`. Run count <= n and ceiling-log monotonicity give
the all-length consequence; the printed weaker `n+n*Nat.clog 2 n` and explicit
length-parameterized form remain separate. The source integer-ceiling bridge
is reused, including zero and one. The sharper integer statement casts the
whole truncated natural `n-1`, so empty input never acquires a negative scan
term. Generic merger premises still permit arbitrary and empty inner runs.

Sorted nonempty input yields one actual run, zero merge comparisons and the
exact measured pair `(xs,n-1)`; the empty equation is separate. Strict descent
similarly yields `(xs.reverse,n-1)` without a general sortedness/stability
claim for an arbitrary strict relation. Eventual growth derives only from
these proved-target numerical bounds: general O(n log2 n), O(n) under a
proved fixed run budget, a general eventual scan lower bound, and Theta(n)
for sorted length-indexed families. The lower estimate n<=2*C visibly starts
at n>=2. No positive bound is asserted at n=0/1.

## Independent expected cases and proof connections

| Case | Expected value/observation and connection |
| --- | --- |
| Empty payload and singleton | Public pure/measured boundary equations; costs zero, no payload instances. |
| Sorted `[0,1,2]` | One run, zero merging, complete count2, through sorted one-run laws. |
| Strict descent `[2,1,0]` | Reversed run, complete count2, through strict-descending law. |
| `[3,1,2]` | Runs `[[1,3],[2]]`; scan2 and actual merge2, bind total4. |
| `[1,3,2,4]` | Existing checked scanner fixture plus actual merge3: total6. |
| `[1,3,2,4,0]` | Three unequal runs; scan4, first pass3, next merge1, total8; adaptive budget14. |
| Tagged `(3,A),(2,B),(2,C),(1,D)` | Output `(1,D),(2,B),(2,C),(3,A)`; scan3+merge3=6; concrete tie order retained. |
| Weak descent `(3,A),(3,B),(2,C)` | Two runs, scan2+merge1=3, exceeding minimum2; whole reversal would wrongly reverse tied payload order. |
| Four merger runs `[[],[2],[],[1,3]]` | Shared API returns `[1,2,3]`, comparisons2; no assertion that scanner emits empty runs. |
| Duplicate key2 | Full multiset preservation supplies count2, which support alone would not establish. |
| Arbitrary tagged payloads | Generic source keyed correctness and concrete cross-run key comparisons, without payload structures. |
| Input-local comparators | Separately established compatibility on the actual nonnegative input; existing negative-key counterexample remains. |
| Arbitrary comparator operations | Occurrences/length/support and lower/adaptive count bounds without a sortedness assertion. |
| Integer zero/one | Printed bounds specialize to0/1 while exact comparison counts remain0/0. |
| Constant-key repeated payloads | Exact n-1, independently proved run budget<=1, bounded-run O(n) and sorted Theta(n), including empty family member. |
| Natural ranges | Explicit pairwise range theorem proves every family member sorted; count n-1 and Theta(n). |
| Modulo-three range-map family | Verified length n supplies the general actual-execution O(n log n) theorem; no tightness claim. |

These are source-linked proof scripts, not newly checked successes. The
numerical expectations were fixed before source authoring. No expectation,
assumption, statement or linter gate was weakened to accommodate a compiler.

## Dependency and validation boundary

The previously checked six natural-run/comparison/list-builder source files
retain their exact hashes. Root reported the BottomUp comparison core and
examples passed focused attempt4 at clean unchanged
`6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b`, exit0,142.194 seconds. The resource
core hash `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826`
is identical to this author's exact5d base. I read the exact5d-to6d diff: only
proof elaboration in two BottomUp example declarations changed. The reused
`Examples.BottomUpCosts.all_two_runs` declaration is unchanged. Root's
integration must retain the corrected example source with hash
`12572e3395c681b18f266374732eb63b059a13eb0f76aef25400aefa8d54a136`.
This source branch was not further fast-forwarded or edited outside its four
owned new files.

Only static source/derivation, exact identity and scope/whitespace checks were
performed by the author. No Lean/Lake/check.sh command, cache operation or
other-worktree edit was performed. The full four-target build and actual
explicit/universe-visible inspection of all105 declarations remain for root.
First acceptance remains exact foundation f17cc6b after accepted Chapter1 R.
All independent final reviews, full validation/audit and immediate candidate
verification gates remain mandatory. No chapter/shared acceptance follows.

C02-110–112 XD01 builder creation/invocation, actual full-scanner work and
empty/single-run merge dispatch remain mandatory next work. The exact book
scope remains all112 Chapter2 obligations and the complete book. This bounded
comparison composition does not discharge operational work by value equality.

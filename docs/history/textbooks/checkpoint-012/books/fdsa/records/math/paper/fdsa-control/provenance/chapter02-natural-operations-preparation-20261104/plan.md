# C02-110–112: remaining operational proof dependencies

Prepared 4 November 2026 during the source hold after checkpoint 0087. This
refines the existing fixed tariff and ascending-path plan; it changes no
requirement, model, source or acceptance state. All prospective names below
are proof targets, not existing or checked declarations. This report is the
only write in this preparation. The author branch remains clean at
`9c5858d0feb56b42701ab1f84e5d9265b953cfea`.

## 1. Exact dependencies and reuse

The complete C02-110–112 clarification, XD01 frozen requirements, original
core/examples, current correction diff, retained provenance erratum, both
independent source assessments and the earlier natural-run readiness/operation
plans were read. The existing plan already fixes the tariff, worker bounds
and homogeneous expected counts; those choices are retained.

XD01's independently source-assessed candidate is
`62809ced86c561c7a6cce8b71e727177a3f17fb8`. Its minimal compiler correction is
`66e480cf6db359ebf97d761b804ebe5d6d946eca`: reserved bare `prefix` binders
become `pref`, and `buildFrom_appCost` explicitly normalizes one natural-number
successor equality. Public contracts and cases are unchanged. Corrected core
SHA-256 is `1853d98cd37b7c1de4bc4928a419b69e1eaf9f59530221b060b98bc8afbf235d`;
examples SHA-256 is `df9936f23d5e60afd562b921d5b4ab0075fa58e7c91efcf92eddc33aa4d5e1a1`.
Root's development integration record identifies
`e2db54211dfe3b2efd76904f1797a9460567ebbc` as the merge with this natural
sorter draft. This is development ancestry, not acceptance. Both retained XD01
source axes report zero new or unresolved source findings and remain Blocked
pending validation. The
first pending foundation remains exact `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`;
accepted R remains `07e480f6ec9958d4975bb90151005b84f2907614`.

| Existing interface | Exact role in the continuation |
| --- | --- |
| `Resources.Measured`, `pure`, `bind`; `CallCount.tick` and its value/cost laws | Sequence actual returned values and charge the already specified operations. No new carrier, executor, interpreter or observation class. |
| XD01 `Builder`, `Rep`, `AppCost` | Ordinary measured suffix callback; all-suffix value and cost contracts remain separate. |
| `createSingleton`, `pushRun_eq`, `pushRun_rep`, `pushRun_appCost` | Actual initial callback and ascending extension: creation 1 then 2 per push; each push adds 2 to application weight. |
| `buildFrom_cons`, `buildFrom_cost`, `buildFrom_rep`, `buildFrom_appCost` | Identify the actual no-restart path, excluding the supplied seed's earlier creation. |
| `toDList_apply`, `toList_toDList`, `toDList_pushRun` | Erase the same callback to the existing scanner's DList, without rebuilding it from a list or transferring costs from value equality. |
| `runsBy`, `ascBy`, `descBy` and their branch/chain laws | Same decisions, current-head convention, strict descending continuation and ascending ties. |
| `mergeAllBy_nil`, `mergeAllBy_singleton`; `BottomUpSorting.allRun_nil`, `allRun_singleton`, `allRun_value` | Exact source dispatch cases; zero comparisons in these cases receive the separate one-unit operational dispatch observation. |
| `sortNaturalBy_eq_mergeAll` | Identify the composed returned value after actual scanner output feeds the restricted base dispatch. |

## 2. Actual scanner operations and erasure

A source-specific resource module can define mutually recursive `runsOpsBy`,
`ascOpsBy` and `descOpsBy`, using the existing measured interface. Initial
ascending selection binds `createSingleton first`; continuation binds
`pushRun current f`; terminal/restart invokes that actual returned callback
once on `[current]`. Descending branches cons onto the actual supplied
accumulator. Restart passes the actual unconsumed `next :: rest` to the same
scanner. There is only one selected recursive successor per branch.

The fixed charges remain: one per scanner/worker entry and tested pair; XD01's
creation/application observations; one per direct descending cons, final
singleton suffix cell and emitted outer-run cons. A singleton callback's
entry already covers its local cons; do not charge that cons twice. Supplied
builders and descending accumulators already exist at worker entry.

Before uniform contracts are substituted, establish these exact equations,
where F(a) denotes `(f [a]).2` and W denotes the relevant cost projection:

| Actual branch | Work equation |
| --- | --- |
| runs `[]` / `[a]` | 1 / 3 |
| runs `a :: b :: rest` | 3 plus selected worker, using the returned singleton callback or direct singleton descending seed |
| asc empty tail | F(a) + 3 |
| asc continuation at `b :: bs` | 4 + Wasc(b, `(pushRun a f).1`, bs) |
| asc restart at `b :: bs` | F(a) + 4 + Wruns(b :: bs) |
| desc empty tail | 3 |
| desc continuation at `b :: bs` | 3 + Wdesc(b, a :: acc, bs) |
| desc restart at `b :: bs` | 4 + Wruns(b :: bs) |

Prove simultaneous erasure to `runsBy`, `ascBy lt a (toDList f pref rep)`
and `descBy` directly from these actual branches. Only ascending value erasure
needs `Rep f pref`; it does not need AppCost. Include the singleton-seed DList
bridge and use `toDList_pushRun` for the changing builder. Descending and
initial scanner erasure need no payload/order/equality/inhabitance assumptions.
The existing raw D-law worker retains its full semantic domain unchanged.

## 3. Builder path and representation-size dependency

Retain the earlier exact arbitrary-callback path lemma. If every adjacent
comparison on `a :: middle ++ [last]` continues ascent, put
`t = middle.length + 1`, `built = buildFrom (a :: middle) f` and
`applied = built.1 [last]`. Direct continuation induction must prove

```text
value(ascOpsBy lt a f (middle ++ [last])) = [applied.1]
work (ascOpsBy lt a f (middle ++ [last]))
  = built.2 + applied.2 + 2*t + 3.
```

The empty-tail base is separately `([value(f [a])], work(f [a])+3)`.
Neither path equation needs Rep or AppCost: the actual application result,
suffix and observation remain present. Use `buildFrom_cons`, not only an
extensional final-value equality.

For the initial source run `first :: middle ++ [last]`, use the actual program
`bind (createSingleton first) (buildFrom middle)`. With m = middle.length,
it returns a builder representing `first :: middle`, construction count
1+2m and uniform application count k=1+2m. Apply it to `[last]`. This supplies
the missing source-size invariant: if p=m+1 is the represented prefix length,
`k+1=2*p`. At the seed p=1,k=1; each actual push increments p by 1 and k by 2.
For r=m+2, prove `count+3=2*r` before `count=2*r-3`, separately for creation
and one application. Empty/singleton scanner inputs bypass this path.

This weight is unfolded callback-invocation occurrence weight, not distinct
shared creation events. Retain XD01's charged identity, padded empty prefix,
expensive supplied callbacks, repeated application and shared self-composition
cases. Arbitrary Rep/D-law functions do not acquire this size invariant.

## 4. Full scanner potential and single-run dispatch

Use the same mutual termination measures as the value scanner: input length
for runs and remaining-tail length plus one for each worker. Generalize the
actual builder and k in the cost induction. AppCost alone supplies the bound
for asc; no Rep, sorted-prefix premise or bound on a supplied accumulator's
length is needed. The frozen simultaneous bounds are

```text
Wruns(xs)         <= 6*xs.length + 1
Wasc(a,f,ys)      <= k + 6*ys.length + 5   if AppCost f k
Wdesc(a,acc,ys)   <= 6*ys.length + 5.
```

The missing arithmetic proof steps are small but essential. With m=bs.length,
ascending continuation consumes 4 and increases the deferred application
weight by 2, giving `4+(k+2+6*m+5)=k+6*(m+1)+5`. Ascending restart gives
`k+4+(6*(m+1)+1)=k+6*(m+1)+5`. Descending continuation gives
`3+(6*m+5)<=6*(m+1)+5`; restart gives equality with that bound. Initial
ascending and descending cases add 3 to worker bounds with tail length n-2;
the ascending seed has k=1. Empty 1 and singleton 3 satisfy the initial bound.
Thus no unproved disjoint-run sum or sharing assumption is needed.

For homogeneous paths, derive exact worker laws before the initial laws:
under an ascending adjacent chain and AppCost f k, Wasc=k+6*ys.length+3;
under a descending adjacent chain, Wdesc=3*ys.length+3 for every acc. Hence
for initial runs of length r>=2, ascending work is 6r-5 and strict-descending
work is 3r. Ties continue ascent. Keyed specializations use existing chain
consequences; generic operations and bounds remain comparator-law free.

The concrete remaining merger dependency is a local observation of its base
branches, restricted by `xss.length <= 1`. Match the actual xss: `[]` returns
`tick (pure [])`; `[run]` returns `tick (pure run)`; the two-or-more case is
excluded by the supplied domain proof. Prove value `mergeAllBy cmp xss` and
cost 1 for every cmp, including `[[]]`. On this proved domain also identify
the whole pair with `tick (BottomUpSorting.allRun cmp xss)` by its two base
laws. This adds no general merger tariff or new generic executor.

Bind the actual measured scanner output to that restricted dispatch, using
erasure to transport a hypothesis `(runsBy lt xs).length <= 1`. As in
`allRun`, a captured measured pair can expose the needed proof without rerunning
the scanner. Prove value `sortNaturalBy lt cmp xs` and exact work Wruns(xs)+1,
then the fixed bound 6*n+2. Sorted/strict-descending one-run laws and the empty
case provide the domain proof. Multi-run `allRun` remains comparison-only;
its traversal/control is not claimed to have this operational observation.
If Growth packaging is added, derive it from these inequalities (for n>=1,
6*n+2<=8*n), while preserving the separate exact comparison counts.

## 5. Independent connected expected cases

The following are hand-derived targets from the fixed source operations,
not compiler results. They must connect through public laws and actual branch
composition rather than an isolated evaluator or a restatement of code.

| Input / state | Expected output | Scanner/worker work | With allowed base dispatch |
| --- | --- | ---: | ---: |
| `[] : List Empty` | no runs | 1 | 2 |
| singleton arbitrary payload | one singleton run | 3 | 4 |
| `[1,2]` / `[1,2,3]` | unchanged single run | 7 / 13 | 8 / 14 |
| `[2,1]` / `[3,2,1]` | reversed single run | 6 / 9 | 7 / 10 |
| `[1,1,2,3]` | unchanged single run, retaining tie occurrences | 19 | 20 |
| `[3,1,2]` | `[[1,3],[2]]` | 10 | not in the base-only domain |
| `[1,3,2,4]` | `[[1,3],[2,4]]` | 15 | not in the base-only domain |
| `[1,3,2,4,0]` | `[[1,3],[2,4],[0]]` | 19 | not in the base-only domain |
| tagged keys `[3A,3B,2C]` | `[[3A,3B],[2C]]` | 11 | not a strict-descending single run |
| supplied f=`compose (singleton 1) (singleton 3)`, current 5, tail `[4,6]` | `[[1,3,5],[4,6]]` | 14, excluding seed creation | worker only |
| supplied f=`compose (singleton 2) (singleton 1)`, current 3, empty tail | `[[2,1,3]]` | 6 | cost law does not imply sorted prefix |
| descending current a, arbitrary already supplied acc, empty tail | `[a :: acc]` | 3 regardless of acc length | worker only |
| merger `[]` and merger `[[]]` | `[]` in both cases | dispatch 1 in both | preserves the distinct outer run counts |

Also retain generic suffix/seed laws and existing negative builder families;
do not replace arbitrary worker contracts with only initial-state examples.
The companion comparison observation remains `Cruns=n-1`, and the complete
natural comparison work remains scan-plus-merge. No operation charges are
added to those counters. No machine-time or stability result is inferred.

## 6. Completion boundary

Only this plan was written. No Lean edits, Git ref/index changes, builds,
cache changes or acceptance claims occurred. The next authoring slice needs
root's explicit source release and the reconciled XD01 dependency. It should
implement this actual scanner/client and its connected examples, retain all
existing value laws and counterexamples, then provide static per-claim review
and an immutable candidate for root's focused diagnostics. Full candidate
checks/audit, actual elaborated-type assessment, both independent axes and
immediate verification remain mandatory; the existing review records continue.

## Input identity at preparation

These hashes identify the local records and exact held source bytes read for
this refinement; historical statements in the earlier reports remain historical.

| Path relative to restored workspace | SHA-256 |
| --- | --- |
| `fdsa-control/research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `fdsa-control/reviews/chapter02-natural-run-costs-implementation.md` | `c5479ef5d7f52f70d440938dc212a08650801164ea7876e34d177fb0524c86f5` |
| `fdsa-control/reviews/chapter02-xd01-integration-readiness-20261104.md` | `78b37323c06c2b147d573f9b3349c3e8f8360b273a509ab48f82c3e2ea35890d` |
| `fdsa-control/reviews/difference-list-cost-requirements.md` | `cb215a33cce3dd258cca37b9d703522d19caf2da76767c01e573d268b3e92c4e` |
| `fdsa-control/provenance/chapter02-xd01-correction1-20261104/result.json` | `8ef82ba8683ef9a29d5182eee733af4be9fd1437fec58e79fa46db9a9ca97004` |
| `conaled-ch02-natural-runs/Applications/Sorting/NaturalRuns.lean` | `123c711b5f0cf05074155f3a0d9ae076aa80a8be482e7e6fc77626aa9db6fb1d` |
| `conaled-ch02-natural-runs/Applications/Resources/BottomUpSorting.lean` | `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826` |
| `conaled-ch02-natural-runs/Applications/Sorting/Natural.lean` | `e4b27eb275e9509b205da7ae25dd7829e664eb47617cb1602e6114eb5d264493` |

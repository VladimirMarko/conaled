# Finite delayed insertion and retained requests

Issue [#510](https://github.com/VladimirMarko/conaled/issues/510) supplies finite
insertion positions, delayed forcing, and a native retained-cache comparison.
It contributes to #459 R2/R7 without completing either requirement or the #149
book reconstruction. It follows the bounded experiment recommended by the
[#475 assessment](design-challenges/2026-11-11/demand-sharing/synthesis.md).

## Values and supported operations

[DelayedInsertion](../../Applications/Resources/DelayedInsertion.lean) accepts
arbitrary labels, including functions. Position `i` denotes
`xs.take i ++ x :: xs.drop i`; equal-valued outputs remain distinct positions.
`ordinary_position` connects each generated recipe to that independent account.
`ordinary_values`, `complete_values`, `completeAccumulating_values`, and
`completeRetained_values` connect complete outputs to native `insertsWith`.
No equality instance on labels or callback results is required.

`ordinary` retains delayed list recipes and wraps recursive recipes with
deferred prepends. `accumulate` carries an arbitrary measured continuation;
`accumulate_position` quantifies over that continuation before induction.
`accumulating_tail` retains an arbitrary appended tail. `accumulatingRecipes`
specializes the open continuation to identity with no
callback event, so the same identified delayed/cache adapter also consumes
accumulating recipes without an extra outer map. Both builders bind the
original suffix rather than reconstructing it inside the thunk.

`countOuter` runs the existing measured fold and retains construction events.
`prepare` uses that fold's returned count as the executable size. Its length
proof is erased; selecting a recipe does not run another length traversal.
`select` visits exactly `i+1` outer nodes, stopping at the selected cell.
The public delayed request applies the callback only after that recipe has
constructed its entire insertion prefix.

`retained` invokes existing `Storage.call` once with `Slots.storage`.
`Slots.setup` allocates one empty slot per admitted identity. Each generated
instance starts with its own setup state; a workload threads that state with a
fixed table and callback. There is no global cache or implicit cross-instance
reuse. `Valid table f` constrains the entire stored measured result. The stored
pair contains the value and full body trace, including the callback's returned
bill and recipe-selection events. Keeping this evidence lets a miss report
its work without evaluating the callback again; a hit ignores the stored trace.
This is stronger than validating the value alone or only its scalar bill.

The adapter uses the returned hit counter to choose its reported branch.
`retained_projection` preserves the exact native state and all four native
counters. `retained_models` proves an independent relation with read, write,
recipe, and callback premises. `native_correct`, `native_retains`, and
`native_repeat` reuse `call_correct`, `call_retains`, and `repeat_hit`.
`retainedRun_projection` connects the ordered consumer to existing `run`;
`retainedRun_correct` preserves output order and measured-result validity.

This scope has total pure callbacks, finite lists, nonrecursive payload work,
and no cache mutation by callbacks. It does not implement cycles, concurrent
forcing, eviction, effects, partial callbacks, or infinite payload spines.

## Event model and tariffs

Events record source operations in order. The model makes no claim about Lean
allocation, elapsed time, trace-allocation overhead, or runtime speedup. The
executable reference returns traces so tests can inspect them; trace reporting
is not itself assigned a permanent tariff. Clients can assign tariffs with
`price`; `reprice_sequence` uses existing `reweight_run` and requires only an
additive monoid, not commutativity.

| Event | Declared source observation |
| --- | --- |
| `input terminal` | Builder input dispatch, including the final nil case |
| `outerDispatch terminal` | Map/force/workload spine dispatch, including nil |
| `outerCons` | One constructed outer cell, including intermediate maps and returned result lists |
| `thunk`, `deferredPrepend`, `continuation` | Creation of the corresponding delayed closure |
| `payloadCons` | One insertion/prefix cons; the original suffix is retained |
| `outerObserve visits` | Native outer fold, with one visit per cell plus terminal observation |
| `request id`, `delivery id` | Identified request and its delivered result |
| `selection visits` | Recipe-list traversal through the selected cell |
| `lookup visits`, `hit`, `miss`, `update visits` | Actual native cache counters; lookup and update visits are not constant tariffs |
| `callback bill` | One callback invocation with its returned, possibly nonuniform Nat bill |
| `setupCells cells` | Native empty-slot allocation |
| `identities cells` | Full-run identity-list construction from the already counted size |
| `innerObserve visits` | Existing complete observer applied to the actual returned inner lists |

A miss records request, lookup, miss, recipe selection, prefix construction,
callback, update, delivery. A hit records request, lookup, hit, delivery and
performs no recipe selection or callback. Workload dispatch and output-list
construction remain outside these per-request events. Full runs retain builder,
count, identity enumeration, setup where applicable, request, and observer
observations. The full accumulating runner traverses its recipes directly, so
it needs neither an identity list nor a cache setup.

`Wraps`, `Ordinary`, `Accumulates`, `Body`, `Request`, and `Forced` specify
primitive transitions independently of equality to an implementation-reported
trace. Actual implementations supply their derivations. Their trace projections
are deliberately narrower than an arbitrary total program cost.

## Independent expectations and checked connections

For an input of length `n`, ordinary construction has `triangle (n+1)` outer
cells; accumulating construction has `n+1`. The recurrences are
`O(0)=1`, `O(n+1)=O(n)+(n+2)` and `A(0)=1`, `A(n+1)=A(n)+1`.
These projections omit other events without claiming those events are free.
`ordinary_body` and `accumulate_position` give `i+1` payload-cons events at
position `i`. Both full-body work theorems give

```
triangle (n+1) + sum (map (fun ys => (f ys).2) (permutations'Aux x xs))
```

Selection, setup, lookup, update, outer processing, and observer costs remain
additional. Callback order is preserved before taking the sum. Construction
and counting have no callback events; a selected request has exactly that
position's callback bill. Calling a nonzero-cost delayed thunk twice repeats
its work; `delayed_twice` retains both traces.

For `x=1`, `xs=[2,3]`, the outputs are
`[[1,2,3],[2,1,3],[2,3,1]]`. Ordinary/accumulating construction uses 6/3 outer
cells, full forcing uses 6 payload cons, and complete observation costs 19.
The native observer's formula is `flatten.length + 3*outer.length + 1`.
The implementation does not traverse a flattened list to compute this formula;
`observe_eq` obtains it from the existing observer theorem. Empty outer lists
cost 1; one empty inner list costs 4; insertion into `[]` yields `[[x]]` with
observer cost 5. An empty callback result still pays its inner terminal visit.

With two slots, requests `[0,0,1]` from empty state have native counters
`(hits, misses, readVisits, rebuiltNodes) = (1,2,4,3)` and setup cost 2.
Delayed recipe selection visits 4 nodes; retained misses select 3. Complete
forced-body bills `b0,b1` give `2*b0+b1` delayed versus `b0+b1` retained.
Equal results need not have equal bills: with callback bill 9, those bodies
cost 10 and 11 under unit payload-cons pricing. Retaining thus pays 21 body
units versus 31 delayed; this excludes the separately charged overhead and
does not prove an overall speedup. Under zero prefix-cons tariff and constant
callback bill 9, the callback-only projection is 18 versus 27.

The [checked examples](../../Examples/DelayedInsertion.lean) and
[public executable assertions](../../scripts/DelayedInsertionTest.lean) retain
empty, singleton, nonuniform callback, arbitrary-tail, function-label,
equal-result/distinct-key, stale-value, stale-bill, repeat-hit, rebuilding,
observer-after-hit, and order-sensitive cases. Literal callback schedules
`f0,f1,g0,g1` and `f0,g0,f1,g1` remain unequal even when their Nat sums agree.
The partial-spine boundary examples reuse existing theorems: unknown left end
blocks append fallback, completed nil permits it, and strict difference-concat
on an infinite outer stream is bottom. Finite cache entries do not implement
partial demand or change these laws.

## Statement review and source qualification

The checked position and continuation claims quantify over arbitrary input
lengths and supported callbacks. Callback charges come from actual callback
results, not an assumed constant. The continuation remains generalized through
recursive calls, including arbitrary appended tails. Position bounds are
finite-size proofs, not runtime length traversals. Cache correctness requires
validity for the exact fixed measured function; a prior cache's correct values
do not license stale bills. Independent read/write premises and the native
projection retain transition and counter meaning. Repricing preserves order
under additive monoids; no trace-fusion conclusion follows from Nat equality.

The [provenance ledger](delayed-insertion-demand-provenance.tsv) maps the selected
recovered obligations. Source members were inspected in the retained
checkpoint-233 ZIP and matched against the checkpoint-335 inventory delta,
which changes neither member. This is source inspection, not replay of the
archived proofs or independent verification of printed-book attribution.

The recovered source charges 2 for a nonempty seed payload and 1 for an empty
seed, and states `triangle n + 2*n + 1` as insertion forcing work. This child's
frozen contract retains the original suffix and counts only the inserted cons
plus preceding prefix cons, giving `triangle (n+1)`. These tariffs differ by
`n`; no equality between the historical scalar bill and this projection is
claimed. Dispatch and closure creation remain explicit separate events here.
The source's uniform-callback force theorem is generalized here to the ordered
bills of arbitrary callbacks.

Recursive permutation enumeration, its factorial growth and complete-permutation
observation remain with #459 R7. Head-of-concat through open ends, infinite
scheduling, partial retained progress, suspend/resume and deferred left-append
histories remain with R2 and existing owners. This child does not close R2,
R7, #459, or #149, and adopts no generic demand or heap framework.

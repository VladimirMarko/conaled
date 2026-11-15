# Measured traversals: alternatives and generality

Recommendation: retain `Resources.Measured` and the existing executable list operations; compare a small callback traversal against native `List.mapM` before choosing its implementation. The missing capability is traversal of actual measured callbacks with declared structural charges. It is not missing sequencing, a reason to replace the counter, or evidence that a general observation framework is needed. A source-model traversal and a native implementation can both qualify, provided each establishes the requested complete pair and execution order. This is an assessment, not adoption authorization.

## Evidence and strongest retention case

All repository declarations below refer to the read-only source checkout at `e80c51d968925be3809ba3acc3259de7041b504b`.

- `Applications/Resources/Measured.lean`: `Measured` is a pair; `bind` combines observations in order. `bind_assoc` needs `AddSemigroup`, the two identity laws need `AddZeroClass`, and `reweight_bind` uses additive homomorphisms between additive monoids. No commutativity is needed. These are already the algebraic ingredients for varying bills and ordered traces. `same_value_different_cost` establishes why value erasure cannot stand in for complete correspondence.
- `Applications/Resources/Workload.lean`: `run`, `run_cons`, `run_append`, `run_state`, and `reweight_run` supply an actual general measured transition executor. `run_observation` requires a state-independent observation law; it cannot discharge arbitrary state-dependent bills merely by choosing a scalar function. The executor itself supports such bills.
- `Applications/Resources/ListFusion.lean`: `map` and `map_work` charge a constant callback price, while `concat1` actually calls `ListAppend.weighted`. `Applications/Resources/ListExecution.lean` has constant-price folds and an explicit `foldlViaReverse_extra` theorem. These existing distinctions between equal results and different execution bills are worth keeping.
- `Applications/Resources/BinaryCounter.lean`: `bits`, `sourcePrefix_encode`, `incWithCost_eq`, `advanceWithCost_eq`, and `counter_run` already cover finite prefixes, actual increments, and their measured execution. Rendering is a new consumer of those states, not a new counter implementation.
- `Applications/Sequences/Permutations.lean`: `bySelection_eqn` retains ordered positional choices; `insertion_perm_selection` proves an outer permutation, not identical order. `insertsWith_eq_map` supports arbitrary callbacks with no equality requirement on labels. `Examples/Permutations.lean` provides `orders_differ`, `insertion_repeats`, `repeated_selection_count`, and function-valued applications. A traversal must preserve these scopes.

The strongest retention argument is compositional sufficiency: ordered additive pair composition already supplies the proposed generality, and the actual clients already expose the pure semantic distinctions needed to specify it. Replacing that foundation would introduce migration obligations without an identified mathematical gap.

The token renderer and delayed measured permutation generators are prospective consumers in the inspected pinned tree. The research documents describe their obligations; they do not constitute implemented two-client reuse evidence. The search found no `mapMeasured` or `concatMapMeasured` owner in integrated `Applications/Resources` or `SquareKit`.

## Competing designs

| Candidate | Capability and assumptions | Tradeoff to test |
|---|---|---|
| Local measured recursion plus existing `bind` and shared exactness lemmas | Can express each client's exact dispatch, callback, append and forcing order with minimal assumptions | Best when source schedules differ; risks repeating induction and reweighting proofs |
| Small measured map and concatMap operations | Can share callbacks, erasure, full pair equations and additive transport; no element equality or uniform-cost premise is needed | Must expose the charge schedule rather than silently choosing one that fits only counter rendering |
| Native `List.mapM`, with a lawful pair writer and charged callback wrappers | Reuses standard sequencing and list theorems, preserving varying callback observations and duplicate order | Native traversal does not itself report structural operations; explicit instrumentation still defines the source bill |
| A generic event program interpreted into bills/traces | Separates generation of events from reweighting and permits richer observers | Adds syntax and interpreter correspondence; no inspected client yet needs this machinery to obtain the required finite results |
| Explicit cached observation state | Can make subsequent forcing cheaper when the state transition records completion | Changes the intended behavior and needs cache correctness; an ordinary thunk alone cannot justify it |

Native traversal is a substantive alternative, not just a hypothetical precedent. In the locally installed pinned Lean 4.35.0 sources, `Init/Data/List/Control.lean:58` defines `List.mapM` by left-to-right callback execution with an accumulator and final reversal. `Init/Data/List/Monadic.lean:66` gives `mapM_cons` under `[Monad m] [LawfulMonad m]`; `mapM_append` and `mapM'_eq_mapM` have the same lawfulness requirement. These exact primary sources were inspected. A pair writer satisfying those laws is a paper-level construction from the existing additive identity and associativity laws; it was not implemented here. Avoid a broad instance change on `Prod` merely for convenience.

That native implementation can carry declared dispatch/cell charges in callback wrappers plus a terminal charge. Its resulting source-model bill does not automatically count the accumulator reversal's native execution cost. This is not a defect if the claim is explicitly a source model, as existing `ListExecution` documentation says. It is a defect in a proposed claim that those observations are exact native allocation/work without an additional operational model. Native implementation and source cost specification should be compared on their stated contracts.

A generic applicative traversal is also mathematically sufficient for independent map callbacks, using an ordered monoid observation. Recursive selection callbacks can still construct measured subresults before combination. It does not remove the need to select a concrete source schedule. A monad-only abstraction is therefore convenient rather than a demonstrated minimal assumption for every operation. Neither route requires commutative observations.

## Smallest useful correction and derivability

First write a single measured map equation and its event order, then build counter output and one permutation output consumer against it. Derive value erasure, exact accumulated bill, constant-cost specialization and additive reweighting by list induction from the operation, rather than adding proof fields for every law. For a proposed schedule that charges dispatch, then callback, then produced cell, then recursion, the paper equations are:

```
M f []       = ([], d)
M f (x::xs)  = let y := f x; let r := M f xs
                (y.1 :: r.1, d + y.2 + k + r.2)
```

The definition requires addition; reassociation and identity results require the corresponding algebraic laws. For natural bills the derived formula is `(d+k)*xs.length + d + sum (xs.map (fun x => (f x).2))`. For a noncommutative trace, retain the recursive equation instead of moving all structural events into one prefix or suffix. This schedule is a proposed test specification, not a claim that recovered sources selected it.

ConcatMap needs a separate decision: mapping all callbacks and then flattening can have a different event order from callback/recursive-tail/append interleaving. Even where natural-number bills agree, ordered traces can differ. `ListFusion.concat1` and `ListAppend.weighted_exact` already supply actual append charges; reuse them when their schedule matches the source. Do not make the generic name promise complete pair equality between arbitrary traversal reorganizations.

Delayed construction should return delayed payloads without executing their callbacks. Outer counting consumes the outer list. Complete observation forces each occurrence and then observes its actual inner spine. This can be layered around the same measured map; a new observation typeclass is not yet justified. Function-valued payloads and arbitrary appended tails must remain legal.

## Discriminating acceptance cases

These are proposed fixtures and paper calculations, not executed Lean checks.

1. Counter rendering: use the actual `BinaryCounter.bits 5`, whose digit lengths are `0,1,2,2,3`. A renderer producing decodable token lists with bill `length+1` has callback bills `[1,2,3,3,4]`. Under the proposed map schedule with `d=k=1`, total bill is `24`. Compare complete token lines, ordered callback trace and total; preserve the seed-inclusive indexing. Separately repeat a representation in the input list to check repeated callbacks and allow noncanonical `[false]`.
2. Permutation consumption: feed `bySelection [1,1,2]` to a callback retaining each list and charging `1+head`, using zero for an empty head. The six outputs have callback bills `[2,2,2,2,3,3]`; the same proposed map has total `27`. Check all six outputs in exact order, including repeated identical lists. Counter and permutation authors should use the same public traversal lemmas, not repeat its induction.
3. Ordering separation: callback observations for `[a,b,a]` must retain `[a,b,a]`, even though duplicates and a scalar sum cannot detect reversal of some fixtures. Include distinct `[a,b,c]` and structural events around each callback. Compare a direct interleaving concatMap against map-then-concat; require equality only if the event schedules actually match.
4. Delayed observation: payloads yielding `[[],[7],[7]]` distinguish empty-inner terminal work and duplicate occurrences. The research observer specification gives inner/outer bill `2 + 3*3 + 1 = 12`, before any separately charged callback work. Outer count must retain zero callback events. Full observation must retain all values, including the empty list, and record each callback bill. Sequentially forcing the same nonzero-cost thunk twice must include its bill twice.
5. Correspondence: compare the entire pair of a well-founded measured selection executor with adequate-fuel execution, not just its result or a bound. Include empty input, duplicates and nonuniform callback bills. Keep under-fuel behavior distinct. Preserve function-valued labels in the generic statements, so no accidental `DecidableEq` requirement can enter shared map/insertion APIs.

The decision test is author effort as well as finite results: compare repeated proof obligations and imported machinery in two independent consumers, plus noncommutative event correspondence. If the native implementation meets these tests with less local machinery, it should remain admissible even without an incumbent adapter. If precise source schedules make its instrumentation awkward, small explicit recursion is justified on that evidence.

## Limits and exposure

I inspected the pinned owners, their listed examples, recovered research/handoff documents, repository domain/architecture guidance and pinned Lean native traversal sources. I did not inspect other agents' reports, contact other sessions, edit target files, run builds, or execute the proposed fixtures. No external paper claims or Felix parity claims are made. Historical drafts and missing historical timing evidence were not treated as verification. The recommendation leaves source event scheduling, the concrete renderer and full delayed executor correspondence open for a checked author trial.

I had no prior task involvement supplied in this fresh assignment beyond the neutral brief and repository instructions. Fresh context reduces shared-history exposure but does not establish independent assumptions. No model diversity was established.

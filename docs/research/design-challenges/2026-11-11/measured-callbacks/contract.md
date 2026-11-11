# Measured callbacks: contract and foundations assessment

Recommendation: retain `Resources.Measured` and its order-sensitive sequencing. Try a small generic traversal, with separately declared structural charges and observers, before introducing a broader observation interface. Existing code already contains a callback-dependent traversal under `StructuredLinear.Costs.traverse`; extracting or generalizing its mathematics is a concrete alternative to inventing another owner. Local traversals using shared lemmas remain viable until both intended clients demonstrate the same operation and charging convention.

This assessment inspected commit `e80c51d968925be3809ba3acc3259de7041b504b` in the pinned checkout. No prior involvement in these implementations is present in my supplied context. I received the common brief and contract lens, read no other assessments, and used no additional agents. This provides context separation, not model diversity.

## Existing guarantees and retention evidence

`Applications/Resources/Measured.lean` defines `Measured α C` as `α × C`. `bind` adds observations in sequence. Its associativity requires `AddSemigroup C`; its unit laws require `AddZeroClass C`. `reweight_bind` requires additive monoids and an additive homomorphism. None requires commutativity. This already supports callback-dependent bills and ordered traces, with costs and semantic bounds kept separate. `same_value_different_cost` explicitly witnesses why erasure cannot establish exact execution correspondence.

`Applications/Resources/Workload.lean` supplies a stateful executor, `run`, whose `run_cons` is an exact measured recurrence. `run_observation` applies only when observations depend on the command independently of state, as stated by its universal `law` premise. `run_append` and `reweight_run` already discharge sequencing and transport obligations. Counter transitions are state dependent: `Resources.BinaryCounter.advanceWithCost` uses this runner, and `advanceWithCost_eq` proves the complete pair `(advance n bs, totalCost n bs)`. A new traversal should not replace this counter executor or assume its transition bill is command independent.

There is a concrete earlier varying-callback implementation. In `Applications/Linear/StructuredCosts.lean`, `StructuredLinear.Costs.traverse` consumes `X → Resources.Measured Y Work`, preserves list order and sums the returned callback observations. `traverse_value` and `traverse_cost` expose both projections; `workload` composes preparation with that traversal. `Applications/Linear/StructuredMeasured.lean:39` uses it for dense rows; `Examples/StructuredLinearCosts.lean` uses `workload` for repeated dense and sparse application. Its observation type is specialized to `Work := Event → Nat`, and it imposes no independent list dispatch charge. Its mathematical shape is the intended varying-callback map. Thus the research note's narrow negative search for names `mapMeasured`/`concatMapMeasured` does not establish that no such operation exists.

The pure permutation contracts are unusually useful retention evidence. `Sequences.Permutations.bySelection_eqn` gives the exact ordered recursion; `insertsWith_eq_map` preserves an arbitrary callback; `bySelection_map` needs no equality decision. `insertion_perm_selection` preserves multiplicities but deliberately gives only outer `List.Perm`. `Examples.Permutations.orders_differ` proves that insertion and selection enumeration orders differ. `Examples.PermutationSearch.enumerate_readout` and `repeated_order` provide an actual search composition sensitive to that enumeration. These distinctions must survive any measured layer.

## Laws to derive before asking builders for proofs

For an uncharged traversal `T f`, the following proposed equations suffice:

```
T f []       = ([], 0)
T f (x::xs)  = bind (f x) (fun y =>
                 bind (T f xs) (fun ys => pure (y::ys)))
```

Under additive-monoid observations, induction should derive the complete pair

```
T f xs = (xs.map (fun x => (f x).1),
          (xs.map (fun x => (f x).2)).sum).
```

This is a paper proof route, not a newly checked theorem. It is already specialized by the two `StructuredLinear.Costs.traverse_*` proofs. There is no need for callback uniformity, `DecidableEq`, a finite alphabet, or a proof field saying duplicate occurrences survive. Each list occurrence contributes once by the defining recursion. Equality of both projections implies pair equality by `Prod.ext`; demanding a separate exactness field would repeat a derivable obligation. Conversely, value equality plus a bill bound does not supply the second equality.

Pointwise equality of callback measured pairs gives traversal congruence. Reweighting by an additive homomorphism commutes with traversal by induction and `reweight_bind`. List append splits traversal into first-list then second-list traversal with concatenation of the resulting values, provided that concatenation is only semantic assembly in this uncharged operation. Charging an actual append requires an additional operation and bill.

A charged map must expose its structural convention. A possible Nat convention is nil cost 1 and cons dispatch/output-cell cost 2; the resulting exact bill is `2 * xs.length + 1 + sum(callback bills)`. That is a new operation definition, not a missing law of the existing uncharged traversal. `ListExecution.foldr` prices a pure callback by one fixed `c`; varying returned observations are not supplied by its `foldr_work` theorem. Building a charged map by that fold would also require checking callback execution order: the existing fold evaluates its tail result before applying the combining operation.

For concatMap, retain an exact recurrence using the callback's returned list and measured append. `Resources.ListAppend.weighted_exact` charges `(dispatch + cell) * left.length + dispatch`, including empty left lists. This gives a derived append bill from actual callback results. A pure flatten plus a length formula does not by itself declare when callback and append events occur. Specify that order before proving the total. The same exact scalar total can describe several distinct traces.

There is an additional law to reject unless restricted: traversing `fun x => bind (f x) g` generally differs from traversing `f` over all inputs and then traversing `g`. The first trace is `f₁,g₁,f₂,g₂`; the second is `f₁,f₂,g₁,g₂`. Scalar Nat totals can coincide while ordered observations differ. Monadic associativity does not permit this interchange. A shared layer must not import commutative-map fusion as an observation-polymorphic law.

## Construction, forcing, and the client contracts

Counter output should render the actual seed-inclusive state list. `BinaryCounter.bits` and `bits_values` already specify the zero-seeded list; arbitrary-seed prefixes and transition execution have their own existing declarations. Rendering callbacks may depend on digit count and return different token lists and bills. A shared traversal can preserve those results and accumulate those bills, but token decode laws and line delimiters remain renderer-specific. Mapping an already accumulated scalar transition cost to a singleton cannot recover the per-transition trace; the trace must be generated while stepping.

Insertion has an extra semantic boundary. A list of delayed callbacks can be constructed without calling them. Counting its outer spine should be independent of all callback results and bills. Forcing each occurrence once and traversing each returned inner spine is a separate computation. Representing a payload as `Unit → Measured (List α) C` does not provide a cache: sequencing two invocations adds two returned observations. Functional equality does not justify deleting either invocation from the measured program.

The recovered proposed observer bill `xss.flatten.length + 3*xss.length + 1` is compatible with an outer charged map costing `2*n+1` and an inner full observer costing `length+1`, when callback evaluation itself costs zero. With delayed callback bills, those bills must be added separately. Thus the advertised formula should either describe already materialized payloads or explicitly state how callback costs are included. Empty payloads still contribute an inner terminal event. This is a scope condition on a proposed observer, not a demonstrated defect in integrated code: the intended counter token renderer and measured permutation executors are not present in the inspected owners.

Fuel-free and adequate-fuel permutation implementations should agree in the entire pair under an explicit sufficient-fuel premise. Prove the operational recurrences match, including terminal dispatch and append costs, then use induction on input length. Existing pure `picks_remainder_length` supplies the termination decrease. `bySelection_mem_iff`, factorial output length, or asymptotic bounds cannot establish this exact correspondence. First-equal erasure and positional picks also remain separate operations even where their output memberships coincide.

## Smallest discriminating trial

Keep all current definitions. Write two independent consumers against either a generalized existing traversal or local traversals with shared bind lemmas. Compare their complete measured pairs to independent recursive specifications, then assess which proofs are reused.

1. Counter renderer fixture: render the five zero-start states `[], [true], [false,true], [true,true], [false,false,true]` with callback bill `1 + digit length`. Callback bills are `[1,2,3,3,4]`, totaling 13. An outer map using the example `2*n+1` structural tariff adds 11, for total 24. Compare exact token lists including line boundaries and a trace of each callback, not just 24. Separately verify the four-transition trace `[1,2,1,3]`; it is a different observation from rendering five states.
2. Insertion fixture: insert `1` into `[1,2]`, preserving `[[1,1,2],[1,1,2],[1,2,1]]`. Let the callback bill be `head + 2*second`, giving `[3,3,5]`. Verify both duplicate occurrences are charged and exact output order is retained. If distinguishing equal occurrences in the trace is required, tag positions before erasing their tags; a pure callback on equal values cannot distinguish occurrence identity by itself.
3. Delayed fixture: payloads return `[], [a], [a,b]` with bills `7,2,5`. Construct and outer-count without callback events; fully observe all three once, retaining all values. Under the observer convention above, inner/outer structural work is `3+9+1=13`, and callback work is 14, totaling 27. Calling the first thunk twice must contribute callback work 14 rather than 7.
4. Trace fixture: use noncommutative event concatenation for two inputs and test the failed fusion interchange above. Include empty outer input, empty concatMap blocks, and function-valued payload labels. Check callback and append-event ordering independently from scalar repricing.

These are proposed, manually calculated acceptance fixtures, not executed Lean checks. Universal induction theorems remain necessary; fixtures alone do not establish the contract.

## Evidence limits and next decision

Only read-only source inspection and paper derivations were performed. No builds, proof audit, benchmark, upstream comparison, tracker operation, or source modification was performed. Exact declarations are cited by file and namespace above; their source proofs were inspected, but this assessment does not independently rerun their validation. Historical counter/permutation drafts were not read as implementation authority. Concurrent #472 changes are excluded.

No defect was established in the inspected measured primitives. The established correction is to the inventory of existing varying-callback traversal capability. The remaining risks are introducing an unnecessarily large interface, losing order through commutative accounting, and conflating thunk construction with forcing. The smallest next decision is whether the two trial clients share only uncharged traversal plus client tariffs, or also one exact structural charging convention. That evidence should determine ownership and extraction scope.

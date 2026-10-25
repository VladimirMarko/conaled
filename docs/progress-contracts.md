# Finite termination and observation contracts

[Issue #146](https://github.com/VladimirMarko/conaled/issues/146) supplies an
experimental ordinary-Lean contract under `Applications/Progress/`. It follows
the [codata research](research/codata-elaboration-termination-contracts.md)
without selecting a universal source language or an unrestricted codata runtime.
The recursion compiler remains owned by #109.

`Machine S A` has a deterministic transition `S → Sum A S`. A transition either
returns a value or continues. `Evaluates step s a k` is an inductive finite
execution with exactly `k` transitions. Its constructors do not mention search.
`Terminates` existentially quantifies the value and count; `TotalOn` quantifies
over every initial state satisfying a precondition and retains its postcondition.
There is one permitted successor at each state, so no nondeterministic or
scheduler quantifier is hidden in these existential statements. A future
nondeterministic model would need to distinguish existence of a terminating run
from termination of every permitted run.

`search` recurses on supplied fuel and returns either a value with its transition
count, or `none`. `check` validates a proposed fuel/value/count certificate.
`check_sound` derives the operational judgment. `search_complete` applies only
to an already finite execution with enough supplied fuel; it does not decide
termination or discover a bound for all inputs. `none` is unknown, including
for a zero-fuel search on a machine that immediately returns. It is not a
certificate of divergence. The indexed `searchSquare` reuses #112's
`Optimization.membershipRep` and explicitly admits unknown results without
attaching a termination claim to them.

`sequential` is an actual two-phase transition machine. The first return step
switches to the second machine. `sequential_evaluates` proves that counts add;
`sequential_total` requires the first postcondition to imply the downstream
termination domain. It keeps the intermediate value in its conclusion.

## Producers and finite observations

A `Producer S A` can emit a value with its next state or take a silent step.
`Delivers` chains finite evaluations of the next emission and retains the
output list, final state and count. `Productive` requires a delivered list of
every finite length. Determinism proves coherence between arbitrary delivered
prefixes. Empty observation requires no steps.

A guarded coalgebra emits at every transition. Its source observation `unfold`
and final state `advance` are defined separately from evaluation and search.
`guarded_delivery` proves their operational realization in exactly `n` steps
for `n` observations. Map, zip and inclusive scan have finite-unfolding laws.
`unfold_transport` reuses a commuting state/value map for every finite length.
The checked toggle and parity scan have finite state, while natural-number
scan retains its computed accumulator rather than erasing it into existence.

The `paused` realization adds a Boolean phase. From phase false it takes one
silent step; phase true emits and resets. `guarded_paused_progress` proves
identical finite output observations with the same underlying final state and
counts `n` and `2*n`. Thus deleting the phase is a valid bounded realization
comparison, including progress. This is more than agreement conditional on
both machines returning: delivery itself is proved for every length. Unlimited
silent stuttering cannot satisfy these concrete bounds.

`filterProducer` emits only matches and otherwise takes a silent step.
`productive_of_next` identifies a sufficient invariant and finite next-emission
obligation. The toggle filter discharges that obligation with checked numeric
certificates. Filtering constant zero for positive values cannot produce one
output, while mapping those same values to `Option.none` emits an observation
at every step. No uniform filter productivity claim is made.

## Demand and composition

`Processor` holds operations: finite input demand, machine state, initialization,
transition and stream meaning. `DeliversWithin p work` is a separate law: for
every stream and requested output length, the initialized machine evaluates to
the specified finite observation within the bound. The meaning function is not
used by the evaluator. Determinism then proves causality with the stated demand,
and actual outputs from different requests are prefix-coherent.

Mealy processors execute an explicit finite-list machine and support map and
inclusive scan. Dropping a fixed `k` observations uses a different machine with
demand `n + k`. Composition runs the upstream processor to satisfy the
downstream demand and passes its resulting list to the downstream machine.
The proof derives demand `d_f(d_g(n))` and work `w_f(d_g(n)) + w_g(n)`.
Dropping two inputs and then mapping successor transforms `0,1,2,3,4` into
`3,4,5`: demand five, three upstream transitions and four downstream transitions.
Two drops also check nonidentity demand substitution. These are sufficient
uniform bounds, not a minimal-demand theorem or a model of adaptive filtering.

`mealy_realizations` crosses the producer/finite-list boundary: a coalgebra
feeds the same Mealy operation, and both actual traces deliver its unfolded
outputs. A map-then-scan example produces `1,3,6` with retained final state
`(6,3)` in three producer transitions and four finite-list transitions.

The finite-observation `mealySquare` and `composedMealySquare` use the existing
relational square composition. Their value-preservation field does not imply
progress. The independent `mealy_delivery` and `compose_delivery` proofs connect
the actual transition machines to those observations. No new compiler syntax
or duplicate relation composition machinery is introduced.

## Execution boundary and remaining work

The step function, element operation and list append are atomic in this model.
Concrete retained cases are executable Lean definitions; kernel-checked `decide`
proves small checker outcomes. General theorems allow ordinary total Lean
callbacks, including mathematical specifications. They make no claim that an
arbitrary noncomputable callback can run, or that evaluating a callback costs
one host instruction. Modeling partial element operations would require their
own evaluation/domain evidence before treating them as atomic steps.

There is no external environment here. Delivery assumes the abstract machine
can take each counted transition. Real input availability, cooperative scheduling
and fairness would be additional assumptions of a runtime refinement. A bound
on abstract steps is not a wall-clock bound or a scheduler guarantee.

Runtime termination, domain totality, finite-observation productivity and
causality have separate definitions. Fuel search terminates by structural
recursion regardless of program termination. Normalization of a language's
conversion procedure is a different property and is not proved here. No
unrestricted termination decision procedure, sharing/space theorem, lazy heap,
final coalgebra transport, target kernel change or host/target version split
is part of this delivery. The contracts leave those implementations open.

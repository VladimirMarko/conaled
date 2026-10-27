# Finite event scripts versus direct interaction contracts

Bounded interface experiment for [#194](https://github.com/VladimirMarko/conaled/issues/194),
following the [observation models](external-interaction-contracts.md#checked-observation-contracts)
and [authority-spike assessment](pre-conaled-authority-assessment.md).
This experiment compares two interfaces to the same independent obligation
contract. It does not implement an OS adapter or complete the effect-interface
research.

The result is limited but useful: generic interpretation removes repeated
sequence induction and permits reuse across obligation and captured-input
models. It does not remove the domain proofs, and the chosen script interface
does not enforce authority ordering. That limitation has a checked counterexample.

## Shared contract and two interfaces

[Obligation.lean](../../Applications/Interaction/Obligation.lean) models one
request's receipt, pending intent, local attempt count, external effect count
and settlement observation. Request values have an arbitrary type. The
specification requires no decidable equality, codec, numeric storage bound or
finite request universe. An executable admission function makes the narrower
choice of returning `Option State`.

`AcceptSpec` is defined independently of the admission function and interpreter.
It requires an empty initial state and an accepted result with matching receipt
and intent, zero attempts/effects and unresolved settlement. `tryAccept_iff` proves
both soundness and completeness for that contract; `admission_complete`
constructs a successful result from the input-only `Ready` premise. A recorded
acceptance therefore does not assert that an external effect has completed.
The model's atomic acceptance is not a theorem about durable physical storage.

`none` means rejection by this pure pre-effect admission function. It does not
stand for an external attempt that failed or whose effect is unknown. External
execution and missing replies retain their state changes explicitly. Observation
receives a `known` flag as model input; no claim establishes that an OS or remote
service supplies truthful confirmation.

The direct interface is `Relation.Comp (AcceptSpec r) LeaseSpec`.
`direct_contract` proves its independent `Leased r` postcondition, including
matching receipt/intent, one lease and no external effect. The event interface
interprets `[accept r, lease]`. `script_meaning` connects the independent event
meanings to the direct relation, while `event_contract` transfers that same
postcondition to the concrete handler. The specification is not defined as
whatever the handler happens to return.

## Reusable laws and connected cases

[InteractionEvents.lean](../../SquareKit/InteractionEvents.lean) supplies four
laws over arbitrary event and state types:

- `interpret_append` equates concatenation with relational sequencing.
- `interpret_simulation` lifts primitive simulations between potentially
  different state types and their relation to a whole script.
- `interpret_safe` specializes that result to transfer endpoint safety.
- `interpret_invariant` lifts primitive invariant preservation without caller
  induction over scripts.

The [checked examples](../../Examples/InteractionInterfaces.lean) use append
to combine actual acceptance/lease and effect/lost-reply executions. Simulation
connects that execution to the independent meanings. `script_bound` combines
invariant lifting with safety transfer to preserve request identity through
arbitrary admitted scripts. Re-acceptance with a different request cannot occur
within such a successful script because admission requires an empty state.

A captured-input handler separately consumes `interpret_safe` and the existing
`Snapshot.compile_sealed` theorem. It has no receipt or lease fields. Its
concrete mixed collection is still subject to the previous noncoherence result;
event interpretation adds no atomic snapshot guarantee. The earlier process
evidence and infinite interrupted-recovery models remain unchanged.

The examples retain explicit receipt mismatch, premature attempt, admission
collision and successful admission cases. Missing acknowledgement leaves an
effect count of one and unsettled knowledge; another execution increments to
two. The delayed-attempt example permits a second external execution after a
new lease. Since no target generation check is modeled, a local lease count
cannot exclude that behavior. This is a counterexample to inferring fencing,
not a demonstration of a bug in the earlier spike.

## Proof work removed and retained

This is a structural source comparison, not a measured programmer-time or
token-cost study.

| Obligation | Direct relation | Event interface |
|---|---|---|
| Admission meaning and conditional completeness | `tryAccept_iff` and `admission_complete` | Same proofs; not removed by syntax |
| Acceptance followed by lease | `direct_contract` explicitly reconstructs the result from the intermediate state | Reuses that theorem, but adds `script_meaning`, primitive handler soundness and a lifting application |
| General sequencing of a changed handler | Caller must establish the relevant relational compositions | One primitive simulation per event form, then `interpret_simulation` performs script induction |
| Stable request identity | Domain facts about admission and later transitions are still needed | `meaning_bound` checks the event forms once; `script_bound` needs no new script induction |
| Captured-input client | Existing `compile_sealed` provides its contract | Two handler cases plus generic safety transfer; no new authority-state requirements |

For the small acceptance/lease pair the event interface adds scaffolding. Its
demonstrated benefit is reusable sequencing and interpretation, not a reduction
in the semantic proof of that pair. The direct proof remains visible rather
than being replaced with a record asking the caller to assert the whole result.
Both interfaces still require assumptions about external observation and the
interpretation's treatment of atomicity and interruption.

## Negative result and next discriminating experiment

`script_is_not_authority` executes an effect from the empty state, without a
receipt, intent or lease. The current handler allows those transitions and the
list interface supplies no protocol enforcement. The successful pipeline's
postcondition must not be generalized to every script. A useful next comparison
should require enabled-state conditions or a protocol-indexed interface and
show how a caller obtains, transfers and consumes authority. It should reject
this exact history without assuming the desired whole-history property.

Finite event lists also cannot express response-dependent continuations,
unbounded retries or interruption inside a handler. Those are limitations of
this executable surface, not restrictions on the mathematical behavior sets in
`InteractionContracts`. No conclusion selects lists as the project's effect
language or rejects interaction trees. The next example should include an
unknown reply and an old outstanding attempt, with an explicit absence or
fencing contract, before choosing richer syntax.

The public entrypoint imports the examples and all new modules for normal
build and exhaustive axiom-audit coverage. No production tool, old spike source,
runtime adapter or proof-audit policy changed. #194 and the #195 migration gate
remain open.

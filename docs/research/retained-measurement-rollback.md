# Evidence produced during local rollback

Issue [#381](https://github.com/VladimirMarko/conaled/issues/381) extends the
[#373 comparison](../../Examples/StateException.lean) with an operation inside
the protected body. The old client captures a controller outside tentative
work. The new body writes the tentative cell, requests a measurement, receives
its selected controller, and raises with that controller. The handler returns
that exact selection. Both policies preserve the operation's history; Undo
restores only the tentative cell.

## Contract and construction

[RetainedMeasurement](../../Applications/Interaction/RetainedMeasurement.lean)
specifies `AttemptContract` independently of the interpreter. An unstarted
controller becomes started, retains the supplied observation, appends precisely
`issued` followed by `observed o`, and satisfies the existing `ResultValid`.
A started controller permits no further issue and leaves all evidence unchanged.
`attempt` implements this through Measurement's existing `begin` and `record`.
The observation argument represents the adapter response at that operation site,
not evidence recorded before the protected computation.

`ProtectedContract` additionally specifies the exact selected controller and
policy-dependent final local state. Both the direct `native` calculation and
the shared scoped interpretation satisfy it. `shared_native` compares their
whole outputs, including local state, retained controller and ordered event
history. This is a matched semantic comparison, not an author-effort measurement.

[RetainedException](../../SquareKit/RetainedException.lean) separates tentative
state `S` from retained operation state `R`. Both policies use the same output
carrier, exposing the last tentative state even on an unhandled exception.
The distinction lies in which local cell catch supplies to its handler. Thus
this carrier is not definitionally the old `Undo` carrier, which hides state
on unhandled failure. No equivalence of those stronger observations is claimed.
The #373 source and clients remain unchanged.

Operations and local laws are separate. `fold_bind` derives interpretation of
continuation substitution from constructor laws; `local_laws` supplies those
laws for a concrete operation interpreter. `scoped_retained` derives retained
relation preservation by induction over bodies and nested catches from local
operation preservation, reflexivity and transitivity. The measurement instance
uses exact ordered list extension. It does not assume whole-program append-only
behavior as an interface field. `nested_failure` derives the retained-state
handoff when an inner handler raises again.

## Checked cases and statement review

[Examples](../../Examples/RetainedMeasurement.lean) retain an unknown response
inside the protected computation. `unknown_retained` uses `exact_new_evidence`
and the existing `no_reexecution` obligation through `no_retry`. The expected
history is exactly two new events, even though the Boolean result is false.
`unknown_correspondences` supplies two worlds compatible with that observation,
one with no known exit and one with exit code zero. Unknown completion supplies
no evidence of nonoccurrence.

The negative cases reject erasing history and appending a second issue event
for an already-started attempt against the same `AttemptContract`. The actual
second operation is refused by `retry_refused`. `recomputation_fails` exhibits
different selected controllers with identical success flags. A recomputing
handler owes exact selection equality at each policy's resumed local state;
`recompute_contract` records that sufficient obligation explicitly rather than
assuming Boolean agreement preserves evidence.

The generic retention theorem quantifies over arbitrary finite syntax and
nested scopes and arbitrary initial retained state. In the measurement instance
it preserves any existing prefix, without assuming that prefix truthfully
records earlier physical events. The exact operation theorem appends its new
ordered pair to an arbitrary prefix. Controller validity is the existing
conditional success guarantee; unknown observations are allowed and satisfiable.
The examples also instantiate a good observation and derive physical completion
only under `Corresponds`.

The initial missing connection was that #373's tree had no operation constructor
and could only carry an already supplied controller. Its old rollback theorem
could not establish an append at an operation site. The new constructor and
local interpretation law supply that connection. Compile-time syntax and
elaboration corrections were ordinary implementation errors, not evidence of a
mathematical obstruction.

## Assessment and limits

Separating retained operation state from tentative state gives useful local
reuse: the same substitution theorem and retained-relation induction serve both
policies, including nested handlers and retries. The native route remains a
short direct calculation for this single operation. This bounded example does
not establish that a shared interpreter reduces total author effort.

An `issued` constructor records authorization in the mathematical model; it
cannot establish a physical launch. An adapter must connect authorized issuance
to actual execution, retain the controller across invocations, report the four
primitive observation correspondences truthfully, and preserve evidence across
whatever failures its environment allows. `physical_success` retains those
correspondence premises. This development supplies no production IO adapter,
crash recovery engine, concurrency semantics, or universal effect hierarchy.
Accepted-history storage has separate durability obligations under #240/#225.

A plausible shared blind spot is treating an event list as evidence of physical
occurrence merely because both native and interpreted calculations agree. Their
agreement checks the same mathematical model; it supplies no independent
physical observation. Another boundary is response availability: the model
supplies a finite response, with `.unknown` available for incomplete knowledge;
it does not prove that an adapter returns or survives process loss.

No incompatible architectural commitment was needed. Further operational
adequacy belongs to an explicitly selected adapter task under #225/#196;
preservation-family reassessment remains with #235. This experiment does not
activate #107, select #108's held-out theorem, or activate #260.

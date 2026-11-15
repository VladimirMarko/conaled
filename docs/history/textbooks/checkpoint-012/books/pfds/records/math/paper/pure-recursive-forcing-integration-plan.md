# Remaining finite-execution integration

This is the selected continuation plan after checkpoint019's local-step
development, not a completed proof. The general thesis claim remains open.

## Stable components

History/Simulation/Forcing now compile with their connected clients. Recurrence
provides positive-prefix nontermination and exact certificate expansion.
Creation and raw Recursive provide actual creation receipts, closed StateRep,
arbitrary-caller prefixes and inverses, and absence of body events strictly
inside the creation/closing prefix. Domain is green, including exact permitted
RHS decoding. Compatibility and its usable basis/negative pointer diagnostic
are green. No component assumes future termination for an unforced thunk.

## Active parallel components

DomainState (shared) supplies pure control/frame/config/result predicates and
preservation through actual step, finite Evaluates and Reaches. It permits
diagnostic faults and uses Domain.ParametersPreserve separately from primitive
representation compatibility. WorldDomain (ordered) supplies allowed immutable
meanings, fresh-delay composition, creation composition through PendingGroup,
and hereditary code validity of cached results via their actual pure witnesses.
Ordinary (map) handles the same-world/same-memory raw/pure steps and final
results outside delay, recursive declaration, suspended-address forcing and
normal/raised memoize-frame consumption. Its no-body-event fact identifies
the part of the raw execution that cannot be reentry. These three components
are uncompiled drafts at checkpoint019; do not treat their prose as evidence.

## Recursive macro and finite execution

Root will compose the actual recursive-creation prefix with one pure declaration
step, transporting old frames/histories through the immutable world extension.
The combined WorldDomain creation wrapper must retain the actual PendingGroup
witness; Creation.create_closed alone intentionally drops that provenance.
The source domain supplies permitted RHS shapes and distinct names, and its
decoder theorem recovers the exact source bindings. Pure DomainState preserves
the post-prefix code domain; the raw creation prefix contains no body event.

Prove finite correspondence by strong induction on the remaining actual raw
transition count. Ordinary, delay and force/cache laws consume one raw step;
the recursive macro consumes3*bindings.length+2 positive raw steps. Existing
prefix inversion recovers the strictly shorter residual evaluation. Cached
pure replay may be longer than the raw step; it is an already justified proof,
not an induction call. Compose the resulting pure prefix with the residual
pure evaluation, retain world extension and final StateRep/ResultRep, and obtain
the pure output domain from actual pure preservation.

For the source reentry claim, use the per-occurrence history at a forcing state
and the immutable meaning identified by its address. The next pure body entry
produces a positive recurrence; any alleged finite raw continuation would
produce a finite pure continuation by the same finite correspondence theorem,
contradicting recurrence. A whole-run formulation must retain occurrences along
actual raw prefixes. Ordinary transitions and the creation macro cannot hide
body events; one-step forcing cases expose their actual body-address event.
Do not infer whole-run absence of reentry from equality of final values alone.

Successful cache/write-count consequences are subsequent obligations. They
must retain the distinction between successful memoization, exceptions that
leave a thunk uncached, and independent allocations with equal pure meanings.

## Acceptance and branch order

All of this remains local10019 development. Its complete candidate still needs
the integrated stock build, exhaustive audit, matching record, independent
Standards/Spec and final verification. Main chapter frontier remains Chapter2.
Corrected import candidate324962e must finish its separate full gate/review;
then a Chapter2 candidate including those exact imports requires its own gate
and linked review continuation before Chapter3 implementation can start.

## Checkpoint020 continuation result

The plan above is retained as the original intended proof design. DomainState,
WorldDomain, Ordinary, RecursiveStep, Execution, Reentry, BodyEvent and NoReentry
now all have terminal green focused module/client records. The actual finite and
observed-entry bridges follow the stated dependency direction; the empty-heap
source cycle consumes the resulting raw theorem. See the execution and no-reentry
reports for exact statements and evidence. No full acceptance follows from these
checks. ValuePersistence and the recovered later-cache-hit source client complete
the remaining successful-cache portion; their own evidence is recorded separately.

# Local10019 recursive creation inside an active force

## Intended case and missing connection

An already active outer suspension at address0 evaluates a recursive declaration
that creates an unforced literal thunk at address1. Independently, the raw
creation/closing prefix is5 transitions; the pure descriptor construction is1.
The missing connection was preservation of the older memoize occurrence's actual
past-body witness across this creation and immutable-world extension. Neither
body termination nor active-address uniqueness was an acceptable premise.

## Implementation and statement review

Pure.Simulation.recursive_entry composes the existing source decoder, actual
create_closed_allowed receipt, raw caller-stack entry prefix and its strict
no-body-event law. It advances every older history by the actual pure recursive
transition after transporting immutable world entries. Its quantifiers retain
arbitrary caller frames and initial represented memory. Source CodeAllowed
supplies permitted RHS shapes and distinct names separately from effect purity.
The result retains exact raw3*bindings.length+2 versus pure1 counts; it does not
claim source/host cost equality. There is no primitive-call obligation in this
prefix and no eager body-evaluation or nonreentry premise.

The connected client consumes this theorem, then identifies the returned raw
and pure configurations by independently reduced prefix equations. Its initial
state is an actual allocation, the outer history is the zero-length body start,
and the active memoize frame's actual address is0. The conclusion retains that
history after allocating address1 and excludes body events strictly before the
reached body configuration. It neither claims that later body steps cannot
force nor substitutes bounded search for nontermination.

## Validation

The first focused check passed all761jobs with frozen source/config hashes,
under pinned Nix/Lean and default proof budgets. Core5.8s, client3.8s. No feedback
changes to mathematical statements or independent expected counts were needed.
Record: validation/suspension-pure-recursive-step-r1.json and matching log.
This is development evidence, not a complete candidate build/audit or independent
acceptance review. General finite correspondence and raw occurrence/no-reentry
remain the next obligations.

## Exact checked sources

- Applications/Suspensions/Pure/RecursiveStep.lean: `2708be3631118478ac1310dbc9c0aa908809ed8b0de6224b548bd5f91ef7d324`
- Examples/SuspensionPureRecursiveStep.lean: `b4e0c9a3c3f9214db1fb6a95be3da91192710cba368e8a6fe57e060fd767e20f`

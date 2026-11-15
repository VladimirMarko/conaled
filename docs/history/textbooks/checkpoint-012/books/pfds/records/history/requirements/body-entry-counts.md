# Local 10022 — conditional bounds on actual suspension-body entries

Version 1, 2026-11-03. Governing requests: REQUEST.md and
REQUEST-union-v2.md. This is an algorithm-independent semantic consequence
needed to connect memoization to later cost observations. The user's explicit
cross-cutting exception applies. Chapter 2 remains the earliest unaccepted
chapter; no later algorithm, exercise or complexity contract is accepted here.

## Motivation, source and fixed scope

Book pp.31–33 distinguishes memoized suspension evaluation from repeated
evaluation. The inspected Chapter 4 inventory and thesis Appendix A evidence
are in research/suspension-foundation-inventory.md, chapter04-readiness.md,
pure-cache-counts-source.md and union-source-identities.json. The existing
source evaluator includes uncached exceptions and retries, including the actual
two-body-entry, zero-write case. Therefore the unconditional statement that
every finite admitted pure program enters each body at most once is false.

Task 10020 proves at most one successful cache write for finite admitted pure
execution, and task 10021 preserves the actual retry counterexample. This task
must derive a distinct conditional body-entry theorem, expose the missing
execution premise, and connect its observation to the existing debit interpreter
only at the level actually proved. It must not revise either earlier result or
erase exceptions from the source language. Full body work, primitive costs,
source operation-incidence graphs and algorithm-specific complexity remain
10017 and the owning chapters.

Starting integration base is 577be121e074ddb5de6727a7481c115cb61b3b27, carrying
the unaccepted 10020/10021 candidates. Keep this as both bounded and original
integration review base across ordinary corrections. Record clean baseline,
development branch/materialization and all inclusions before editing. No
unrelated exclusion or pre-existing task work is intended. Semantic reuse is
from the existing raw machine, continuation laws, value persistence, pending
addresses, source nonreentry, observation and resource interpreter.

## Intended raw transition and prefix laws

An exceptional memoize unwind for address a means the actual current control
is a raised packet and the actual top continuation frame is memoize a. This
is a structural predicate on the existing configuration. It is not defined by
a desired event-count inequality or a guessed chronological graph.

For an actual continuing transition, a previously pending address must either
remain pending, be written by that transition's cacheWrite event, or be the
address of an exceptional memoize unwind. Prove this using the existing
continuation decomposition/lifting laws where possible. Do not replicate the
entire evaluator or introduce a replacement stack/event interpreter.

Use the ordinary property that the address currently has a value cell or a
pending memoize frame. A body-entry event establishes pending membership in its
actual successor. Bounded memory and absence of the particular exceptional
unwind preserve that disjunction along a continuing step. Finished answers
need no residual stack property because the existing observer is absorbing.
No uniqueness of pending frames, purity, totality or result-value constancy is
required for these raw one-step laws. Reference assignments at other addresses
and locally caught exceptions remain permitted.

NoMemoizeUnwind at address a quantifies over actual unfinished Prefix.observe
states and forbids that structural unwind there. Supply current-state and
actual-successor shift lemmas. This is an extra premise, not a consequence of
purity or finite normal return. A handler outside the body can return normally
after abandoning and retrying a thunk; the retained counterexample must still
exclude the premise.

Reuse existing FreshEntries for nonreentry. It is derived by the existing
finite pure source theorem, rather than assumed as a desired counting bound.
Under ConfigBounded, FreshEntries and NoMemoizeUnwind for the selected address,
prove at most one actual body event there for every observation budget. An
initially pending-or-value address has zero future body entries under the
applicable hypotheses. No initial pending-address Nodup premise should be
introduced unless the argument truly needs it. The raw bound must also cover
unfinished prefixes, faults and unused budget after a completed answer; it
does not assert termination of arbitrary raw configurations.

## Actual event observations and source specialization

Use the existing ordered FreeAddMonoid Event observation and unchanged
Resources.run. An ordinary additive indicator of a selected event is the
actual list occurrence count and the existing additive reweighting. Share
routine observation facts rather than create another evaluator or trajectory.
The existing cacheWrites projection must retain its public behavior; no
retrofit or proof-policy change is required merely to add a body projection.

Specialize the raw body-count result to the existing admitted finite pure source
domain, reusing finite_fresh_entries, StateRep/EnvRep, compatible primitives,
hereditary preservation, code/environment admissibility and a real finite
Evaluates witness. Discharge boundedness and fresh-entry conditions from those
results. Keep the additional per-address NoMemoizeUnwind premise explicit.
Neither normal final return alone nor cache-write uniqueness discharges it.

Project the same actual event list to its ordered body addresses. When all
addresses satisfy the derived count bound, prove that this projected list is
Nodup and that its length equals its finite support cardinality. Equal code
at independently allocated addresses must remain distinct identities.

Connect that observation to 10021's unchanged realization interpreter: label
each body event by its singleton address, other events by empty support, and
use zero unshared charge for this selected body-entry observation. Prove that
the interpreter charges the number of distinct body addresses generally, and
that it equals the actual body-entry count when the proved nonrepetition
conditions hold. This is a correspondence for body-entry events only. It does
not bound the transitions inside a body, treat every body as unit runtime work,
or close the full source/debit correspondence obligation.

## Connected cases and independent expectations

Develop checked uses alongside the theory, with independently justified
expectations preserved through proof repairs. Reuse existing public examples
where they already provide the intended observation. Required distinctions:

- A pending memoize frame under an ordinary appended stack survives a
  continuing transition; a successful return removes it and writes its actual
  address; a raised packet can remove it without a successful write.
- A first force has a prefix with one body entry and zero cache writes, while
  the frame is still pending. The universal body-count theorem applies to
  that unfinished prefix as well as later budgets.
- A successful repeated force enters its body once and subsequently hits the
  cache. Apply the general body-count result with its actual premises proved.
- A handler inside a body may catch an exception and return normally without
  abandoning that body's memoize frame. Do not replace NoMemoizeUnwind with a
  blanket ban on exceptions or handlers.
- The existing handled-outside/retry case has two body entries and zero writes,
  despite finite pure normal return. Keep its exact source observation and
  demonstrate failure of the additional no-unwind premise.
- Reentry and exceptional retry are different failure modes. Retain a raw
  active-address case showing why freshness is a separate premise.
- Two distinct fresh cells with identical body/capture contribute two distinct
  body identities. The aggregate observation and debit-interpreter connection
  must preserve that distinction and the repeated-address counterexample.

The same example may discharge several obligations. No theorem-count quota
applies. A direct concrete computation alone does not exercise a universal
theorem: connect the case through the public law with its assumptions proved.

## Statement review, integration and completion

Review quantifier order, actual prefix scope, address identity, stack membership,
value persistence, event-versus-body-work meaning and the no-unwind condition.
Check nonvacuity, normal returned retry, unfinished prefixes and absorbing
finished observations. Reuse continuation structure and ordinary additive/list
interfaces. Keep data, observations and laws separate and expose only necessary
assumptions. Record any genuine mathematical correction without weakening
independently justified example expectations to make compilation succeed.

Integrate core modules and connected clients through SquareApplications.
Application documentation describes stable APIs and their limits; implementation
evidence and local workflow remain in session. No new axiom, admission, unsafe
or native proof shortcut, proof-budget increase, linter suppression or relaxed
validation gate is allowed. Root owns compilers/Git/candidate capture. Keep
active input closures stable and at most one full check plus one focused wrapper.

Focused successes need exact input identity and retained failed rounds; they
are development evidence only. Freeze a clean isolated exact candidate, run
its own pinned-Nix stock full build and exhaustive audit, retain the matching
verification record, obtain both independent full-scope Standards/Spec outcomes
in one retained loop, and immediately verify the identical candidate before
acceptance. Preserve all code/history/tickets/evidence in uploaded recovery
checkpoints. Existing predecessor gates and chapter order remain unchanged.

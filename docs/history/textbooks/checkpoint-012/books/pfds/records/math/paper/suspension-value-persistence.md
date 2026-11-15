# Raw value-cell persistence

Assigned continuation of #10019 after green BodyEvent. Owner:
`chapter02_shared`; root owns commits, integration, acceptance and checkpoints.
No ValuePersistence files existed at checkpoint020. All existing frozen
sources, including the immutable #10014 candidate, remain unchanged.

## Claim and operation-level investigation

In the original raw machine, an occupied value cell stays a value cell during
bounded execution. The payload is existential and may change. No counterexample
to this statement was found: the only operation that can install a thunk is
delay allocation, which chooses the frontier; boundedness makes that frontier
different from every occupied address. `allocate_retains` provides the precise
old-cell fact. Assignment and memoization write value cells. `srec_value`
preserves values even when the address belongs to the closing target set.
Every other actual transition retains memory or only updates exception names.

`Core.Machine.HasValue memory address` is existence of a current `.value`
lookup. `OutcomeHasValue` follows the actual sum result to its memory.
`step_hasValue` assumes only bounded input memory and this lookup property.
`evaluates_hasValue` and `observe_hasValue` reuse `ConfigBounded`, including
its existing pending-frame condition, to keep subsequent inputs bounded.
Fresh `start`/`startPattern` corollaries require only initial memory boundedness
and the occupied value; their empty stacks discharge the frame premise.

The actual Prefix and Progress.Evaluates APIs are reused. `hasValue_no_body`
uses the unrestricted BodyEvent iff. `hasValue_hit` uses the existing raw
hit transition. `observe_no_body` and `observe_force_hit` compose those laws
with actual later live observations; the latter returns the then-current
payload. There is no new runner or event generator.

## Independently intended connected observations

- Allocate a value cell 7 at address 0. An actual assignment through variable
  5 changes it to 8 and returns unit after six transitions. The constructor
  persists through the finite run, while an explicit inequality excludes
  payload equality. Every unfinished observation uses the universal prefix
  law to retain both boundedness and a value, hence cannot emit `.body 0`.
- Bind that assignment before forcing the same address. Nine transitions
  finish assignment and its binding; six more enter the suspended pattern,
  so the 15-step live prefix is about to hit. `observe_force_hit` supplies the
  exact hit transition with payload 8, independently of the old payload 7.
- Reuse the original `Examples.SuspensionMachine.reentrant_overwrite` run,
  retaining final 8, two body entries, two cache writes and one hit. Its reached
  memory has a value at address 1. A new force from that actual memory has no
  later body-entry event at 1, using the established bounded-memory result and
  the new observation theorem. The two earlier writes remain part of the claim.
- A stored body raising a captured packet takes six transitions, skips its
  memoize frame and returns the same memory with a thunk. Repeating the match
  takes another identical six-step run and enters the body again. `HasValue`
  is explicitly false, so the persistence theorem is not applied circularly
  or extended to unsuccessful body evaluations.

These are new applications of the generic laws alongside preserved original
source executions. No expected value, address or resource count is inferred
from a desired green result.

## Statement review before first check

The claim concerns the cell constructor and exact physical address. Nested
values, arbitrary stored references and source exceptions are allowed. No
primitive law is needed: raw primitives do not take or return memory. The
finite-run result can be normal, exceptional, a match result or a fault.

The configuration-invariant premise is used for future boundedness, not as a
purity or no-reentry assumption. Repeated pending memoize frames are allowed
by that invariant, so later writes can overwrite an already stored payload.
The immediate hit/no-body facts require only the current value cell, without
boundedness, typing, global provenance or termination.

This proves no fixed payload, at-most-one cache write or global at-most-one
body entry from creation. Multiple body entries may precede the first value
write, and body exceptions can leave a thunk. Pure payload correctness remains
the separate StateRep/finite-correspondence responsibility.

## Validation status

Core and connected client drafts are written. First focused feedback is
pending; no acceptance claim or changes to limits/tooling/semantics.

## First focused feedback

`suspension-value-persistence-r1` ended exit 1 with all 23 input hashes
unchanged, 21:53:54.393002–21:54:12.264280 UTC on 2026-11-02. The remaining
goals came from splitting the outer outcome match before its inner transition
cases: the resulting transition equalities lived in hypotheses while the
first draft split only the goal. The correction adopts Invariant's existing
controlled substitution/simplification/hypothesis-splitting proof shape. No
statement, assumption, expected result/count or proof limit changes. Store
helpers and public execution/observation consequences produced no independent
errors; no core-green claim is made until the private obligations close. Exact
first-round log/command/hash evidence is retained in `session/validation`.

Root independently inspected the written statements and clients before this
check. The preparatory pass found the bounded-allocation premise necessary,
the existing pending-frame invariant appropriate for whole runs, and the
payload/duplicate-write/raised-body cases meaningful. It found no mathematical
mismatch in the inspected statements; it was not an acceptance review.

Second focused run `suspension-value-persistence-r2` closed all proof goals
but ended exit 1 on four unused fallback tactics after simplification had
already discharged their cases. The redundant `exact present` alternatives
were removed; no linter suppression or limit changes. All 23 hashes stayed
unchanged, 21:55:38.278229–21:55:54.901933 UTC. This is still not a reported
green module; the next check will establish the clean core/client result.
Exact r2 evidence is retained in `session/validation`.

## Final focused handoff

`suspension-value-persistence-r3` passed with exit 0 and 748 Lake jobs. The
core compiled in 4.8 seconds and all connected clients in 2.3 seconds. All 23
source/configuration hashes remained unchanged from queue through completion.
The run started 2026-11-02T21:56:55.469493+00:00 and finished
2026-11-02T21:57:08.768484+00:00, under pinned offline Nix, one Lean thread
and the shared focused-build lock. Exact r1–r3 logs and command/hash records
are retained in `session/validation/suspension-value-persistence-r*.{log,json}`.
The owned source whitespace check also passed.

Public API in `Suspensions.Core.Machine`:

- `HasValue`, `OutcomeHasValue`; store-operation consequences
  `HasValue.allocate`, `HasValue.memoize`, `HasValue.srec`.
- `step_hasValue`, `evaluates_hasValue`, `start_evaluates_hasValue`,
  `startPattern_evaluates_hasValue`.
- `observe_hasValue`, `observe_unfinished_hasValue`,
  `observe_finished_hasValue`, `start_observe_hasValue`.
- `hasValue_no_body`, `hasValue_hit`, `observe_no_body`, `observe_force_hit`.

All public statements and original expectations remained unchanged through
proof-engineering corrections. The checked applications are:

- `Mutation.assignment_overwrites`: actual six-step assignment, explicit
  initial 7/final 8, HasValue supplied by finite-run preservation, and proved
  inequality of the old/new lookups.
- `Mutation.assignment_prefixes`: every actual live prefix retains both the
  old bounded-config invariant and HasValue, then excludes body 0.
- `Mutation.later_force_hits_new_payload`: actual 15-step prefix to a force;
  the generic later-hit law yields precisely payload 8 and the body exclusion.
- `Reentrant.two_writes_remain`: retains the pre-existing actual effectful
  source execution, final 8, two body entries, two cache writes and one hit,
  then derives the new post-execution future no-body fact.
- `Exceptions.raised_body_can_repeat`: explicitly bounded thunk memory, two
  consecutive valid six-step raised-body runs with exactly the same memory,
  a current thunk lookup, a proof that HasValue is false, and an actual body
  event. The second run starts in the first run's reached memory.

This slice proves a constructor-persistence law of the original raw semantics.
It does not claim a fixed payload, a single cache write, or a single body
entry from allocation. The exception case and retained effectful overwrite
make those boundaries concrete. Pure payload correctness remains separate.
No existing source, execution semantics, configuration, dependency, proof
budget, linter setting or entrypoint was changed. Both owned source files
are frozen; no owned compiler remains. Parent owns commits, checkpoint
integration, complete-candidate gates and independent acceptance reviews.

Final source SHA-256:

- `Applications/Suspensions/ValuePersistence.lean`: `ce6998fd2e8d400dc69d9a5ff8f503ea28182403a721efc8a8251b60772b60f8`
- `Examples/SuspensionValuePersistence.lean`: `1072d09d7f1a3bc6d83a145685cbde3cad8730e0f9377028500dee1ea48090e1`

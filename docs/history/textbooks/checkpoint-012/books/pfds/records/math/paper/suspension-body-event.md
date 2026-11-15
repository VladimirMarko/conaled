# Exact raw body-event origins

Assigned continuation of the #10019 implementation loop. Owner:
`chapter02_shared`; root owns integration, commits and acceptance. Existing
DomainState, raw Machine, Recursive and Prefix sources stay unchanged.

## Intended statement and examples

`Core.Machine.body_event_iff parameters config address` characterizes the
existing transition event exactly. A `.body address` event is equivalent to
the existence of caller environment, suspended inner pattern, body and capture
such that the current control inspects exactly that address and its current
memory cell is exactly that thunk. There is no ConfigRep, heap-validity,
purity, typing, termination, nonreentrancy or source-well-formedness premise.
The converse reuses the existing public `body_transition` theorem. The forward
direction checks the actual transition cases. No new runner or event axiom
is introduced.

`body_event_address_unique` retains physical address identity: a transition
cannot have body events for two distinct addresses merely because the stored
code/capture are equal.

Connected intended observations, determined from the transition equations:

- Two actual delays place the same variable-9 code and capture `(9,7)` at
  addresses 0 and 1. The caller shadows variable 9 with 99. A suspended
  variable-3 match at address 1 emits precisely `.body 1`, enters the captured
  code/environment, and pushes the memoize frame. It does not emit `.body 0`.
- The same entry with an existing constructor frame retains that caller tail.
- The uncached match takes five transitions: entry, captured variable lookup,
  cache write, variable match, final matched delivery. It binds variable 3 to 7,
  stores value 7 at address 1, and leaves address 0 a thunk.
- Repeating the suspended match in that actual resulting state produces
  `.hit 1`; no body event or uncached-origin witness exists at any address.
- Address 4 is absent. Its suspended match produces the missing-address fault,
  preserves input memory and has no body event or origin witness.

These cases apply the general iff/uniqueness laws alongside the existing
transition and finite-evaluation APIs. The two equal thunks distinguish
physical identity from code equality; the cached case is linked to an actual
preceding write, not to a separately assumed cache state.

## Statement review

The iff quantifies the actual emitted address, not merely some address with
matching code. The lookup is in the current configuration memory, so the
claim remains valid during repeated/reentrant writes and under arbitrary
caller stacks. Body/capture witnesses are not assumed to terminate. Diagnostic
faults and cached hits are excluded by their distinct event constructors,
without relying on type safety or purity. The claim is only about the current
transition, not how many future body events occur.

## Read-only live-prefix helper finding

`Applications/Suspensions/Recursive.lean` already contains a private theorem
`Core.Recursive.observe_after_prefix` with the exact generic statement:

```lean
{parameters : Parameters Primitive} {config next : Config Primitive}
{budget : Nat}
(first : Prefix.observe parameters budget config = .inr next) (extra : Nat) :
Prefix.observe parameters (budget + extra) config = Prefix.observe parameters extra next
```

Its proof unfolds the existing observer and uses `Function.iterate_add_apply`
after commuting the two count summands. `Prefix.lean` exposes `observe_zero`,
`observe_succ` and `stays_finished`, but no public general live-prefix
composition theorem. This is a reusable existing proof for a later owner to
expose or relocate. `Core.Observation.workload_append` is a public composition
law at the resource layer, and `observe_erases` connects its first projection
to `Prefix.observe`; those laws can also derive the result but require the
resource observer dependency. Neither Recursive nor Prefix was edited in this
slice.

## Validation status

The first focused check established a green BodyEvent core (53 s), with all
public statements unchanged. The batch ended exit 1 solely because the cached
client tried to rewrite an expanded transition equation through a private
configuration abbreviation; projection/equality composition replaces that
rewrite. No event, count or memory expectation changes. All 19 source/config
hashes were unchanged, 21:29:49–21:32:38 UTC on 2026-11-02. Exact r1 evidence
is saved in `session/validation/suspension-body-event-r1.{log,json}`. The core
is frozen for downstream imports; the corrected client needs its final check.
This is not a full #10019 or source-coverage acceptance claim.

## Preparatory peer statement pass

The ordered worker independently read the new statements and cases. It
confirmed the exact inspected address/current thunk in the unrestricted iff,
the absence of a validity/domain premise, distinct addresses for identical
cells, and captured 7 versus caller-shadowed 99. It verified all five uncached
transitions and the separate cached-hit/missing-address transitions. The
nonempty caller-tail case claims only the entry transition, not a well-typed
whole continuation. The peer made no edits or acceptance claim.

The thunk condition denotes the current `.thunk` cell constructor. It does
not imply that the body has never been entered: active reentry and bodies
that previously raised are deliberately still covered. The statement asserts
no monotonic cache property or global limit on entry count.

## Final focused handoff

`suspension-body-event-r2` passed with exit 0 and 744 Lake jobs. All 19
source/configuration hashes stayed unchanged. It ran from
2026-11-02T21:35:59.146015+00:00 to 2026-11-02T21:38:12.597305+00:00
under the pinned offline Nix shell, one Lean thread and the shared focused
lock. The client compiled in 117 seconds; the r1 green core was unchanged.
Exact log/command/hash records for both attempts are saved in
`session/validation/suspension-body-event-r*.{log,json}`.

The final public API is `Core.Machine.body_event_iff` and
`Core.Machine.body_event_address_unique`. All statements and expected counts,
values, cell identities and event constructors were retained throughout. The
only correction was an example proof's abbreviation-sensitive rewrite. No
existing source, configuration, entrypoint, proof limit or semantics changed.
The owned source whitespace check passed. Both source files are frozen, with
no owned compiler remaining. Parent retains full-gate, review, checkpoint and
#10019 integration responsibility; this is focused evidence only.

Final source SHA-256:

- `Applications/Suspensions/BodyEvent.lean`: `41cf64feb32b28b1b3e03bcba475f7fd5811f33307aa253328e2527d2fbed0d2`
- `Examples/SuspensionBodyEvent.lean`: `fcb8561a8b1d845cd6f0483f68bbec35e63710f40a136035dc5b7273ffc361a8`

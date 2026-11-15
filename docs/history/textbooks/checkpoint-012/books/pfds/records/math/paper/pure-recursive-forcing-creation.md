# Local 10019: actual recursive creation and closing

Assigned slice of the parent-owned implementation loop. Worktree
`purity-foundation`, branch `pfds/pure-suspensions`; starting HEAD
`6f2290f2ab916468d499e5de388ed7be7408dc96`. Requirements are
`session/requirements/pure-recursive-forcing.md` version 1 and the agreed
finite-world/provenance interface. No GitHub writes, entrypoint changes,
commits or acceptance claims belong to this slice.

## Intended connection and cases

`Recursive.create` already proves finite creation, bounded memory, retention
of old occupied cells, and the unforced-target premise for SRec. The missing
connection is a finite semantic-world extension for the exact created group,
including its closed raw captures. This is a missing representation bridge,
not a claim that a compiler failure demonstrates a mathematical gap.

The retained mutual example has `f () = force s` and `s = $(f ())`, with an
older occupied cell captured through an unrelated outer name. Expected facts:
the new delay is allocated at address 1, its final capture contains both
recursive members and the outer binding, address 0 retains integer 41, and
the actual machine reaches the closed body state in eight transitions. No
cyclic body is forced and no termination claim is made.

The duplicate-name example first allocates a delay and then shadows its
identifier with a function. Its SRec target set is empty, and the delay still
contains the original empty capture after closing. It therefore cannot meet
the proposed pending certificate for its full-group meaning. This justifies
the explicit distinct-source-name premise rather than silently treating all
list members as effective bindings.

## Interface and statement review

`PendingGroup` has exactly five fields: immutable world extension, world
frontier, `GroupRep` for the actual template, freshness of SRec targets, and
an origin/cell/target account of every new meaning. It does not claim closed
cell validity during creation. Existing-world entries remain identical;
new entries have the complete finite group descriptor but still point to
preclose thunks with the original raw capture.

`create_pending` consumes an actual `Recursive.create` receipt, bounded raw
memory, the old world frontier, the represented outer capture, and distinct
source names. No full state representation, purity, acyclicity, nonreentrancy
or body-evaluation premise is required. It reuses the original raw allocator
and `Durability.put`/`Extends`; there is no second public template datatype.
The private fold invariant uses the existing `GroupMembersRep` cursor and
retains fresh-address and exact-thunk evidence for processed bindings.

`PendingGroup.closed_new` relates the updated raw capture to
`Meaning.environment`, including the group members. `closed_old` combines
the established creation retention with the fresh-target footprint to retain
old occupied cells through SRec. `closed_environment` represents the actual
body environment and its overriding order. The mutual example consumes all
these public claims and the existing counted machine prefix.

Structural representation is deliberately independent of code purity and
cache validity. World meanings need not be injective, and raw-value
representation need not be functional. State representation, primitive
compatibility, finite-run adequacy, strict occurrence descent and no-reentry
remain parent/other-slice obligations.

## Validation state

The first focused check ran after the parent reported Representation core
green. It ended exit 1 on 2026-11-02 at 20:37:51 UTC, with all queued/start/end
source hashes unchanged. The library had two local proof-elaboration errors:
equality elimination had renamed two lookup-proof binders, and the final
GroupRep alias needed an explicit change of the goal. All other library
declarations elaborated in that pass; the connected client had not yet run.
Both corrections preserve statements and expected cases. Evidence is saved
as session/validation/suspension-pure-creation-r1.{log,json}. All focused
builds use the pinned offline Nix route, one Lean thread, the shared focused
lock, and frozen dependency/source hashes.
Parent-owned complete-candidate build/audit and independent reviews remain
required regardless of this slice's focused outcome.

The second focused check ended exit 1 at 20:39:19 UTC with unchanged
queued/start/end hashes. Pure.Creation compiled successfully (32 seconds),
including the actual receipt bridge and all closing laws. The client reported
only a type-inference error in its initial allocate_bounded invocation; the
explicit raw Memory Empty type was added without changing the proposition.
The other connected client proofs reported no errors in that pass. Core is
frozen for parent-owned Memory integration; final client check is pending.
Evidence: session/validation/suspension-pure-creation-r2.{log,json}.

The third focused target passed: 750 jobs, exit 0, from
20:41:31.523718 to 20:41:43.690130 UTC on 2026-11-02. The client compiled in
4.4 seconds. Queued/start/end hashes matched for the full local import closure
and configuration. Both owned sources are unchanged after this pass. Evidence
is saved as session/validation/suspension-pure-creation-r3.{log,json}.

A preparatory read-only statement pass by the ordered worker found no semantic
mismatch in the five-field pending invariant, actual-receipt construction or
closing laws. It specifically checked the use of distinctness to turn raw list
membership into effective lookup, and the duplicate-name counterexample. This
was not an independent acceptance review; complete-candidate gates and both
review axes remain parent-owned.

Checked source hashes at this handoff:

| File | SHA-256 |
|---|---|
| Applications/Suspensions/Pure/Creation.lean | `cd890effa3e586e12e502595d3f8159a3cbfc803f0da580d69bcb1ee570c1f8e` |
| Examples/SuspensionPureCreation.lean | `cfad4b13f93378fa6f29ff845570f6cbbfeab585af5b375f07b66a0e5cc86b33` |

The parent has assigned a following composition with Pure.Memory once that
module is green: derive closed StateRep from initial StateRep plus this
certificate/receipt, then package actual creation, extension and represented
closed state/environment. That extension is not yet implemented or checked.
The present pass establishes only the structural creation/closing slice.

## Composition with represented memory

After checkpoint018 released its write hold, the parent reported the
Pure.Memory core and clients green at commit
`86b394f5537cd9a61ac9b9708b5fef8face6d047`. The assigned follow-on adds
`PendingGroup.closed_state` and `create_closed` in the existing module, with
an acyclic import of Memory and no change to the five-field certificate or
previous theorem statements.

`closed_state` consumes the original StateRep, represented capture and actual
creation receipt. It derives preclose/closed boundedness from the original
creation laws. Old entries retain their actual raw cells and transport their
CellRep witnesses through World extension. New entries use their fresh target
bounds to exclude old World meanings, then consume `closed_new` and its
expanded capture. No successful evaluation is required of those new bodies.

`create_closed` additionally uses actual `create_exists` to return the reached
memory/environment and receipt, World extension, final StateRep and represented
body environment. The new connected client identifies that existential receipt
with the independently specified mutual-group receipt, retains the eight-step
machine prefix, and establishes the old cached cell's actual two-transition
pure evaluation. The cyclic new cell remains unforced. Existing raw-footprint
and duplicate-name expectations are unchanged. This extension is drafted and
awaits its focused check; it is not yet covered by the earlier r3 evidence.

The composition and its connected client passed together on their first
focused check: suspension-pure-creation-r4, 752 jobs, exit 0, from
20:50:20.318025 to 20:50:35.424275 UTC on 2026-11-02. Creation compiled in
4.5 seconds and the client in 2.6 seconds. The import closure was recomputed
to include Memory and Pure.Machine; all queued/start/end source and config
hashes matched. No source changed after this pass. Both the original
structural cases and the stronger actual-creation StateRep case passed.
Evidence: session/validation/suspension-pure-creation-r4.{log,json}.

The ordered worker also completed a preparatory read-only check of the two
new statements and client. Old CellRep.cached evidence is preserved through
CellRep.mono without rerunning its body; new entries use CellRep.thunk with
represented captures and no finite-body premise. The full StateRep describes
represented addresses, allowing unrelated occupied cells, as Memory specifies.
No semantic mismatch was reported. This remains preparatory feedback, not
an acceptance review or completion of 10019.

Final checked owned source hashes:

| File | SHA-256 |
|---|---|
| Applications/Suspensions/Pure/Creation.lean | `f46d236bc93220d6e4cfd3c150dd293a496b509074b961ba1ca9ec774ca5f193` |
| Examples/SuspensionPureCreation.lean | `b9f7b216579e15b3e757692a224f1215339b837ae8b076e969ce198b34d458f1` |

There is no remaining owned compiler, no placeholder/admission, no proof
limit or linter change, and no post-check source delta. Root owns commits,
entrypoint integration, durable capture and complete-candidate build/audit
and independent review. Pure finite-run adequacy and the source no-reentry
claim remain open; these creation/closing laws do not settle them.

## Caller stacks and creation events

The parent assigned a further narrow extension of raw Recursive in the
purity-foundation worktree. The frozen 10014 candidate and its checkout are
untouched. Existing public statements and examples remain; the original
empty-stack entry theorem specializes the new stack-parametric prefix law.

The agreed APIs are `enter_body_prefix_with_stack`,
`evaluates_from_body_with_stack`, and `evaluates_iff_with_stack`. They preserve
the original caller stack through the exact `3 * length + 2` creation prefix,
then retain the same reached answer and add exactly that prefix to the finite
body-and-caller count. The existing private `evaluates_strip_prefix` is exposed
publicly with its statement and proof unchanged. No new runner or evaluation
relation is introduced.

`enter_body_prefix_no_body` quantifies over actual live `Prefix.observe`
states at indices strictly below `3 * length + 2` and excludes every `.body`
event at those transitions. Its private proof inspects the three transitions
for each permitted function/delay RHS; the outer entry and final SRec steps
also have core events. The strict boundary leaves subsequent body execution
unconstrained. This is the local fact needed to skip creation as a macro
without hiding a force occurrence.

The connected client retains a constructor-77 caller frame: creation takes
eight steps, the variable body and constructor return take three, and the
whole run takes eleven. The inverse law recovers the same three-step residual.
A separate client applies the universal no-body-event law to all eight prefix
positions. These additions are drafted and await a focused check; the earlier
r4 evidence applies to the pre-extension source state only.

The caller-stack/event extension passed its first focused check, including
the unchanged earlier Examples.SuspensionRecursive client: 785 jobs, exit 0,
from 20:57:54.476300 to 20:58:38.294571 UTC on 2026-11-02. Raw Recursive
compiled in 3.9 seconds, the expanded PureCreation client in 3.4 seconds,
and the retained Recursive client in 2.7 seconds. Queued/start/end hashes
matched for the full two-target local import closure and configuration.
Evidence is saved as session/validation/suspension-raw-recursive-stack-r1.
{log,json}. Raw Recursive and the expanded client are now frozen, with no
post-check source changes. Pure/Creation itself has exactly the r4-green hash.

Statement review: all prior public propositions retain their parameter and
result types. The now-public evaluates_strip_prefix has the identical old
statement and proof. The new finite iff keeps the reached Answer, including
its memory, and the exact additive count under an arbitrary caller tail; it
adds no validity or return-mode premise. The no-body law refers to actual
observed intermediate configurations and every possible body address. Its
strict index bound excludes the residual body state. Permitted RHS shapes
suffice: no distinctness, typing, purity or body-termination condition is
needed for this event fact. Positive prefix/run clients establish that the
observation premises are usable, while the original creation/state cases
and duplicate-name rejection remain unchanged.

Final source identities after the raw extension:

| File | SHA-256 |
|---|---|
| Applications/Suspensions/Recursive.lean | `cbf1dfda736afb9f8e4e9bc4b023030edcb6713de9902a8828cdc1489f0d0934` |
| Applications/Suspensions/Pure/Creation.lean | `f46d236bc93220d6e4cfd3c150dd293a496b509074b961ba1ca9ec774ca5f193` |
| Examples/SuspensionPureCreation.lean | `c2dceb5d457101b7fb537e784d5bd2a1499cf7e814ff59c8147d115e26755a4f` |

Only the purity-foundation copy of raw Recursive was edited; the frozen
10014 candidate was not changed. No new runner, evaluation relation, proof
budget, linter exception or admission was introduced. The focused lock was
released and the Domain owner was notified that raw Recursive is stable.
There is no remaining compiler owned by this slice. Parent-owned candidate
integration, exhaustive audit and acceptance review remain outstanding.

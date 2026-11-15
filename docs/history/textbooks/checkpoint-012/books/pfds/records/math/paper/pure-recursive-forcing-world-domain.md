# Local 10019: admissible immutable worlds and cached witnesses

This is the parent-approved WorldDomain slice in the existing implementation
loop, fixed review base `b422800fb5b6dc1253823057c0ea71644274d77c`. Owned files
are `Applications/Suspensions/Pure/WorldDomain.lean`,
`Examples/SuspensionPureWorldDomain.lean`, and this report. Existing
Representation/Memory/Creation/Domain source remains unchanged; parent owns
commits, entrypoints, tracker, full validation, reviews and checkpoints.

## Approved boundary and public API

`WorldAllowed operations world` requires `Domain.ValueAllowed` of the value
of every meaning present in that immutable world. It does not state raw cell
validity, a world frontier, freshness, finite evaluation or no-reentry.
`meaning_code` projects the allowed body and `meaning_environment` derives
admissibility of its effective capture through `bodyEnvironment_allowed`.

`WorldAllowed.put` preserves this code-domain property from the old property
and the new meaning's admissibility. It does not need freshness and does not
conclude `Durability.Extends`. `WorldAllowed.delay` composes this fact with
the existing actual `Memory.StateRep.delay` theorem, which separately derives
freshness, extension, the represented allocated address and raw state validity.

`pending_allowed` uses an actual `Creation.PendingGroup` certificate, the old
world property, and an allowed group. Its old-entry branch uses the previous
world. For each new target it obtains an effective raw lookup through
`mem_addressRange`, transports that lookup through `pending.members.unroll`
and `EnvRep.lookup`, uses `GroupAllowed.members` and `EnvAllowed.lookup`, and
identifies the resulting pure value with the immutable meaning at that raw
address. There is no new template induction or body-termination premise.

The additional parent-requested `create_closed_allowed` wrapper composes
`Core.Recursive.create_exists`, `Creation.create_pending`, closing's state
and environment theorems, and `pending_allowed`. Its premises are initial
StateRep/WorldAllowed, the represented outer capture, and an allowed group;
distinct binder names are obtained from that group. Its result retains the
actual creation receipt and PendingGroup certificate (including extension),
alongside the closed StateRep, WorldAllowed and represented body environment.
The generic bridge therefore need not recover a dropped pending witness or
assume successful creation separately.

`cached_result_allowed` unpacks the finite pure evaluation already required
by `Memory.CellRep.cached`. From the allowed meaning and primitive output
preservation, `DomainState.start_allowed` and `evaluates_preserves` derive
admissibility of its result. The conclusion retains that exact pure view,
transition count, representation proof and evaluation witness.
`cached_lookup_allowed` applies this to an actual cached-cell lookup using
`StateRep.lookup` and the world's meaning property. Neither theorem infers
that an arbitrary unforced body terminates.

## Connected clients

- Actual delay of integer 41: the raw transition returns address 0, frontier
  becomes 1, and the raw cell contains the unforced source body. The composed
  delay theorem supplies state and world-domain validity.
- Actual cache-write frame for that value: the reached cell is justified by
  the literal body's two-transition pure evaluation. The cache lookup lemma
  supplies the admissible result with its witness intact, and deterministic
  evaluation uniqueness checks integer 41 and count 2.
- The existing mutually dependent function/suspension descriptor is created
  through the combined wrapper and its actual raw receipt. The pending
  theorem supplies an allowed world; closing supplies `StateRep` and the
  represented environment; the expected eight-transition prefix
  stops just before forcing the new suspension. Code and effective capture
  admissibility are projected from its world entry without evaluating its
  cyclic body.
- Overwriting an existing meaning with another allowed literal preserves
  WorldAllowed but fails immutable extension. This checks that the put theorem
  has not silently absorbed the separate freshness requirement.

## Current validation status

Checkpoint 019, commit `41895aa`, preserved the uncompiled initial draft;
the just-requested combined creation wrapper had not yet been written at that
capture. The wrapper and its mutual client connection were added after the
capture hold was released. No source from Creation was changed.

After the shared worker signaled DomainState core-green and froze its inputs,
WorldDomain revision 1 passed its core and every connected client on the first
focused attempt: 2026-11-02 21:21:22.983660–21:22:12.026071 UTC, exit 0,
760 jobs. Core compilation took 34 seconds and the example 4.1 seconds.
All 30 local source modules and 5 configuration inputs were unchanged at queue,
lock acquisition and completion. Evidence is
`active-validation/suspension-pure-world-domain-r1.{json,log}`. The wrapper used
the pinned offline Nix environment, `LEAN_NUM_THREADS=1`, shared focused-build
lock and this worktree's private project outputs. No Forcing module is imported.

| Checked source | SHA-256 |
| --- | --- |
| `Applications/Suspensions/Pure/WorldDomain.lean` | `d4c811882707c942e1d69fb6af71e81253695b4fdb98d045b156991e2e7159b9` |
| `Examples/SuspensionPureWorldDomain.lean` | `5de16e1b462b842e5ec92338ddd9e155a7583110f886245323fa4f631468240c` |
| Imported `Pure/DomainState.lean` | `5e6d5294dd41029867b5f6590a98a08dce5a9801572cf81c46c19c9e160bb058` |
| Imported `Pure/Creation.lean` | `f46d236bc93220d6e4cfd3c150dd293a496b509074b961ba1ca9ec774ca5f193` |

Git HEAD was `41895aaff989c81cfe1ed23243e773be308d8711`; the exact frozen file
hashes identify the additions after that recovery commit. `git diff --check`
for the two owned source files passed. Source inspection found no admissions,
new axioms, linter suppression or raised proof budgets. Whole-candidate
validation, exhaustive proof audit and independent reviews remain parent-owned.

## Statement review and checked connections

WorldAllowed ranges over semantic-world entries, not arbitrary raw occupied
cells. Its meaning premise checks stored code and captures through the finite
Domain predicates. The effective body environment is obtained through the
existing member/body-environment preservation theorem. No unrolled cyclic
predicate or body-evaluation condition was added.

The creation theorem keeps the intermediate PendingGroup certificate distinct
from the closed StateRep. New meanings may have admissible code while the raw
thunks still have their preclose captures; raw-state validity is concluded only
after SRec. The combined wrapper retains the actual receipt and witness needed
by the later recursive machine bridge.

The cached-result premise is an already justified cached cell. Its finite pure
evaluation is unpacked, not postulated anew or inferred for a cold thunk. The
conclusion carries the same pure result and transition count, and the extra
domain fact is derived through actual pure evaluation preservation. This is
not an equality between pure and raw execution costs.

| Public result | Checked connection |
| --- | --- |
| `WorldAllowed.empty/put` | Literal delay uses put through the actual allocation composition. The overwrite client proves both worlds allowed while directly refuting Extends. |
| `meaning_code`, `meaning_environment` | The actual mutual-group world lookup supplies both conclusions, including the effective environment with recursive members. |
| `pending_allowed` | The new address's allowed value comes from represented effective group lookup. The old-entry branch consumes the initial world property. No template induction is duplicated. |
| `create_closed_allowed` | `Mutual.actual_recursive_world_allowed` consumes the wrapper, identifies its existential receipt with the independently computed source creation result, retains the represented closed environment and checks the actual eight-transition prefix. |
| `WorldAllowed.delay` | `Literal.actual_delay_allowed` combines its state/world conclusions with the actual raw delay transition, expected address 0, frontier 1 and stored source-body lookup. |
| `cached_result_allowed`, `cached_lookup_allowed` | `Literal.actual_cache_allowed` retains the actual cache-write transition and state, consumes the public lookup corollary, then checks integer 41 and the body count 2 through evaluation uniqueness. |

The checked cases require no termination premise for the newly created cyclic
thunk. The literal cache case explicitly supplies its actual finite pure body
witness. No expected value, count, statement or premise was changed in response
to compiler feedback; this slice passed its first focused check. Source and API
are now frozen for parent integration.

## Remaining integration obligations

The execution simulation, cache-history derivation, proper nested-body
occurrence certificates, actual no-reentry and resource theorems remain
separate obligations. This slice does not establish ticket or chapter
acceptance.

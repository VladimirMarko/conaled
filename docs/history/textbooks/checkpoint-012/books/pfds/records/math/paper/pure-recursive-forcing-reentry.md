# Local 10019: pure obstruction at a represented active force

This is the bounded parent-assigned Reentry slice in the current implementation
loop, fixed review base `b422800fb5b6dc1253823057c0ea71644274d77c`. Owned files
are `Applications/Suspensions/Pure/Reentry.lean`,
`Examples/SuspensionPureReentry.lean`, and this report. All imported
Simulation/History/Recurrence interfaces are already green and remain
unchanged. Root owns Execution/RecursiveStep, integration, commits, tracker,
complete validation, audit and independent reviews.

## Checked public statement

`Suspensions.Pure.Simulation.ConfigRep.active_force_pure_not_terminates`
takes a represented raw/pure configuration pair, an equality identifying the
raw current control as a suspended pattern on an address, and an indexed raw
stack lookup identifying a pending memoize frame for the same address. It
concludes that the current pure configuration has no finite result.

The index identifies an occurrence rather than assuming address uniqueness.
The current caller environment/inner pattern need not equal those saved by
the old memoize occurrence. Their common immutable address meaning identifies
the body and its effective capture. There is no code-domain, primitive law,
raw finite-execution, nonreentry or distinct-active-address premise.

## Proof connection

Inverting the existing ControlRep/ValueRep yields the exact pure forcing
control and the immutable meaning at the address. The existing
`History.ActiveHistories.reentry_not_terminates` uses the occurrence's actual
past pure prefix to exclude every finite evaluation of that body.

The next actual pure force step enters
`appendFrames (start meaning.environment meaning.body)
  (.force caller inner :: pureStack)`.
`Machine.not_terminates_append` excludes completion under the caller frames,
and `Recurrence.Reaches.not_terminates` transports that obstruction back across
the one-step entry. The proof does not assume that the raw machine has no
finite execution, and does not derive raw nontermination here.

## Connected case

The client reuses `Examples.SuspensionPureSimulation.before_related`, including
the cyclic cell's represented capture and the actual fourteen-transition body
history. The old memoize occurrence is at index 3, behind ordinary caller
frames. Both original next-step equations are retained: the raw machine enters
body address 0, and the pure machine enters the corresponding finite meaning.

`active_cycle_no_finite_pure_result` consumes the new public theorem.
`obstruction_at_actual_reentry` keeps the representation, indexed occurrence,
both actual entry transitions and the pure obstruction in one conclusion.
`cycle_has_no_finite_pure_answer` specializes the result to every answer class
and finite count, including exception, matching, mismatch and fault outcomes.
These are not bounded-search failures or a raw nontermination claim.

## Statement review within the current implementation loop

- The theorem starts at the current force control and excludes completion of
  that whole pure configuration. It does not stop at the isolated body.
- The same immutable meaning is obtained by actual world lookup after
  inverting the control/value representation; it is not an independently
  chosen body with the same printed code.
- The pending frame premise uses a concrete list occurrence and its address.
  It contains no active-address uniqueness or hidden no-reentry requirement.
- The cyclic client discharges all representation/history premises using an
  unforced thunk and the actual fourteen-transition prefix. Its memory proof
  does not assume body termination or the conclusion being proved.
- `Progress.Terminates` ranges over all result constructors and finite counts;
  no type-safety premise is used to discard faults.
- Raw nontermination and the absence of active reentry in finite raw runs
  remain obligations for composition with the separate finite-correspondence
  theorem. No such result is asserted by this module.

## Focused validation evidence

The first check passed with no source corrections:

- Target: `Examples.SuspensionPureReentry`.
- Pinned offline Nix development environment, `LEAN_NUM_THREADS=1`, default
  Lean proof limits; serialized with `active-validation/focused-build.lock`.
- Started: `2026-11-02T21:28:45.673493+00:00`.
- Ended: `2026-11-02T21:29:49.144826+00:00`.
- Exit code 0; 758 jobs; the new library compiled in 23 seconds and its client
  in 30 seconds.
- All 33 local source/configuration hashes were identical before queueing,
  after acquiring the lock, and after the terminal result.
- Log: `active-validation/suspension-pure-reentry-r1.log`.
- Machine-readable command, timestamps and full input hashes:
  `active-validation/suspension-pure-reentry-r1.json`.
- Recovery HEAD at the check: `41895aaff989c81cfe1ed23243e773be308d8711`;
  these new files are not claimed to have been committed by this worker.

Checked SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `Applications/Suspensions/Pure/Reentry.lean` | `335ebd1d615341b149b38f40111a33bb9423a1074ed0fbe5efaff1bd2e7c7d85` |
| `Examples/SuspensionPureReentry.lean` | `e79e3c6b4bf8d6dfcb5afa8464d94dde438ebd295ff097a1b95cd0df525ed405` |

Both owned Lean files are now frozen. Neither Execution nor RecursiveStep is
in this target's import closure, and no shared dependency was edited.
This is focused compilation and statement inspection in the existing loop;
root still owns integration, complete validation, audit and independent review.
No complete-ticket or chapter acceptance is claimed.

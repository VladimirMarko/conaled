# Between-tick Boolean backend migration (#464)

This first delivery changes a running Boolean delay between its one-bit Circuit
realization and a two-bit realization retaining `(b,!b)`. It preserves the current
continuation after a nonempty prefix. It does not initialize a replacement
session or replay inputs. Explicit requests select the target; no tuner, native
emitter or shared migration interface is required.

The required [pending-work successor #480](https://github.com/VladimirMarko/conaled/issues/480)
is implemented in the [bounded peer experiment](pending-peer-migration.md).
This quiescent delivery drains accepted work before transfer; it does not
establish migration of queues, acknowledgment state, asynchronous callbacks or
crash recovery. #464 remains the staged capability owner.

## Mathematical contracts and reuse

[MigrationPair](../../Applications/FRP/MigrationPair.lean) extracts the existing
redundant Circuit from `Examples.IndefiniteService` without changing that example's
public definitions or compiler correspondence. Both Boolean states are reachable;
reachable pairs are exactly the complement pairs. `forward` builds the complement
pair, and `reverse` projects only after validation. Invalid raw pairs `(false,false)`
and `(true,true)` are rejected. These total Lean functions terminate.

`finite_suffix` reuses `Feedback.run_related` for arbitrary related current states
and every finite input suffix, preserving both output order and retained state.
`infinite_suffix` rebases the two initialized records to those current states and
applies `Feedback.transport`. Rebasing a proof record runs no initialization.
`prefix_migration` uses `run_append` to connect the processed prefix to its
continuation. The reset counterexample preserves the old published value `false`
but changes the output on the next input `false` from `true` to `false`.

[Migration](../../Applications/FRP/Migration.lean) has a concrete tagged backend.
A redundant state retains two Boolean fields and an erased complement proof.
A tick result retains the actual Circuit output and candidate continuation,
with proofs of the delay observation, next logical state and representation.
`step_balance` accounts for each accepted input and publication while retaining
an explicit unpublished obligation. `execute_balance` proves this over arbitrary
finite command schedules, including repeated transfers, queries and refusals.
`completed_schedule` identifies the entire output list and retained logical state
with the ordinary delay execution when no publication obligation remains.
Executable sessions store none of these proof histories.

A shared conversion record would still require this pair's conversions, invariant,
resource admission, publication and ownership protocol. Here it would additionally
package dependent state types without simplifying the caller. The direct protocol
therefore exposes two targets and ordinary commands; shared finite and stream
simulation laws remain the reuse point. No new generic conversion architecture is
adopted.

## Ownership and publication

The public runner is [migration-service.lean](../../scripts/migration-service.lean).
Run it through `direnv exec . lake env lean --run scripts/migration-service.lean`,
optionally with `redundant` as its initial realization. Each byte is one command;
newline is ignored. The adapter never accumulates a line or lifetime transcript.

| Command | Effect |
| --- | --- |
| `0`, `1` | Accept one input only while idle and no migration request/preparation exists. |
| `e` | Evaluate the accepted input once, retaining output and candidate state. |
| `w`, `p` | Refuse or accept the pending output. Acceptance publishes once; a repeated `p` is rejected. |
| `t` | Commit a published tick's candidate continuation. |
| `d`, `r` | Request delay/redundant. Conflicting and same-backend requests reject explicitly. |
| `m` | Prepare with the adapter's logical transfer budget of 128 slots. |
| `b`, `f`, `v` | Exercise insufficient budget, modeled allocation refusal or modeled validation refusal. |
| `o` | Commit prepared ownership, releasing old/preparation storage. |
| `c` | Cancel migration and release preparation, preserving any accepted tick. |
| `q` | Query backend, committed state, phase, last publication, request and preparation. |
| `u`, `j` | Evaluate only if the active owner is delay/redundant respectively. |
| `z` | Reject an unsupported target. |

Business outputs use `B:0` or `B:1` lines; control responses use `C:` lines.
Queries add no business output and cannot combine two accepted identical inputs.
A pending output can wait while queries and cancellation remain responsive.
Migration preparation waits through accepted, pending and published phases until
tick commit. `Safe` and `execute_safe` in
[MigrationSafety](../../Applications/FRP/MigrationSafety.lean) ensure that prepared
storage occurs only at the idle boundary for its latched target.

Before ownership commit only the old backend evaluates ticks. Preparation retains
its authority; cancellation and modeled failures clear target storage and leave
its continuation usable. After commit evaluation selects only the active target.
`wrong_owner_preserves` checks synchronous commands naming the other backend.
There are no retained asynchronous owner handles, generation counters or callback
exclusion claims. A mathematical copy of old state is not itself protocol authority.

The [IO adapter](../../Applications/FRP/MigrationIO.lean) writes and flushes each
business output before installing the successful published transition. Tick
commit is a subsequent command, as is migration commit. This follows the existing
`IndefiniteIO` local write/flush acceptance convention. A write or flush exception
terminates without replay: its external effect may be ambiguous. Successful local
flush is not remote acknowledgment, durable delivery or crash recovery. Explicit
sink refusal is a deterministic control action; it does not interrupt an
arbitrarily blocked OS write. Allocation refusal is injected after modeled budget
reservation, not recovery from arbitrary Lean host allocation exceptions.

## Storage, work and progress

[MigrationResources](../../Applications/FRP/MigrationResources.lean) counts logical
slots by phase. It includes active state, a reserved last-publication cell,
accepted input, pending/published candidate and output, and prepared target.
The fixed 80-slot allowance comprises eight control slots, one input-byte buffer,
a 32-slot control response buffer, four business-output slots, 32 query workspace
slots and three spare slots. Response lengths are checked by `status_frame_bound`
and `query_frame_bound`. These are logical buffer reservations; Lean string
allocation, headers, garbage collection and OS buffers are not represented as
literal Boolean cells.

Even an arbitrary manually constructed session fits `state_slots_bound` (89 slots).
Reachable prepared sessions have no tick candidate. Preparation additionally
counts a two-cell conversion temporary and retains both old and new backend;
`admitted_preparation_fits` proves the resulting storage plus temporary fits the
supplied budget. The uniform preparation allowance is 87 slots, below the
adapter's 128-slot transfer budget. That budget is specifically for transfer,
not a physical memory limit for the whole process.

The actual Circuit counts remain delay work/arena `3/13` and redundant `9/46`.
`peak_slots_bound` conservatively adds the selected evaluation arena and conversion
temporary to protocol storage, giving 137 logical slots. `commandWork` separately
charges fixed protocol dispatch/observation, validation, reserve/release, conversion
(complement construction or projection), and commit. These declared operation
units are not clock cycles or an allocator trace; no ranking cost is present
because the caller explicitly selects a target.

`drain_idle` supplies the finite evaluation/publication/tick-commit schedule.
`drain_then_migrate` connects retirement to successful preparation and ownership
commit. They require those operations, including sink acceptance, to be scheduled.
`refusal_wait` permits every finite number of sink refusals without changing the
session. An indefinitely blocked sink has no migration deadline; cancellation
still preserves accepted work.

`scheduleWork` accumulates each `commandWork` along the actual changing session.
`selected_schedule_work` proves the exact cost of retirement followed by preparation
and ownership commit. Retirement costs zero when idle, `1 + tickWork + 2` when
accepted, two when pending, and one when published. The accepted case includes
evaluation dispatch. Preparation and ownership commit add `5 + conversionWork`.
`pause_schedule` connects this phase-dependent schedule cost to `pause`, with
explicit admission, scheduler and sink waits. `pause_bound` gives those wait
bounds plus at most 19 operation units. A reachable redundant accepted tick
migrating to delay costs 18 units before waits, not 17. The modeled interval
starts after the request command is admitted; request handling costs one separate
command unit. The measured request-to-quiescence interval also includes that
request's round trip, so it has a different start boundary. No bound is claimed
for an arbitrary unfair scheduler.

## Validation boundary

[Checked clients](../../Examples/BetweenTicksMigration.lean) cover both directions
after nonempty prefixes, arbitrary schedule accounting, two transfers between
ticks, queries, duplicate publication, cancellation, invalid pairs, failed
preparation, old-owner rejection and logical resource bounds. Independent reference
expectations and subprocess tests preceded the protocol adapter; the saved red
run failed because the runner was absent, not because a mathematical proposition
had been disproved. No frozen Git predecessor is claimed for that test-first log.

[Public tests](../../scripts/test-migration-service.py) exercise real subprocess
IO, phase snapshots, requests during all waiting phases, finite sink refusal,
failures/cancellation, incremental output before EOF, a long bounded stream and
malformed input. A `/dev/full` test checks actual stream-error termination; the
exact external effect of a later failing write/flush remains a trusted IO boundary.
Existing reactive-service subprocess tests remain regression checks.

## Bounded measurements

The [raw measurements](between-ticks-migration-measurements.json) record 18 successful
samples: three repetitions of delay, redundant and forward-migrated sessions at
suffix lengths 16 and 64. The harness uses Python `perf_counter_ns` around public
command/response round trips on CPU 0, with Lean 4.35.0 and the recorded Linux host.
It records hashes of the exact operational sources, protocol `migration-byte-v1`,
realization identities and the full workload. The Git revision in that artifact
is the preimplementation baseline; file hashes identify the measured additions.

Startup ends at the first query reply. Request-to-quiescence begins with one
pending tick and includes the same sink refusal, requested 10 ms wait, acceptance
and retirement in each variant. Baselines use query controls where the migrated
variant requests, prepares and commits. Preparation and commit timings include
pipe IO, interpreter execution and scheduling, not just conversion instructions.

| Variant | Suffix ticks | Median startup ms | Median admission pause ms | Median pause plus suffix ms |
| --- | ---: | ---: | ---: | ---: |
| delay | 16 | 2183.315 | 10.207 | 10.634 |
| redundant | 16 | 2186.723 | 10.232 | 10.633 |
| migrated | 16 | 2194.107 | 10.234 | 10.681 |
| delay | 64 | 2178.922 | 10.185 | 11.623 |
| redundant | 64 | 2215.579 | 10.254 | 11.729 |
| migrated | 64 | 2198.474 | 10.249 | 11.801 |

Migrated preparation round trips had median 0.022 ms, and ownership commit
0.011–0.012 ms. These small timings do not resolve intrinsic converter cost or
establish a speedup or amortization crossover. They include interpreter/IO
costs on a host for which the owner reported thermal precautions. The existing
Circuit model predicts more work for the redundant realization; semantic
equivalence alone promises no performance benefit.

Formal preservation, declared logical resource costs, measured process timings
and trusted compiler/host/IO behavior remain separate claims.

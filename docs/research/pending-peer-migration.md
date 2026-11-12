# Pending peer migration (#480)

[PendingMigration](../../Applications/FRP/PendingMigration.lean) extends the
[between-tick experiment](between-ticks-migration.md) with an ordered in-process
peer. Transfer can happen with accepted, computed, or published but unconfirmed
work. The peer, request slots and event queue stay with the adapter while the
active Circuit backend changes. The two backends still implement the same
initialized Boolean delay.

This is a controlled executable peer. The adapter owns every event that can
refer to a slot; there are no independently delayed messages outside that
store. Process crashes, restart recovery and arbitrary external networks are
outside this contract. A failed output write terminates the runner and provides
no recovery evidence about an external recipient.

## Publication and knowledge

Admission reserves one of two reusable slots and appends it to the ordered
request list. Only its head can evaluate or publish. Evaluation retains the old
logical state as output and the input as the next state. The peer publishes a
matching request once, recording its input and output. Matching retries return
its outcome without another effect; conflicting payloads are rejected.

Peer publication and session confirmation are separate transitions. Dispatch
can publish while dropping its reply. The session then remains computed with
its old active state, even though the source-level effect has happened. A query
or retry must produce and deliver a published reply before local tick commit
can install the input as the next active state. The session cannot read the
peer ledger to infer publication during migration or commit.

Cancellation is an explicit synchronous operation of this in-process peer. It
returns prevented when it replaces a reservation with a cancellation tombstone,
and too-late after publication. The latter response does not confirm the
request or advance local state. The pending second input can also be cancelled.
These returned outcomes are part of the selected peer API, not an implicit
observation of hidden state.

A prepared target freezes business operations. Preparation copies and validates
the current active continuation; commit changes its owner once. Cancellation,
allocation refusal, insufficient budget and validation failure preserve all
accepted work and leave the old backend authoritative. A published but
unconfirmed head retains both its input and output, its computed phase, and
the stable peer ledger through the transfer. It therefore retains the logical
source obligation until reconciliation and local commit finish.

## Retirement and progress

Terminal committed or cancelled work closes its route. Closing blocks new
publication, retry and query submissions for that request. Already queued
traffic is consumed without creating replies on the closed route. Release
checks the entire event store for references, including publish, retry, query
and reply messages, before clearing the request and peer slot. A terminal slot
still consumes admission capacity until release succeeds.

[PendingMigrationSafety](../../Applications/FRP/PendingMigrationSafety.lean)
proves that successful release excludes every message kind. The finite-token
negative control accepts an old false response after one-bit generation
wraparound even though the current response should be true. Actual reuse relies
on owned-event retirement, not a generation token or a timeout.

[PendingMigrationProgress](../../Applications/FRP/PendingMigrationProgress.lean)
assigns rank two to requests and rank one to replies. Each dispatch decreases
rank, including when a request generates a reply. With at most four queue
entries, eight public dispatch opportunities empty the queue, provided no new
traffic is submitted and preparation does not freeze dispatch. Popping an entry
always leaves capacity for its response; the executable fallback cannot drop a
requested reply. Lost replies require an explicitly scheduled query or retry.
These are conditional scheduling bounds, not wall-clock or external fairness
claims.

## Continuation and resource evidence

`prepare_commit` identifies actual successful public prepare/commit execution
with checkpoint transfer. `suffix_related` preserves the complete checkpoint
and effective output trace for arbitrary finite business suffixes.
`repeated_migration` composes actual transfers in either direction at arbitrary
cuts and compares them with their migration-free schedule. These results do not
assume an initial checkpoint or a specific test fixture.
`suffix_observations` and `repeated_observations` additionally preserve the
command-aligned acceptance and cancellation outcomes, including too-late
cancellation, rather than only the business output list.

[PendingMigrationSource](../../Applications/FRP/PendingMigrationSource.lean)
separately defines an independent delay source with a logical state and pending
input occurrences. Acceptance appends an occurrence, successful cancellation
removes the selected pending occurrence, and publication consumes the oldest
remaining occurrence while emitting the old state. Confirmation and commit
cannot advance that source twice. `step_refines` proves every actual command
implements a source step, and `execution_refines` lifts this to arbitrary finite
schedules from any valid checkpoint. `initial_no_loss` accounts for every
accepted occurrence as pending, effectively published, or prevented;
`reachable_owners` proves distinct occupied slots exactly match admission order,
including quarantined requests. The proof-only source projection may inspect
the peer ledger to describe effects; executable session confirmation cannot.

[PendingMigrationResources](../../Applications/FRP/PendingMigrationResources.lean)
counts both participants and the framing reservation. Two request slots, two
peer entries, four queued events and both backend copies use at most 138 retained
logical cells; a command uses at most 192 with temporary overlap. The queue
append/response branches count a complete new queue while the old list remains
live. Evaluation includes the existing Circuit arena bound. One-byte input
parsing and bounded output frames retain no input line or lifetime transcript.

Preparation emits its actual budget, allocation attempt, allocation, copy,
validation and release events. Budget refusal allocates nothing; allocation
refusal records only an attempt. Validation failure allocates and then releases
the target and scratch space. Successful preparation releases scratch, retains
the target alongside the old owner, and later ownership commit releases the old
backend. Cancellation releases the prepared target. The lifetime theorems
interpret those executed traces and prove releases cannot exceed live cells.

Work follows the actual command transitions, including refusals, bounded scans,
Circuit evaluation, conversion and validation. A command costs at most 14 model
operations; a finite schedule costs at most 14 times its length. Environmental
admission, scheduling, publication, confirmation and retirement delays remain
separate parameters. These are logical storage and operation models. They do
not measure Lean's allocator, garbage collector or operating-system buffers.

The reuse boundary is deliberate. The existing `MigrationPair` conversions,
`MigrationSafety` prepared ownership record and `MigrationResources` Circuit
costs apply directly. The [frontier](../../Applications/FRP/Frontier.lean)
protocol closes timestamp windows under source honesty; it does not own these
reply events. [Durability.Protocol](../../Applications/Durability/Protocol.lean)
uses a retained accepted history and crash/recover observations, while
[RetentionBanks](../../Applications/Durability/RetentionBanks.lean) models
persistent bank publication. Neither contract supplies reusable peer identities
with bounded callback retirement. This implementation adds no shared recovery
or scheduler interface.

## Running the adapter

Run `direnv exec . lake env lean --run scripts/pending-migration.lean`, optionally
with `redundant` as the initial backend. Newlines are ignored; every other input
byte must name a command. Business frames are `B:0` or `B:1`, status frames begin
with `C:`, and queries return backend, committed state, occupied slots and queue
length.

| Bytes | Operation |
| --- | --- |
| `0`, `1` | Accept an input if a slot is available. |
| `e`, `p` | Evaluate head; queue publication. |
| `y`, `z`, `k` | Queue matching retry, conflicting retry, or outcome query. |
| `d`, `x` | Dispatch one message with reply delivery enabled or dropped. |
| `t` | Commit a confirmed tick. |
| `n`, `N` | Cancel the head or second request through the peer. |
| `c`, `l` | Close terminal head; release after all references drain. |
| `r`, `a`, `o` | Prepare redundant/delay; commit prepared ownership. |
| `b`, `f`, `v` | Exercise budget refusal, allocation refusal, validation failure. |
| `s`, `q` | Cancel preparation; inspect bounded current state. |

The required first fixture is `1epx0rokddtclepddtclq`. It accepts true, publishes
false with a lost reply, accepts false, migrates, reconciles and commits the
first request once, then continues. Its effective outputs are `[false,true]`
and final state is false. [Checked examples](../../Examples/PendingMigration.lean)
also distinguish early cancellation, too-late cancellation, refused unconfirmed
commit, failed preparation, quarantine, and finite-token wraparound.

The public [runtime tests](../../scripts/test-pending-migration.py) exercise
these paths and stream 256 inputs with slot reuse, dropped replies and repeated
migration, reading each response before submitting the next operation. The
stream test checks incremental behavior; the universal state bounds come from
the theorems. Invalid input fails immediately. The `/dev/full` test exercises
failure of the first acceptance control frame, before any peer publication.
Ordinary and quiescent migration runners keep their existing protocols.

# Indefinite service by finite reactive circuits

[#234](https://github.com/VladimirMarko/conaled/issues/234) establishes a sufficient
class with an executable witness: initialized Boolean circuits with a fixed
finite product state. Every accepted input yields one output, and the state
retained between steps has fixed representation shape. Sequential composition,
parallel composition and pure Boolean circuits stay in the class. An explicit
state delay permits feedback; instantaneous recursive circuits are excluded.

The formal resource guarantee is about an explicit circuit machine. The supplied
Lean runner executes the same circuit evaluator, but Lean compilation, allocation,
reclamation and IO remain trusted. There is no theorem of bounded physical heap
usage or uninterrupted service despite host failures.

## Public definitions and guarantees

- [Circuit execution](../../Applications/Circuits/Execution.lean) reuses
  `Applications.Circuits.Circuit`. `execute_correct` connects its executable
  evaluator to the existing Boolean interpretation. `executes` constructs a
  finite operational derivation for every input. `Executes.result` proves its
  result and calculated work/allocation totals agree with the static analysis.
- [Initialized service](../../Applications/FRP/Indefinite.lean) supplies
  `Program`: a circuit from input/state to output/state and an initial value.
  `Program.correct` preserves initialized-machine semantics. `Program.uniform`
  bounds every stream, prefix and internal allocation position with one bound
  determined before the stream is chosen. `Program.next` proves finite work for
  the next output. `Program.service` combines these distinct conclusions.
- `Program.seq_machine` and `par_machine` recover the existing synchronous
  composition laws. `seq_work` and `par_work` calculate the fixed wiring
  overhead. `Program.compiled` accepts the existing reactive compiler's circuit
  target; compilation is not repeated when inputs arrive.
- [Checked clients](../../Examples/IndefiniteService.lean) cover Boolean delay,
  two sequential delays, parallel delays, pure negation, a redundant state
  representation, and finite environmental waits. `delay_compiled` connects the
  operational delay to #231's compiled delay without changing its theorem.

No universal preservation record is introduced. Membership follows from a
concrete finite circuit body. This is a sufficient class, not a classifier for
all Lean programs, all finite-state implementations or all FRP semantics.

## What the resource model counts

`cells` counts Boolean payload cells. Product layout is fixed by its type and
can be represented as a flat block; unit has no payload cells. Every circuit
node reserves one evaluator frame and copies its finite input and output blocks.
The conservative arena keeps all those reservations until the tick finishes.
Composition includes the intermediate result; pairing includes the shared input
and first branch result. The allocation schedule follows the evaluator's node
order. `arena_prefix` bounds every partial schedule, including internal execution
positions, by its static total. End-of-tick reclamation restores the empty arena.

The retained bound is `cells stateType`; a tick's temporary arena is `body.arena`.
Their sum bounds the modeled live resource throughout the tick. Work counts
syntax-node dispatches, including one Boolean gate operation at a gate node.
Copies of statically shaped blocks are atomic operations in this machine; this
is not a claim that copying an arbitrary-width block takes constant physical
time. A lower-level realization must account for each copied cell and its own
representation, for example by charging work according to the arena cell total.
All widths and totals depend on the fixed program, never the execution length.
Cumulative work and cumulative allocation over infinitely many ticks may grow
without bound. Per-tick reclamation, rather than bounded cumulative allocation,
is what permits the uniform live-space bound.

The delay body visits three nodes, reserves 13 arena cells/frames, and retains
one Boolean outside the arena. The arithmetic is checked in the client module.
Two delays retain two Booleans and have a larger but still static arena and work
bound. The sequential constructor evaluates the first circuit once, passes its
bounded result to the second, and retains both updated states. Parallel wiring
uses a bounded pair and evaluates its branches synchronously. Neither creates a
queue. Pure operations are admitted through finite circuit expressions, not by
assigning a constant cost to arbitrary functions.

Immutable circuit syntax and its timing annotations are fixed program data.
Their resident storage is an additional configuration-dependent constant, outside
the tick arena. The rational gate annotations are never incremented and are not
runtime clocks. The model does not count Lean tuple metadata, reference counts,
allocator bookkeeping or operating-system buffers as Boolean cells.

## Productivity and environmental assumptions

Bounded storage permits silent waiting, so it is not the progress theorem.
`Program.Environment` supplies a finite input-readiness wait, scheduler wait and
sink-acceptance wait for each round. These are explicit premises about continued
inputs, eventual service and eventual output consumption. Their values need not
have a uniform bound. A missing input, unfair scheduler or permanently blocked
sink cannot provide the relevant finite witness.

`Program.starts` constructs round times from those waits and the independently
proved finite circuit work. `Program.Round` records the service phases and actual
operational evaluation. `scheduled_run` constructs the next round at every
prefix, and `productive` derives accepted outputs beyond every finite model
time. An infinite sequence of completion times is not assumed. A round finishes
before the next one starts, so output backpressure is part of the model.
The logical stream indices and model times appear only in proofs.

This is conditional productivity of the circuit service model. It does not prove
that a particular OS schedules the process fairly, that an external peer writes
forever, or that Lean IO completes without errors. It also supplies no physical
deadline. The runner exposes those assumptions at its input/output seam.

## Running the witness

From the repository's development shell, build once and run:

```sh
lake build Applications.FRP.IndefiniteIO
printf '10110' | lake env lean --run scripts/reactive-service.lean
printf '10110' | lake env lean --run scripts/reactive-service.lean twice
```

The outputs are `01011` and `00101`, respectively, with no added newline.
The [IO adapter](../../Applications/FRP/IndefiniteIO.lean) reads one byte, accepts
ASCII `0` or `1`, executes one transition, writes one byte and flushes before
reading again. It retains no earlier inputs, outputs, IDs, timestamps or tick
counter. An absent input blocks; EOF ends that externally supplied finite session.
Malformed input throws before its transition. IO errors also abort the session;
earlier outputs are not rolled back, and a write/flush error does not establish
whether the peer observed an output. There is no retry or crash-recovery claim.

The adapter requires streams honoring the one-byte read request and bounded
write/flush buffering. Standard stdin/stdout are the tested realization;
arbitrary user-supplied `IO.FS.Stream` implementations need their own contracts.
Lean's evaluator/compiler must implement the iterative loop with bounded stack,
reclaim obsolete values and avoid accumulating closure or allocator state.
Circuit evaluation has fixed syntax depth, but connecting its abstract frames
to the host stack and heap remains trusted. The OS and peers must provide bounded
buffers or backpressure if their memory is included in the desired system bound.
An infinitely fast producer's external backlog is not covered by this program's
retained-state theorem.

[Runtime tests](../../scripts/test-reactive-service.py) exercise known traces,
empty input, malformed input, argument errors, output before EOF, and a longer
session consumed incrementally. They test the actual public IO path. They are
not proofs of host resource bounds.

## Changing a backend without repeating client proofs

`Program.transport` specializes the existing `Feedback.transport` theorem.
Another backend supplies an input relation, state/output observations,
initialization and local transition preservation. The theorem carries those
observations to every state and output in the stream. It does not require state
representations to be equal or invertible.

`Program.transport_bound` uses #231's covered relational bound theorem for
reachable states. The backend supplies a monotone resource conversion and a
local comparison on related representations. Coverage follows from the same
transition simulation, so an empty relation cannot certify target execution.
The redundant-bit example recovers the same outputs and a two-cell retained
bound. Its own circuit `service` theorem separately supplies transition work,
temporary storage and progress; retained-bound transport alone supplies none of
those additional obligations.

Without these routes, a second representation needs another induction over all
stream prefixes for state/output preservation and resource bounds. The checked
client instead supplies one local step proof, initialization and a resource
comparison. The circuit-specific facade adds no new category or universal
contract class, and ordinary `Feedback` clients retain their public statements.
A backend with different clocks, partial failure or asynchronous observations
needs additional native contracts; it cannot inherit this synchronous schedule
by erasing those differences. [#235](https://github.com/VladimirMarko/conaled/issues/235)
owns that continuing compatibility and author-usability assessment.

## Exclusions and remedies

| Case | Why this criterion does not establish indefinite service | Needed change |
|---|---|---|
| Increasing `Nat` counter | A fixed field count does not bound the number of bits in its value. | Finite representation with a justified observation/exhaustion contract, or eliminate the counter. |
| Growing history | Every prefix is finite but the retained sequence length has no uniform bound. | Bounded history, aggregation justified by observations, or external storage with its own contract. |
| Unrestricted input payloads | Even one accepted value can exceed any fixed representation budget. | Fixed finite type, bounded admission or a streaming representation with its own proof. |
| Producer outruns an unbounded queue | Unconsumed outputs accumulate despite finite worker state. | Backpressure, finite capacity with explicit loss/admission behavior, or a stronger consumer assumption. |
| Finite IDs with arbitrarily delayed replay | Reused names cannot distinguish a new request from an old command carrying the same name. | #232's exclusion/retirement contract, changed observations or an identifier-free protocol. |
| Instantaneous feedback | A cyclic combinational equation need not have a unique, productive solution. | Explicit initialized state delay or a separately justified fixed-point semantics. |

The counter/history inequalities are checked in the example module. Queue growth
and information-loss negatives remain in
[the preservation experiment](../../Examples/PreservationBounds.lean).
Identifier elimination/replay is assessed in
[the request-identity note](frp-request-identity.md) and owned by
[#232](https://github.com/VladimirMarko/conaled/issues/232). The bounded external
frontier driver [#233](https://github.com/VladimirMarko/conaled/issues/233) is a
different protocol with different state and resource obligations; this witness
does not certify that driver as indefinitely bounded.

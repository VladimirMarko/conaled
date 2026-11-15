# Bounded runtime iteration with retained parity

Issue [#484](https://github.com/VladimirMarko/conaled/issues/484) extends the
bounded-service examples to a runtime fold. The installed capacity is fixed.
Each admitted batch contains at most that many Boolean samples. A tick emits
the old retained parity, folds XOR over the actual samples starting from that
bit, and retains the result. Empty batches still emit the old bit.

`BoundedFold.body` is first-order source compiled once to a circuit.
`BoundedFold.execute` visits the runtime list and executes that circuit at each
sample. `whole_fold` connects this resumed loop to the existing
`ListFoldCompiler.compile`; `source_preservation`, `compiled_iteration` and
`visits` connect it to the existing source fold and its finite execution count.
The seed-parametric whole-fold equation is a proof: the executable loop does
not compile its current state at each tick. This is runtime finite recursion,
not compile-time unrolling. The stream semantics describes repeated ticks,
not an instantaneous recursive feedback loop.

The independent fixture was frozen before implementation. Starting false,
batches `[true,false]`, `[]`, `[true,true,true]`, `[false,true]` emit
`[false,true,true,false]` and finish true. The batches contain 1, 0, 3 and 1 true
samples. `fixture` connects these literal expectations to `run_correct`.
Capacity zero, arbitrary initial bits, nonempty-prefix resumption and a
negation consumer exercise different observation and lifetime cases.

## Storage and execution

The selected model counts logical cells, not Lean heap bytes. Every Boolean
list node owns a payload and a link cell. A terminator, old retained state,
accumulator, cursor and control frame add five cells. The cursor is an address
in the fixed-capacity buffer; its word width depends on that installation.
There is no unbounded integer identifier, logical time or history in retained
state. Gate delays are fixed syntax labels, not growing numerical state.

`resident n = 2*n + 5` counts the whole batch throughout evaluation. Each
iteration uses the existing circuit copied-value arena. Its internal allocation
prefixes are included in `iterationTrace`. The next accumulator is copied while
the old accumulator and arena are still live. Then the arena and old
accumulator are reclaimed before the next iteration. At completion, output and
next state are copied before acceptance releases the batch and the remaining
working cells. Exactly one retained bit remains. Input ownership is bounded
in the execution judgment: the remaining list length cannot exceed the owned
batch capacity.

`Executes` records actual compiled-body evaluations, result states, work and
these lifetime transitions. `executes` constructs a derivation for the real
runner; `Executes.result` identifies its result, work and trace. `trace_bound`
proves the allocation bound, including internal circuit allocation positions.
The uniform bound is `resident C + code.arena + 2`, independent of the number
of ticks. This is a conservative bound; it need not be attained for an empty
batch. `uniform` quantifies over every admitted stream and tick.

The lifecycle charges are separate:

- Initialization installs the fixed circuit/configuration and writes the one
  retained Boolean. Code installation is outside the per-tick bound.
- The core service receives a `Batch C` with its capacity proof. Optional
  `ingest` examines at most `C+1` constructors and rejects without inspecting
  the remaining tail. `ingestion_bound` proves this inspection count and
  `ingest_rejected` characterizes capacity failure. Accepted ingestion copies
  two logical cells per sample plus a terminator. Its implementation is a
  host wrapper, not a verified allocator. The producer owns the external
  source list; its allocation is outside the service's ownership claim.
- Each iteration charges circuit dispatches plus sample dispatch, result copy
  and reclamation. Finish charges two copies and acceptance. `work_bound`
  gives `C*(code.work+3)+3` for the transition/observation lifecycle, excluding
  ingestion and environmental waiting.
- While the sink waits, the current output and batch remain owned. The next
  batch is not accepted. Sink acceptance releases them. No output queue is
  introduced.

Traces, completion times and proofs are ghost observations. The executable
loop does not retain them. The process-level test harness collects finite
outputs for comparison; it is not an indefinite bounded-heap IO driver.
Lean's allocator, tail-call behavior and garbage collection remain a trusted
host boundary. These proofs establish the declared logical machine's resource
contract, not a measured or verified bound on host allocation or wall time.

`Round` combines local evaluation with finite input, scheduler and sink waits.
`scheduled` constructs rounds from those premises. `productive` derives
unboundedly many accepted rounds without assuming a completed output schedule.
No progress is claimed when input never arrives or the sink never accepts.

## Admission and composition

`Realization` preserves arbitrary state carriers and native semantic
observations. `assess` returns an accepted realization and evidence, a capacity
rejection, or unsupported analysis. `Admission.run` executes the returned
realization. `BoundEvidence.executor` identifies the analyzed runner, and
`admitted_execution` connects its accepted evidence to an actual execution and
all allocation checkpoints. An unknown analysis does not reject the semantic
route. This is one bounded extension of #481, which remains an umbrella; it
is not an analyzer for arbitrary Lean functions.

`BoundedFold.Regional` composes the actual fold with a copied Boolean boundary
and a circuit negation consumer. The adapter retains the last transferred bit;
a reserved boundary slot and synchronization frame remain live through the
fold. After batch release, the next fold state and those three cells coexist
with the consumer's arena and output copy. `Regional.Executes` links both
executions to the composed trace. The whole bound is the maximum of the fold
bound plus three and the consumer arena plus five. `boundary_separator` finds
an actual checkpoint that exceeds the independent fold budget even though the
consumer fits that budget too. `Regional.scheduled` and `Regional.productive`
also construct service for the composed executor under finite environmental
waits, charging consumer and boundary work. Region budgets therefore cannot simply be
checked independently against one shared capacity.

This local composition does not change #485's plan grammar or claim automatic
fold-leaf admission by its existing F/D/N catalog. It supplies concrete resource
and execution contracts for #486 whole-plan selection. Ranking must charge
analysis, policy work and conversion, preserve the selected executor identity,
and reconsider evidence when context changes. A semantic equality alone does
not transport an allocation schedule.

## Separating cases

`growing_counter` rejects one fixed bound for unary exact naturals, whose
representation at value n contains n cells. It does not reject bounded modular
counters or observational quotients. `retained_history` rejects one fixed bound
for arbitrary exact retained Boolean histories. A summary bit and a service
that applies backpressure have different storage observations.

`unbounded_iteration` shows that the same terminating runtime fold has no
uniform work bound over arbitrary lists. Every individual list still has the
finite execution supplied by `visits`. Input ownership itself also grows with
unbounded lists. Bounded input is a sufficient class, not a universal necessary
condition: a different streaming interface could bound live space while total
work grows.

## Transfer and remaining extensions

At a quiescent boundary after sink acceptance, transfer must preserve retained
parity, installed capacity and input representation, compiled-body identity,
and the adapter bit if the composed runner is used. Validity includes the
capacity contract and the encoding of every retained bit. A direct Boolean
copy costs one cell write and overlaps old/new state for two cells; adding the
adapter doubles both retained payload and copy work. An ownership token/frame
and configuration validation require additional implementation-specific space
and work. These figures exclude those controls and do not constitute a new
migration executor or theorem. #464's Boolean/redundant-pair migration is a
reuse input, not already a proof for this fold.

An in-flight transfer additionally needs the owned batch, remaining cursor,
accumulator, old output, publication/acceptance phase, any live arena, and
retirement/cancellation obligations. Restarting from just parity can duplicate
or omit sample visits or outputs. The pending-work protocol remains owned by
[#480](https://github.com/VladimirMarko/conaled/issues/480). Its selected first
delivery is a bounded in-process ordered peer with query/idempotency and explicit
retirement covering callbacks, queries and retries, without crash recovery. That
selection is not an implemented migration contract for this fold. #487 must account
for old/new overlap, moved buffers, preparation, cancellation retirement and
progress under repeated changes. Regional productivity does not establish
progress under arbitrary repeated migration.

| Extension | Ownership and capacity | Progress and observations | Owner/reuse |
|---|---|---|---|
| Runtime closures | Code identity plus bounded environments, captured aliases and reclamation; distinguish shared from copied captures | Bound applications and allocation; preserve captured values and output order | #109, #483, #174; no runtime closure ABI selected here |
| Recursive data | Bound reachable nodes and payload sizes, sharing and reclaimable regions; fixed field count is insufficient | A terminating traversal may have input-dependent work; preserve demanded values and structure observations | #109, #174, #193 |
| Growing dependency graphs | Bound nodes, edges, retained subscriptions and queues; preserve sharing and retire removed nodes | Fair scheduling and bounded reconfiguration work; preserve dependency and event observations | #27, #194, #486, #487 |
| Numerical/error state | Fixed arity does not bound rational numerator/denominator bit size; error histories and certificates also own storage | Bound arithmetic and refinement work; preserve the selected enclosure/error observation rather than assuming exact finite representation | #27, #194; recovery remains #225 |

No universal scheduler, host GC, regional grammar redesign, effect protocol or
numerical representation is adopted by this client. The concrete missing
contracts already have owners above, so no duplicate pending-work successor is
created.

## Evidence

Public modules are `Applications/FRP/BoundedFold.lean`,
`BoundedFoldResources.lean`, `BoundedFoldRegional.lean` and
`BoundedFoldAdmission.lean`. Checked cases are in
`Examples/BoundedFoldReactive.lean`. `scripts/test-bounded-fold.py` compares the
public compiled runners with a count-of-true parity oracle, including full
outputs, final states, continuation and regional observation. It also checks
capacity/unknown outcomes, ingestion edges and the actual boundary separator.
The integration handoff records exact build, proof-audit and independent review
results; a focused local build alone is not acceptance.

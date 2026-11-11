# FRP runtime direction and bounded follow-ups

**Assessment date: 2026-11-11. Status: research snapshot with proposals for
owner selection.** Capability gaps, issue states and priorities below describe
the evidence at that date; this document is not a maintained execution plan.
Before using a proposal as pending work, check
[#27](https://github.com/VladimirMarko/conaled/issues/27), its linked follow-up
issues and the scope owners named below for later decisions and delivery
records, then check the corresponding source. Issue closure alone does not
establish that every proposal here was implemented.

**Owner direction recorded 2026-11-11, after the assessment:** the owner accepted
the compositional hybrid-runtime direction and the proposed starting sequence,
and explicitly requested live backend migration. [#464](https://github.com/VladimirMarko/conaled/issues/464)
owns that added capability; section G records its initial staged criteria. This records a scope decision,
not implementation or completion; the linked scope owners remain the place to
check subsequent work.

The investigation recommended an executable rational phase fragment with strict
switching and retained residual state as the next semantic milestone relative
to the inspected baseline. It also proposed a parallel FRP client reusing #436
to select a compiled realization before initialization. These recommendations
did not authorize runtime implementation, choose an external delivery protocol,
or create issues.

The long-term recommendation is a compositional, demand-driven hybrid runtime:
compiled discrete and continuous phases, explicit event order and knowledge
frontiers, bounded admission and backpressure, alternative execution targets,
and optional recovery under storage and peer contracts. This is a feasible
research direction because several constituent contracts already exist. It is
not an estimate of delivery effort or a claim that their composition is proved.

## Evidence boundary

Local source was inspected at `3c064b11a5812e38c317601473e6897f65ce2a32`.
The corrected runtime overview at
[`c58e1be4`](https://github.com/VladimirMarko/conaled/blob/c58e1be4c4ec77c1deb7d2fbdfd694283931bb6a/docs/research/frp-runtime-follow-up.md)
was also inspected; this note adds decisions and proposed specifications without
repeating its edit. GitHub issue bodies, relevant delivery comments, and open
issue searches were checked on 2026-11-11. In particular,
[#27's body](https://github.com/VladimirMarko/conaled/issues/27)
at that date distinguished completed kernel work from unselected runtime proposals.

The repository's [glossary](../../GLOSSARY.md) calls a backend an interpretation
with preservation obligations. Such a backend need not emit native code.
This assessment follows that distinction and the
[language direction](../language-direction.md): mathematical behavior,
observations, realization operations and their laws stay separate. It proposes
no replacement for existing denotational mathematics or one universal runtime
interface. [ADR 0001](../adr/0001-modules-and-proof-dependencies.md),
[ADR 0002](../adr/0002-relations-and-synchronization.md),
[ADR 0008](../adr/0008-timing.md), and
[ADR 0010](../adr/0010-composition-and-proof-audit.md) constrain the reuse below.

## Capability and issue map

| Owner question | Delivered evidence | Remaining ownership and gap |
|---|---|---|
| Executable dynamic switching and phase evaluation? | [`Event.switcher` and `RNF`](../../Applications/FRP/Spec.lean) give noncomputable real-time denotations. Changes at `s` affect only times strictly after `s`; ordered occurrences determine the final selected phase. | Open [#27](https://github.com/VladimirMarko/conaled/issues/27) explicitly owns executable phase syntax, evaluator correctness and switching residual state. It is a scope owner, not a ready implementation specification. |
| General asynchronous scheduler? | [`Engine.step`](../../Applications/FRP/Engine.lean) executes concrete two-source commands; [`Frontier.observeMerge`](../../Applications/FRP/Frontier.lean) waits for both strict frontiers. [`Program.productive`](../../Applications/FRP/Indefinite.lean) constructs a synchronous service schedule under finite input/scheduler/sink waits. | #27 owns a demand-driven graph scheduler, wakeups, cancellation, reclamation, schedule independence and conditional progress. These delivered command/synchronous machines are not that scheduler. |
| Continuous integration? | The FRP denotation leaves `integral` without an adopted analytic contract. A separate [`CheckedMotion.checkedStep_correct`](../../Applications/Orbifold/CheckedMotion.lean) proves rational Euler error propagation for a specific disk-motion field. | #27 owns analytic integration and predicate-event semantics. The numerical motion implementation is reusable evidence, not a generic FRP integration primitive. |
| Crash-recoverable external delivery? | [#233](https://github.com/VladimirMarko/conaled/issues/233) supplies a bounded driver; [`DriverIO.drive`](../../Applications/FRP/DriverIO.lean) aborts after ambiguous publication failure. [#240](https://github.com/VladimirMarko/conaled/issues/240), [#241](https://github.com/VladimirMarko/conaled/issues/241), and [#251](https://github.com/VladimirMarko/conaled/issues/251) supply related recovery, diagnostics and retention models. | Open [#225](https://github.com/VladimirMarko/conaled/issues/225), [#196](https://github.com/VladimirMarko/conaled/issues/196), and [#194](https://github.com/VladimirMarko/conaled/issues/194) own durability and external interaction. No integrated crash-recoverable FRP adapter was found; it needs a bounded child scope linking input, state commit, publication, acknowledgment and retries. Closed [#226](https://github.com/VladimirMarko/conaled/issues/226) is prior assessment, not unfinished implementation. |
| Compilation through the categorical compiler to another backend? | Closed [#228](https://github.com/VladimirMarko/conaled/issues/228) delivers [`ReactiveCompiler.compile`](../../SquareKit/ReactiveCompiler.lean), storing target seed/body morphisms. [`ReactiveConsumers`](../../Applications/FRP/ReactiveConsumers.lean) uses executable functions. [`Program.compiled_source`](../../Applications/FRP/Indefinite.lean) connects actual Boolean circuit-target compilation to source meaning. | Alternative target interpretation is already implemented. A further target owes primitive interpretations, local soundness and execution. No dedicated open FRP native-code emitter issue was found. Open [#109](https://github.com/VladimirMarko/conaled/issues/109) owns recursion/fixed-point compilation, not all backend emission. |
| Policy-directed runtime choice? | Closed [#436](https://github.com/VladimirMarko/conaled/issues/436) delivers finite admitted selection, contextual observations/fallback, and distinct scan and prepared-tree clients. | No FRP client or dedicated open FRP policy integration ticket was found. Open [#235](https://github.com/VladimirMarko/conaled/issues/235) retains preservation and usability ownership. Startup selection is a bounded new application; live state migration needs additional operations and proofs. |

Closed #229/#230 connect command execution to compiled consumers and sequential
request state. Closed #232/#236/#237 address identity and retention under
different contracts. Closed #234 establishes a nonempty compositional
indefinite-service class. Their results are inputs to new work, not prerequisites
to reopen. See the [pipeline](reactive-pipeline.md),
[exclusive adapter](exclusive-request-adapter.md),
[retention](frp-query-retention.md), and
[finite-circuit service](indefinite-reactive-service.md) records.

The negative tracker findings are bounded by the search: repository-scoped open
issue queries for `FRP`, `backend`, `switching`, and `436`, up to 100 results
each, followed by inspection of relevant issue bodies. They found umbrella
ownership and completed deliveries, but no dedicated emitter or policy-client
ticket. An issue using unrelated terminology could escape these queries.
Recheck before creating any child issue.

## Interfaces to reuse before adding runtime abstractions

| Existing interface | Reuse and local obligation |
|---|---|
| [`FirstOrderCompiler.Target` and soundness](../../FirstOrder.lean), [`ReactiveCompiler.Compiled`](../../SquareKit/ReactiveCompiler.lean) | Compile initialized first-order seeds/bodies once; `realize_compile` and `run_sound` discharge compiler induction. A backend supplies its operations and primitive laws. Changing state representation additionally requires simulation; the current exact compiler theorem does not construct it. |
| [`Circuit`](../../Applications/Circuits/Syntax.lean), [`execute_correct` and `Executes`](../../Applications/Circuits/Execution.lean) | Reuse the typed circuit representation and actual evaluator as a second target, including static work/arena analysis. Its Boolean value correctness is distinct from analog stability/timing equivalence in ADR 0008. A physical deadline cannot be inferred from syntax work or modeled depth. |
| [`Initialized`, `Feedback.transport`](../../Applications/Progress/Feedback.lean), [`Progress.Feedback.run_related`](../../Applications/Progress/Reactive.lean) | Relate initialization and each transition, then reuse finite and stream results. Keep output and retained-state relations explicit. Relations alone neither compute a transfer nor prove progress. |
| [`Program.transport` and `transport_bound`](../../Applications/FRP/Indefinite.lean) | Recover the finite circuit client's observations and retained-state bound for another backend. That backend still owes finite transition work and temporary-space bounds. The existing uniform theorem counts Boolean cells/arena frames, not physical Lean heap bytes. |
| [`Frontier.State.Completes`, `advance_sound`](../../Applications/FRP/Frontier.lean), [`Pipeline`](../../Applications/FRP/Pipeline.lean) | Preserve complete ordered batches, multiplicity and source honesty assumptions. A frontier is knowledge strictly before its value. Silence is distinct from an emitted empty batch: only actual delivery ticks the consumer. |
| [`Exclusive`](../../Applications/FRP/Exclusive.lean), [`Retention`](../../Applications/FRP/RetainedLifecycle.lean) | Reuse serialized admission or explicit future-query bounds where their contracts fit. Exclusive operation excludes stale request callbacks by its communication contract; it does not detect them. Retention rejects expired queries rather than answering with an empty batch. Neither provides cancellation or crash recovery. |
| [`Choice.select`, `selected_contract`, `select_none_iff`, `select_map`](../../Applications/Optimization/Choice/Selection.lean) | Admit semantically valid realizations before ranking. Preserve the selected contract independently of score; use `none` for empty admission. Embedding/nesting needs matching admission and score conditions, not a new chooser. |
| [`Choice.choose`, `Epoch.complete`, `admittedContext`](../../Applications/Optimization/Choice/Evidence.lean) | Use exact declared implementation/target/workload/site/protocol/requirements/catalog context. Revalidate deserialized epochs; incomplete or mismatched evidence selects the fixed policy for the whole catalog. The generic selector does not own sessions; a stateful client must retain its chosen strategy with its state. |
| [`Measured.bind` and reweighting](../../Applications/Resources/Measured.lean) | Compose explicit costs and erase them separately from semantics. Charge selection, instrumentation, feature extraction, preparation, conversion, buffering and execution at their actual boundaries. Semantic equivalence gives no speedup theorem. |
| [`Durability.Protocol`](../../Applications/Durability/Protocol.lean), [`RetentionBanks`](../../Applications/Durability/RetentionBanks.lean) | Reuse accepted-history refinement, persistence-before-root-publication and crash-cut arguments. Atomic durable root installation and retained cells are explicit target assumptions. Bank reuse has its own ownership/query contract; it is not a generic storage driver. |
| [`CheckedMotion`](../../Applications/Orbifold/CheckedMotion.lean), [`NumericalExecution`](../../Applications/Orbifold/NumericalExecution.lean) | Reuse executable rational checks, accumulated approximation packets and finite execution composition as a concrete continuous client. Its field/domain constants and exact trajectories belong to disk motion. General integration needs its own existence, stability, truncation and event-detection arguments. |

The [budget-driven disk driver](budget-disk-driver.md) already performs bounded
accuracy-directed subdivision selection. It tries a prefix of 1, 2, 4 and 8
subdivisions from the same incoming error packet, charges discarded attempts,
and preserves the committed prefix on failure. Its
[`Driver` implementation](../../Applications/Orbifold/Driver/) supplies a
concrete policy consumer to compare with #436; it does not yet use #436's shared
selector or connect to the FRP lifecycle. Packet-bit guards exclude arithmetic
temporaries, and process limits remain operational assumptions. Preserve this
existing adaptive capability when designing a hybrid client.

The existing [graph-core emitter](graph-emission-implementation.md) emits a
bounded proof fragment to Lean expressions. Its typing/denotation and producer
validation separation is relevant design evidence, but it does not emit
`ReactiveCompiler.Compiled` circuits as standalone native programs. A new
emitter must identify its artifact language, execution semantics and trusted
toolchain boundary. Running the present Lean implementation through Lean's
ordinary compiler is also distinct from adding a categorical backend emitter.

## Runtime ambition and policy interaction

Retain independent denotational and operational layers. Source switching changes
the selected behavior according to an event history. Backend replacement keeps
the same source behavior and changes its realization. At a switch, residual
state must implement the source's boundary rule; at a backend replacement, state
conversion must preserve the future observations of the existing computation.
Neither operation can be justified by comparing only the next aggregate output.
For example, two consumers with equal totals can retain different delayed values
and disagree on the next input. This is a proposed separating case, not a new
checked theorem.

The runtime should admit program/backend/workload combinations with explicit
resource and progress contracts. A fixed finite circuit already supports
arbitrarily many synchronous rounds in its abstract model. More general graphs
need bounds on live nodes, outstanding demands, values, timestamps and queues,
plus reclamation and backpressure. A fixed number of `Nat` fields is not a
fixed representation bound. Arbitrary dense-time computation, unbounded
history queries, growing counters and permanently blocked sinks cannot inherit
#234's theorem. Preserve those useful unrestricted mathematical specifications
while stating the narrower admitted execution class.

#436 should participate first at session creation or compilation. Admit targets
using semantic, resource and target-capability contracts, then rank admitted
choices using fixed or validated empirical evidence. Freeze the chosen target
and its state for that session. Later choices may rank scheduler plans, phase
representations or numerical methods only after their respective legality and
error contracts exist. Nested local choices must preserve the enclosing
contract; locally cheaper work/depth does not justify arbitrary contextual
pruning. [The choice implementation](policy-directed-choice.md) records that
limitation and its existing clients.

This is justified reuse, not evidence that tuning will pay for itself. The
[#436 closure receipt](https://github.com/VladimirMarko/conaled/issues/436#issuecomment-6769708358)
records mixed historical measurements and no recovery of training cost over
the measured requests. Those runs used `Lean --run`; later source changes make
their old evidence context inapplicable. Stale pending-review paragraphs in the
research note do not override the closure receipt. A new FRP experiment must
measure its own target, include cold initialization and amortized session costs,
and retain cases where fixed selection wins.

Continuous phases should support exact rational fragments first and certified
approximation where needed. Dense-time strict causality does not imply a
productive feedback construction. A hybrid extension must state non-Zeno or
bounded-horizon assumptions, initialization, flow existence/uniqueness where
required, domain validity, numerical error and event-location uncertainty.
Predicate crossing cannot be inferred from sparse samples without additional
assumptions. Numerical error must survive switches and conversions rather than
resetting to zero. The existing [numerical motion](numerical-motion.md) achieves
this for a specific field; it supplies no generic sparse-event detector.

Recovery should be an optional realization contract. Retained semantic state,
persistent data-structure versions and crash durability are different claims.
The [accepted-history implementation](accepted-history-implementation.md)
preserves committed ordered history under its modeled primitives. External
delivery additionally needs a peer observation contract: if output took effect
but its acknowledgment was lost, retry can duplicate effects unless the peer
deduplicates stable identities or an appropriate atomic protocol couples the
effect and its receipt. An FRP frontier does not settle that ambiguity.

## Implementation proposals and subsequent owner direction

At the assessment date, the preferred first milestone was A. B was proposed to run
alongside it. C extends the compiler without depending on general scheduling.
D builds on A's execution contract; E and F are separately selectable consumers.
The later owner request adds G as required runtime scope. Its first stage can
reuse B's session machinery and existing targets; it does not require C's new
artifact emitter. Its second stage needs the chosen queue/publication contract.
None requires closing #27, #109, #194, #196, #225 or #235.

### A. Rational phase evaluation and strict switching

Proposed owner: #27. Implement rational constant/affine phases with real-valued
denotation, rational queries and a finite ordered catalog of phase-change
packets using the existing strict-frontier protocol. Retain the active phase,
activation time, and residual phase parameters; use a sequential exclusive
request owner. Reject a query older than the admitted lower bound. This first
fragment need not introduce asynchronous workers, arbitrary source recursion,
integration, or online generation of arbitrary code.

Acceptance requires an evaluator theorem for every admitted phase/query and a
constructed state invariant linking the executable selected phase to
`denoteRNF`. Prove the finite-run observation theorem for every admitted packet
trace, preserving order and repeated equal-time changes. Check the old phase
at the switch timestamp, the last ordered change strictly afterward, empty
change batches, delayed frontier completion, repeated queries and rejected
backward queries. Include a time-dependent phase whose value exposes an
incorrect restart of its local clock. Prove retained-state/temporary-work bounds
for explicit capacities and rational representation assumptions; a finite
catalog alone does not bound rational numerator/denominator growth.

The owner must select the exact phase grammar and query-retention contract
before implementation. Compare direct phase evaluation with compiling its pure
arithmetic through `FirstOrderCompiler`; reuse compilation where it removes
recurring proof work. Record unsupported stateful phase forms explicitly.

### B. Session-start policy selection for compiled finite FRP

Proposed coordination: #27/#235, reusing completed #436. Use one Boolean
initialized source program and two executable realizations: the function target
and the existing circuit target. Both must derive from `ReactiveCompiler.compile`
and preserve the same initialized output stream. Retain the chosen realization
and its state in a session package; no reselection occurs during that session.

Reuse `choose_contract` for correctness independent of ranking and supply
decidable admission for stated capability requirements. An unsupported resource
claim must exclude a candidate from that requirement, not treat its missing
bound as zero. Exercise a composed delayed program, fixed selection, complete
empirical evidence changing the next session's selection, mismatched/incomplete
evidence fallback, duplicate candidate identities and no admissible candidate.
Reject or fall back on ambiguous evidence identifiers using the existing epoch
validation behavior. Compare complete ordered outputs and final-state relations,
not only sums.

Measure compilation/preparation, feature extraction, admission/selection,
instrumentation, conversion, per-step execution and transport on one declared
target across short and longer bounded sessions. Report total training cost and
whether any observed savings repay it. Do not require a speedup for acceptance.
Preserve #234's circuit bound; claim a corresponding bound for the function
target only if separately justified. A result that no useful admission or cost
difference exists is evidence to narrow the next experiment.

### C. Executable backend artifact for a bounded reactive fragment

Proposed owner: a new scoped child coordinated with #27/#235, after duplicate
search and explicit artifact-target selection. Start with finite Boolean
seed/body circuits, sequential composition and one-tick delay. Compare reusing
`Circuit.interpret` with a new `FirstOrderCompiler.Target`; choose the route that
reuses frontend proofs and gives an independently executable artifact.

Acceptance requires a specified target artifact, evaluator, initialization and
step semantics, with correctness factored through local target laws and
`ReactiveCompiler` preservation. Demonstrate emitted seed/body artifacts running
multiple inputs while retaining target state, including a composed delay and an
order-sensitive example. Reject malformed or unsupported artifacts explicitly.
Account for representation and temporary storage. If native C, LLVM, WebAssembly
or another external toolchain is selected, specify which lowering is proved or
translation-validated and which compiler/runtime behavior remains trusted;
execute the emitted artifact in tests. An interpreted syntax tree alone must
not be reported as native-code emission. General recursion remains #109's scope.

### D. Bounded demand graph with cancellation

Proposed owner: #27 after A establishes phase execution. First support a fixed
finite dependency DAG, bounded demand slots, finite-value discrete nodes and
explicit delayed edges for feedback. Define pure scheduler transitions, a
bounded ready queue, dependency/frontier wakeups and cancellation ownership.
An IO worker adapter is a later boundary unless selected explicitly.

Prove each delivered observation sound for every completion of known inputs,
no duplicate/lost accepted demand, and schedule independence of the selected
output observation. Internal silent transition counts need not be equal across
schedules; declare their observation mapping before comparing temporal laws.
Conditional progress requires fair enabled scheduling, terminating evaluators,
source completion and sink consumption. Prove bounded live queue/node storage
under capacity admission and backpressure. Check cancellation before dispatch,
during pending dependency work and after completion; a late callback from a
cancelled/reused slot must not satisfy new demand. Also check a shared dependency
with one surviving owner and a blocked sink. General dynamically growing graphs
and unrestricted distributed scheduling remain outside this first contract.

### E. One certified continuous phase client

Proposed coordination: #27 with the existing numerical motion work. First wrap
the admitted rational disk-motion steps and bounded subdivision driver as a
finite-horizon phase client,
reusing `checkedStep_correct`, accumulated packets and `run_append`. Define the
bridge from source phase time/control boundaries to its existing exact timed
commands before claiming FRP integration. Alternatively select an affine ODE
with an exact rational solution; do not require both to close this experiment.

Acceptance requires endpoint and clock correspondence, rejection outside the
admitted domain, carried error across a phase switch and a composed run, and a
resource contract that includes rational arithmetic. Record the flow/domain and
step-size assumptions supporting the error result. A negative example must
expose resetting accumulated error or accepting an uncertified domain step.
Do not claim arbitrary integration or event detection. A later detector needs
its own crossing/isolation contract, treatment of tangency and missed crossings,
and a progress assumption excluding infinitely many required events in a finite
interval. Policy choice among solvers waits for comparable error contracts.

### F. Recovery of one sequential reactive session

Proposed coordination: #225/#194 with #27. Start with one writer, one outstanding
finite-value input and a finite-state consumer. Specify stable input identity,
state transition commit and pending output as one recoverable observation;
choose a deduplicating receiver contract or explicitly weaker at-least-once
publication before implementation. Define where acknowledgment is recorded and
what survives a crash. Preserve ordered source batches if the lifecycle is the
selected client; the simpler finite-value service must not be described as a
recovery implementation for every lifecycle query.

Construct the refinement into the accepted-history/storage primitives instead
of assuming whole-session atomicity. Check crashes before/after state commit,
after peer effect but before acknowledgment, during recovery, and during output
retirement; test conflicting retry payloads and repeated crashes. Prove no
duplicate consumer transition for an admitted identity and the selected external
observation guarantee under its peer assumptions. State conditional recovery
progress separately. First prove the model with an executable fault-injection
adapter; add a real storage/peer adapter only with explicit primitive contracts
and tests at that boundary. Reuse #251 retention only after its query, ownership
and identity constraints match; unbounded deduplication history is not bounded
service merely because consumer state is finite.

### G. Live backend migration within a reactive session

Owner-requested addition, recorded 2026-11-11 and tracked in
[#464](https://github.com/VladimirMarko/conaled/issues/464). Coordinate #27/#235, reuse #436
for policy selection, and coordinate #194/#225 when publication or recovery is
involved. Migration changes the realization of the same source computation
after it has processed inputs. It must preserve the continuation rather than
initialize a new session. Source-level switching in A changes the source
behavior and does not discharge this contract.

**First delivery: migration between ticks.** Use a finite Boolean reactive
program with delayed state and two executable realizations. Include a pair with
different state representations, such as a product of delayed Boolean values
and explicitly reordered registers; selecting the same representation under two
names is insufficient. Reuse B's session package where available. Compare
direct state conversion with a shared conversion interface before adding an
abstraction, and construct the transfer for the selected pair.

A migration request stops new admission at a defined boundary. Complete the
current tick and retire its output under the chosen sink contract before
transferring; the initial slice admits no pending input/output at the transfer
point. Construct a terminating executable transfer for every reachable source
state admitted by the migration contract, and prove that it establishes the
target invariant and state relation. Reuse `Progress.Feedback.run_related` from that
related state, and `Feedback.transport` for the continued stream, rather than
repeating the generic simulation induction. Prove preservation of the entire
ordered output continuation and retained state for every admissible input
suffix, including repeated migrations. A migration must not rerun source
initialization or replay an already consumed input.

Prepare the target while the old state remains authoritative, then give the
ownership change one explicit commit transition. A rejected request or failure
before commit leaves the old session usable; after commit only the target may
advance. Specify which preparation failures are modeled and how temporary
storage is released. Crash recovery is an additional contract, not a consequence
of atomicity in the transition model. Check migration after a nonempty prefix,
repeated migrations, an unsupported pair, a failed preparation, and a case where
resetting delayed state preserves the last output but corrupts the next one.

Apply #436 admission to the source/target pair, reachable-state requirements and
available transfer resources before ranking. Evidence must identify both
realizations and the migration protocol. Keep explicit migration requests usable
without a tuner. Charge conversion work, old and new state retained together,
temporary buffers, observation/selection costs and admission delay. Measure the
pause and any amortized benefit on bounded sessions; no speedup is required.
Conditional progress must include completion of the current tick and sink
retirement. A blocked sink may prevent reaching the transfer point; define
deferral or cancellation without losing accepted work. A pause bound requires
bounds on those waits as well as the transfer itself.

**Required successor: migration with pending work.** The first delivery does
not complete this broader capability. Select a bounded queue and publication
protocol, then transfer the outstanding requests, ordered input/output buffers,
frontiers, cancellation ownership, and publication/acknowledgment status with
the machine state. Define the cut separating work owned by the old and new
realizations. Prove that accepted work has exactly one owner across the cut,
that late callbacks cannot advance retired state or a reused request slot,
and that migration preserves the chosen external observation contract. Test
pending input, unpublished output, publication with a lost acknowledgment,
cancellation during transfer, and failed preparation. An already effective
external output must not be blindly replayed after transfer. Use F's recovery
contract if crashes during migration are included; otherwise state that boundary
explicitly. Completion of the first stage must retain a tracked successor for
these obligations, rather than relabeling migration between ticks as general
pending-IO migration.

For any selected formal implementation, acceptance includes checked positive
and separating applications, statement review, the applicable README build and
proof audit, independent Standards/Spec review, and runtime checks for the
unproved IO boundary. This report itself changes documentation only and claims
no new checked theorem or runtime measurement.

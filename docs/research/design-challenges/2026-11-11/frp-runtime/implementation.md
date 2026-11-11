# FRP runtime assessment: implementation and use

Baseline: `1ecdea2376786920a043009a35712a5dec93723a`, supplied source archive. Assessment date: 2026-11-11.

Retain the candidate's separation of denotation, executable realization, resource admission, and optional recovery. Change the order of experiments: use the existing synchronous service to test executable state transfer and session ownership early; settle phase query/commit behavior before building a shared hybrid execution interface. Keep startup policy selection as a small optional client. Its success would establish little about the difficult state and ownership boundaries.

This is a recommendation about what to learn first. The inspected code does not establish that one demand-driven hybrid runtime is necessary for these libraries, nor that it would fail. A synchronous service with separately composed phase and demand adapters remains a credible implementation organization.

## Strongest case for retaining the candidate

The proposed boundaries have useful existing implementations behind them:

- `ReactiveCompiler.compile`, `realize_compile`, and `run_sound` in `SquareKit/ReactiveCompiler.lean` compile seed and body once and establish the complete initialized machine and finite run, including state. Builders need local target soundness rather than a new proof for every reactive program.
- `Program.service`, `uniform`, `seq_machine`, `par_machine`, and `compiled_source` in `Applications/FRP/Indefinite.lean` provide a synchronous finite Boolean execution class, composition, and an explicit arena bound. `Examples/IndefiniteService.lean` exercises composed delays and a redundant state representation. This is stronger evidence than a planned runtime record with assumed correctness fields.
- `Progress.Feedback.run_related` in `Applications/Progress/Reactive.lean` starts from arbitrary related states and returns ordered output and final-state relations. It already supplies the continuation induction needed after a constructed transfer. Adding another generic migration simulation law would duplicate available machinery.
- `Frontier.advance_sound` and `observeMerge_sound` in `Applications/FRP/Frontier.lean` distinguish packet validity from source honesty and establish observations for compatible completions. The numerical driver similarly constructs `Selected` evidence from an actual guarded run (`Applications/Orbifold/Driver/Interval.lean`, `searchCandidates`), rather than asking its caller to supply the conclusion.

These support the candidate's local-contract approach. Keep ordinary callers of these libraries usable without policy contexts, scheduler construction, or persistence setup. The source evidence supports reuse of these components, not yet their end-to-end composition.

## Findings

### IU-1. Startup selection misses the state-representation boundary

**Established interface limitation; sequencing concern.** `ReactiveCompiler.realize` always produces state `Val B s`. Its target parameter changes stored morphisms, but the supplied denotation returns the same semantic state shape. Thus B's function/circuit selection can prove a useful compiler result while avoiding heterogeneous executable state and conversion entirely. This does not make B incorrect; it limits what B teaches about the intended session package.

There is already a smaller discriminating example. `Examples/IndefiniteService.lean` defines `redundant`, `related`, and `related_step`: a Boolean delay and a two-Boolean representation related by `v = (u, !u)`. It proves stream observation and a retained-state bound. The missing migration work is the executable conversion, ownership transition, failure behavior, and continuation from a noninitial state. The relational simulation itself is already available.

**Correction.** Bring G's first delivery forward as an explicit, untuned library operation. Use the existing delay/redundant pair, or a compiled pair with reordered registers, and construct conversions in both directions. Retain the old state during preparation and expose one commit point. Only then decide whether a general session package is worth its caller obligations. B can reuse the resulting package when helpful; neither needs asynchronous scheduling or artifact emission first.

**Discriminating test.** Process a nonempty prefix ending with retained `true`, fail one preparation, then migrate successfully and process a suffix whose first result depends on that retained value. Repeat the migration. Prove results through `run_related`, and separately test the executable failure/commit adapter. Compare caller code for direct conversion against the proposed shared package. Preserve source observations and the existing circuit resource theorem; add temporary storage for both states without claiming a host heap bound.

### IU-2. Phase retention must be designed around admitted queries

**Unanswered design choice with a paper separating case.** A proposes retaining active phase, activation time, and residual parameters, rejecting queries below a lower bound, and checking backward-query rejection. These requirements need one explicit query policy. `RNF` and `denoteRNF` (`Applications/FRP/Spec.lean`) are extensional: a selected phase is evaluated at the supplied global time. They do not prescribe a moving evaluation cursor. `RetainedLifecycle.step` permits a query whenever it satisfies the lower bound and other lifecycle conditions; the lower bound is not automatically the most recently answered timestamp.

Hypothetical separating case: retain lower bound 0; use phase value 0 until a strict change at time 1 to phase value 10; answer time 2, then time 1/2. Keeping only the newest active phase cannot answer both admitted queries unless some representation of the earlier phase remains. Rejecting the second query is legitimate if admission advances the lower bound, but is a stricter interface than retaining arbitrary queries above 0. A finite catalog of phase *forms* does not retain the ordered activation history by itself. Retaining the complete finite change schedule would solve this example, at an explicit capacity and scan/index cost.

The clock question is equally concrete: a phase denoting `t ↦ t` selected at time 5 yields 6 at query 6. Restarting its clock yields 1. A local-time phase is possible, but activation time must enter its denotation or parameters explicitly.

**Correction.** Select either monotone queries with reclamation, or a bounded historical query window with retained activation data. State how repeated queries, lower-bound movement, and a pending query interact. Reuse `RetainedLifecycle`'s pending-conflict rule if its policy fits; do not impose its entire source-log representation merely to inherit the rule.

**Discriminating test.** Compare a direct evaluator over a bounded ordered activation list with a cursor implementation on the same admitted trace, including time 1 itself, time 1/2 after time 2, repeated time 2, and two changes at time 1. Count retained activations and temporary rational arithmetic separately. This is a paper case, not a checked counterexample to an implemented A.

### IU-3. Bounded cancellation needs callback retirement, not only stale-ID checks

**Plausible risk shared by D and pending-work G.** The candidate correctly demands rejection of late callbacks after cancellation and slot reuse. It does not yet select the mechanism that permits bounded indefinite reuse. Existing `Lifecycle.Fresh` (`Applications/FRP/Lifecycle.lean`) uses a strictly increasing `Nat` high-water mark. `Exclusive` avoids executable labels for its sequential ownership discipline. Neither supplies bounded reusable asynchronous callback identities.

Paper adversarial schedule: dispatch work in a slot with a finite generation token; cancel it; retain its callback outside the runtime; reuse the slot enough times to repeat the token; deliver the old callback while the new request is pending. Token equality alone cannot establish ownership. An unbounded generation counter avoids token repetition but needs its own representation-growth contract. This argument applies to implementations using only that finite token for disambiguation, not to protocols that prove old callbacks impossible before reuse.

**Correction.** For the first demand adapter, quarantine a cancelled slot until its worker completion or cancellation acknowledgment retires the callback capability. Model occupied, cancelled-but-unretired, completed, and free states explicitly where needed. Capacity admission must count quarantined work and undelivered output. Progress then depends on eventual retirement as well as fair scheduling and source/sink cooperation. A synchronous pure scheduler may retire work immediately because no external callback exists; keep that simpler contract available.

**Discriminating test.** Use a deliberately tiny generation space, withhold one callback across repeated cancellation/reuse attempts, and verify either that reuse stops safely or that the old callback is rejected by a stronger ownership mechanism. Repeat with migration during quarantine and with a shared dependency whose other owner survives. This exposes whether boundedness comes from reclamation or merely from assuming that obsolete work disappears.

### IU-4. Numerical execution is currently a command transaction, not a read-only phase query

**Established difference between existing APIs; unresolved bridge.** `Numerical.run` in `Applications/Orbifold/NumericalExecution.lean` consumes durations and controls and returns final packet, samples, and elapsed time. `Driver.drive` in `Applications/Orbifold/Driver/Execution.lean` commits accepted intervals, preserves the pending suffix on failure, and carries the outgoing packet into the next interval. `searchCandidates` retries from the same incoming packet and charges failed attempts. These are useful transaction semantics.

A's phase evaluation is a query against a time-dependent denotation. Merely invoking the numerical driver for each query risks making repeated observations advance the system or accumulate error again. Conversely, permanently caching every observed packet introduces history storage absent from a simple active-phase record. The candidate acknowledges the bridge as an obligation, but postponing E leaves this distinction untested while A determines the phase interface.

**Correction.** Write a small bridge trial alongside A: separate committed command advancement from observation of an already determined endpoint, or explicitly admit only forward numerical advancement queries. Identify the authoritative packet, its time, incoming uncertainty, and when a trial result becomes committed. Preserve `selected_sound`, `selected_error`, `drive_partition`, and `run_append`; do not add duplicate error-propagation assumptions that follow from those results.

**Discriminating test.** Observe one endpoint twice, fail a later accuracy attempt, switch control, then continue. Compare committed endpoint/error/time with one unsplit command execution under the existing theorem hypotheses. Require repeated reads to preserve committed state when the selected interface promises observation. Include the trace/sample storage in the finite-horizon bound. The existing `Report.observations`, `Report.searches`, and `Result.samples` are retained lists; they cannot silently become an indefinite bounded runtime log.

### IU-5. The first delivery should expose the publication boundary before adding a general scheduler

**Sequencing recommendation supported by executable callers.** `Indefinite.serve` (`Applications/FRP/IndefiniteIO.lean`) reads one byte, computes, writes and flushes output, then advances its local state variable. `DriverIO.publish` explicitly treats flush as local publication, and exceptions terminate without retry. These are coherent current contracts, but neither distinguishes a peer effect from its acknowledgment. `Durability.Protocol.SpecStep` records accepted history and acknowledgments; it does not implement a receiver's external effect.

The candidate's F and G correctly reserve this distinction. A large pure DAG scheduler can still succeed without testing it. Its dependency on A is also not established by the existing code: finite-value discrete dependencies and delayed synchronous edges can be investigated without rational phase evaluation.

**Correction.** Keep a synchronous service as the default executable core. Add one explicit pending-output state and a sink acceptance transition for the selected client before generalizing admission ownership. Use that same tiny protocol to test pause, failed preparation, cancellation/deferral, and later recovery. D can remain a separate experiment justified by an actual multi-demand client; it need not inherit A's query state representation.

**Discriminating test.** Block the sink after computation, request migration, then release it. Verify that no next input is admitted at an unsupported boundary and the already computed output is neither lost nor recomputed. For F, separately inject the lost-acknowledgment case under the chosen peer contract. No local transition atomicity theorem should be reported as a crash-safe or externally exactly-once implementation.

## Caller effort and measurement

Compare a direct composed caller, an explicitly selected caller, and a tuned caller under the same output/state contract. Record the extra definitions each must supply: capability admission, candidate identity, evidence context, state invariant, conversion, and effect ownership. Do not infer author productivity from the existence of these records.

The current separation permits low-overhead ordinary execution. `Circuit.execute` computes no counters or trace; `work`, `arena`, and `allocations` are separate model functions in `Applications/Circuits/Execution.lean`. `Choice.Epoch.complete` validates the entire evidence set, and `policyScore` invokes that validation when constructing the score (`Applications/Optimization/Choice/Evidence.lean`). Startup-only selection can keep validation off the per-tick path. Measurements should verify that intended placement and include preparation, conversion, and observation costs. Existing synthetic evidence in `Examples/PolicyChoiceClients.lean` demonstrates selection behavior, not speedup.

## Evidence and validation limits

I read only the supplied brief and pinned archive, including required architectural/domain/skill guidance, relevant ADRs, declarations, and consumers cited above. I did not consult live issues, the original checkout, history, other reports, or previous session handoffs. I had no prior runtime-design involvement supplied in my context and observed no accidental exposure to withheld runtime preferences. Required archived direction documents contain general project preferences, which I treated as constraints rather than a runtime verdict.

This report uses source inspection and explicitly labeled paper schedules. I ran no Lean elaboration, build, audit, benchmark, or executable experiment; no dependency or build cache was changed. Existing theorems are identified by their inspected statements and proofs, not independently revalidated here. No external-source claims are needed for these findings. Missing evidence includes actual proposed session/phase interfaces, a chosen bounded callback protocol, an emitted artifact, end-to-end adapter tests, and matched author/performance measurements.

Tooling used: shell read/search commands and `apply_patch` for this report. I am the independent implementation-and-use subagent; no nested agents were used. The session identifies the agent family as GPT-6/Codex but does not expose a reliable exact model version or sampling configuration to me. Independent report writing does not establish model diversity or proof checking.

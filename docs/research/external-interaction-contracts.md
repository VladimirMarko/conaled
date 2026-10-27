# External interaction contracts: first research milestone

Research for [#194](https://github.com/VladimirMarko/conaled/issues/194), within
[#196](https://github.com/VladimirMarko/conaled/issues/196). Assessed against
repository revision `a24253f0dacb6721bdbfb25acca0fd1e62aabcf3` on 2026-10-27.
This note proposes discriminating models and a staged investigation. Its worked
models are mathematical sketches, not kernel-checked Lean results. It does not
complete #194, select an ADR, or authorize a production measurement port.

The next useful step is to formalize observations and conditional refinement
for the two consumers below, then compare author interfaces against those same
obligations. Relational traces, event handlers, and ownership/recovery logics
offer different benefits. None of the inspected facilities supplies their
combination, or a proof about the operating system, merely by being imported.

## Existing capabilities and concrete gaps

The local source assessment follows the [architectural standard](../agents/architectural-quality.md),
[language direction](../language-direction.md), and ADRs
[0001](../adr/0001-modules-and-proof-dependencies.md) and
[0010](../adr/0010-composition-and-proof-audit.md).
The relation and timing comparisons also follow ADRs
[0002](../adr/0002-relations-and-synchronization.md) and
[0008](../adr/0008-timing.md).
The following paths refer to the pinned repository revision above; later edits
require reassessment.

| Existing construction | What can transfer | What must still be supplied |
|---|---|---|
| Exact/relational squares and [relational composition](../../SquareKit/RelationalCategory.lean) | Separate operations, observations, preservation, and composition of established contracts | The existing function interfaces do not themselves describe interference or divergence. A chosen behavior carrier and compatible observation relations need their own laws. |
| [Retained-state composition](../../Applications/Incremental/Stateful.lean), #113 | Arbitrary state representations related to a mathematical specification; composition at specified sequential boundaries | An external step may be interrupted or observed incompletely. The pure total update interface does not establish crash recovery or concurrent access. |
| [Resource workloads](../../Applications/Resources/Workload.lean) | Explicit additive accounting and reweighting | Costs of failed attempts, cleanup and persistent effects; connection between symbolic cost, runtime measurements and deadlines. |
| [Evaluation](../../Applications/Progress/Evaluation.lean), [streams](../../Applications/Progress/Streams.lean), [processors](../../Applications/Progress/Processors.lean) | Distinguish bounded search from existence of a finite evaluation; productivity and finite demand/delivery obligations | Evaluation's deterministic atomic machine and the delivery hypotheses do not provide an OS scheduler, cancellation protocol or arbitrary environment model. |
| [FRP traces](../../Applications/FRP/Trace.lean) and [demand](../../Applications/FRP/Demand.lean) | Keep source honesty, availability and processing fairness separate | A filesystem or process adapter must establish its own corresponding assumptions; no automatic transfer of FRP progress. |
| [Digital timing](../../Applications/Timing/Digital.lean), [adder hazard](../../Applications/Timing/Adders.lean) | Separate value, signal and timing observations; value agreement alone need not imply timed agreement | No general clock, failure-detector, storage or distributed recovery model follows. |

Two existing tools make the missing obligations concrete:

- [The checker benchmark](../../scripts/benchmark-order-certificate.py) launches
  a subprocess with timeout and CPU-limit settings, writes its log, updates a
  results record, then checks the exit status. Timeout/spawn exceptions and
  recording failures are not represented by the same completed-result record.
  Import discovery precedes later source hashing and copying. Those steps do
  not constitute an atomic snapshot of all input files. Recording the manifest
  hash also does not freeze dependency contents or the compiler executable.
- [The fresh checker](../../scripts/check.py) reads source for inventory and
  scanning, then invokes compilation on live paths. Private output directories
  prevent stale artifacts from substituting for fresh results. They do not
  freeze source inputs. The [README](../../README.md#build-and-audit) explicitly
  requires sources and dependencies to remain stable. Concurrent edits therefore
  violate a stated premise; this is not evidence that the existing checker
  promises and fails to provide unconditional snapshot isolation.

These are reasons to investigate contracts, not changes to production tooling
in this milestone. #43 retains verification refinement, #7 source handling,
#6 snapshots, and #195 measurement tooling.

## Primary research and three candidate approaches

The comparison below separates results established in the cited works from
proposed uses here. No proof or library from those projects has been ported or
validated against this repository.

**A. Relational transitions and observable behaviors.** Abate et al.'s
[trace-relating compiler correctness](https://people.mpi-sws.org/~dg/papers/esop20.pdf)
(ESOP 2020, §§1–2) permits different source and target trace spaces connected
by a relation. Existential and universal images characterize transported
properties and source obligations. The observation relation matters: an
arbitrary relation need not preserve the original property unchanged. This
supports comparing a benchmark's abstract evidence record with process and
filesystem events without requiring equal event alphabets.

Proposed use: specify admissible finite prefixes and maximal behaviors,
including divergence and interrupted observation, by predicates. Interpret
implementations into those behaviors. Keep environment assumptions explicit.
No finite state space, executable choice, decidable relation or total successful
completion is required of the mathematical specification.

**B. Event trees and compositional handlers.** Xia et al.'s
[Interaction Trees](https://arxiv.org/pdf/1906.00046v2)
(POPL 2020, §§2–4, especially Figs. 9–11) separates events from their handlers,
supports potentially diverging computations, and establishes interpretation
laws for return and sequencing. It offers an executable program interface and
equational reasoning. Its paper leaves further nondeterminism/concurrency
reasoning to subsequent work. [Choice Trees](https://popl23.sigplan.org/details/POPL-2023-popl-research-papers/61/Choice-Trees-Representing-Nondeterministic-Recursive-and-Impure-Programs-in-Coq)
(POPL 2023, authors' abstract) explicitly adds internal nondeterministic
branching. An external reply parameter and internal nondeterministic choice
should not be identified without checking their semantics.

Proposed use: write a bounded orchestration program once, interpret its events
into a deterministic fixture and a target adapter, and relate both to A.
An event named `publish` does not make publication atomic; its handler must
justify that abstraction. Effects taking place before a missing reply require
a semantics of the handler's intermediate behavior, not only return values.

**C. Ownership, interference and recovery contracts.** Hayes, Jones and Colvin's
[Refining rely-guarantee thinking](https://eprints.ncl.ac.uk/186500)
(2012 report, §§3–4 and operational semantics §7) records allowed environment
steps separately from component guarantees. It explains why sequential
refinement rules need interference conditions. [Iris](https://swasey.github.io/papers/iris/iris-popl15.pdf)
(POPL 2015, §§1–3) uses resource ownership and invariants for concurrent
protocols; an invariant cannot simply be opened across arbitrary non-atomic
code. Neither result licenses exclusive ownership of a file merely because
the program possesses its pathname.

[FSCQ's Crash Hoare Logic](https://adam.chlipala.net/papers/FscqSOSP15/FscqSOSP15.pdf)
(SOSP 2015, §§3–4) adds crash and recovery conditions, including recovery that
can itself crash. Its disk model includes asynchronous writes and explicit
assumptions such as atomic sector writes; its extracted executable retains
trusted components (§6). Proposed use here: specify publication and cleanup
with separate normal, interrupted and recovered postconditions, and prove
which resources remain owned. This is a candidate proof discipline, not a
proposal to port Iris or FSCQ in full.

| Criterion | A: relational behaviors | B: events and handlers | C: ownership and recovery contracts |
|---|---|---|---|
| Benchmark consumer | States exactly which evidence each execution permits, including no reply | Convenient orchestration and deterministic fault injection | Describes ownership of child handles, output destinations and cleanup duties |
| Mutable-input consumer | Can distinguish a captured byte collection from a coherent source revision | Separates discovery/read/compile/publish requests; handlers expose capture policy | States which paths/objects may change, and what a stable snapshot resource permits |
| Composition | Relations compose, but contextual refinement requires compatible environments and observations | Handler interpretation laws help sequential reuse; concurrency and interrupted handlers need more semantics | Framing requires resource separation and interference stability; recovery requires each interruption state to enter a valid recovery precondition |
| Caller effort | Small mathematical starting point; raw trace arguments can become repetitive | Removes control-flow repetition if handler laws are reusable; event syntax can become bookkeeping | Local specifications can hide internals; permission and invariant setup may be expensive |
| Local implementation obligations | Every concrete behavior must have an allowed abstract account | Each handler and handler composition must preserve the selected observations | Each primitive must establish its normal/crash guarantees and maintain shared protocols |
| Main unresolved cost | A useful proof interface for open systems | Lean representation of infinite behavior and nondeterminism without forcing specifications into executable syntax | How little ownership/recovery machinery suffices for these consumers |

A and B are not competing mathematical and executable versions of the same
thing automatically. C can supply compositional proof rules for either.
Compare them on the same examples before choosing shared infrastructure.

## Observations before representation

The following are proposed models, not claims about all platforms. They use
small state sets to discriminate designs. Their eventual general interfaces
must allow richer state spaces and behavior predicates.

### Benchmark subprocess and evidence capture

Distinguish these observations: an attempt was requested; a child was observed
to start; output bytes were observed; an exit was observed; cancellation was
requested; cleanup was confirmed or unresolved; a record became visible; and
durability was acknowledged under a stated storage contract. No single `ok`
bit records all of them. Partial stdout and stderr are separate sequences;
their local order does not supply an unobserved global interleaving.

An example abstract result contains attempt identity, input/tool provenance,
observed output prefixes, termination knowledge, and publication knowledge.
Knowledge is a set of world states consistent with observations, not a guessed
world state. An unresolved outcome permits several worlds; it is not a claim
that all of them happened. This epistemic interpretation is a proposal for
the example, not a general epistemic logic already present in the library.

For example, two histories with retained observations `[request, timeout]`
can differ: one never created a child, while another created it and appended
a marker before observation was lost. If both are admissible, the retained
observations justify neither `marker absent` nor `marker present`. An adapter
that returns `not executed` for both cannot refine that knowledge contract.

| Example transition | World change | What the orchestrator can conclude |
|---|---|---|
| Spawn rejected before creation, with a trustworthy reply | No child created | This attempt did not start |
| Child starts; orchestrator loses observation before recording acknowledgement | Child exists and may execute | Creation is unresolved from retained evidence |
| Child writes a prefix then exits or is killed | Prefix may remain; external effects may already exist | A later nonzero exit does not imply no effects |
| Timeout is noticed; termination requested | Request may reach the child or process group | Neither exit nor complete cleanup follows from request alone |
| Record publication takes effect; acknowledgement is lost | Record exists | Publication is unresolved until a suitable read/recovery protocol resolves it |
| Cleanup fails after a successful computation | Result may remain valid; resources remain | Record computation and cleanup outcomes separately |

Safety proposal: every claimed observation is justified by the attempt's
evidence, and no result for one input identity is labeled as a result for
another. A stronger completed-result contract additionally requires observed
termination and the requested output completeness. Progress requires bounded
or fair scheduling, service availability, pipe draining and a cleanup policy;
it cannot follow from safety or a requested timeout alone.

**Retry counterexample.** In a hypothetical effectful benchmark, the child
appends a marker, exits, and its acknowledgement is lost. Retrying the attempt
appends twice. Idempotent record replacement does not make the child execution
idempotent. Safe retry requires a weaker goal that tolerates duplicates, an
effect-idempotence proof, or a deduplication protocol with adequate persistence
and agreement between the effect and its identity. A fresh identifier per
retry does not provide deduplication of the original logical operation.

### Fresh build or snapshot over mutable files

Separate path names, object identities, captured bytes, dependency membership,
and the bytes actually supplied to compilation. A content hash can identify
captured bytes subject to its equality/collision assumptions. It cannot by
itself prove that they were the bytes later compiled, that dependencies were
stable, or that all captured files coexisted at one time.

Consider this hypothetical two-file history:

| Step | External state | Observation |
|---|---|---|
| Initial | `(A0, B0)` | Capture `A0` |
| Permitted actor updates A | `(A1, B0)` | None |
| Same actor updates B | `(A1, B1)` | Capture `B1` |
| Build captured collection | Collection `(A0, B1)` | Each file has a truthful individual digest |

The captured pair never existed as the external directory state. Per-file
integrity therefore does not establish a coherent revision. A separate
counterexample reads/scans `A0`, then another actor replaces it with `A1`, then
the compiler opens the live path. The scanner and compiler have used different
bytes. An open handle can protect against some pathname replacement effects;
it does not establish immutable contents or a multi-file snapshot by itself.

Three valid specification choices have different implementations:

1. **Exact captured collection:** compile the same captured bytes used for
   discovery and evidence, and report their identities. No claim that the
   collection was a simultaneous external state.
2. **Coherent revision:** acquire an immutable revision, transactional snapshot,
   or equivalent protocol covering the declared input/dependency scope. State
   what the snapshot excludes and what makes its objects available.
3. **Stable environment:** assume no relevant mutation throughout the operation.
   This resembles the current checker's documented premise. Detection of some
   mutations can improve diagnostics without proving that every violation is
   detected; equal before/after checks can miss intervening changes.

A refinement between these contracts needs evidence of the extra property.
They are not interchangeable labels. Compiling immutable copies can satisfy
choice 1 while failing choice 2. The same publication/unknown-acknowledgement
problem arises when recording a build receipt or creating a snapshot reference.

## Laws to test and assumptions they expose

These are proposed obligations and counterexamples for the next checked models.

For a precise safety-only composition experiment, let `C` and `D` be relations
on states, `R*` the reflexive-transitive closure of permitted environment steps,
and `{P} C {Q}` mean every `C` result from a `P` state satisfies `Q`.
From `{P} C {Q}`, `{Q} D {S}`, and stability
`Q(x) ∧ R*(x,y) → Q(y)`, infer `{P} (C ; R* ; D) {S}`.
Here `;` is existential relational composition. The intermediate witness
after `C` satisfies `Q`, stability transports it across `R*`, and `D` supplies
`S`. This sketch proves no existence of a result and thus no termination.
The write/read example below falsifies the rule with stability omitted.
Crashes inside `C` or `D` need additional transitions or behavior semantics;
this endpoint rule does not cover them merely by allowing boundary interference.

- **Sequential composition:** an intermediate assertion must survive the
  permitted environment steps before its consumer uses it, or the interface
  must transfer a resource that protects it. `write(p,x); read(p)` need not
  return `x` when an authorized actor may replace or delete `p` between calls.
- **Refinement:** for each target behavior under an admissible target
  environment, require a permitted source behavior related by the selected
  observation relation. Record how environment assumptions are translated.
  If that relation erases failed publication, refinement cannot establish
  durable evidence. Progress needs maximal/infinite behaviors or an additional
  progress judgment; finite successful traces alone omit a hanging execution.
- **Framing:** operations on supposedly disjoint paths may still alias the
  same object or contend for shared capacity. Prove the relevant separation
  and stability assumptions; disjoint strings are insufficient.
- **Recovery composition:** each reachable interrupted state must satisfy a
  recovery precondition, including interruption during recovery. Recovering a
  log and recovering a result file independently need not preserve their
  cross-file consistency when they describe different attempts.
- **Cancellation:** a cancellation request is an event, not rollback. A
  compensating action is another fallible action. Catching an exception or
  arranging a finalizer does not prove cleanup across process death or loss
  of scheduling.
- **Accounting:** include attempted work and cleanup in the chosen resource
  observations. A bound on one attempt does not bound arbitrarily many retries;
  sharing an exhaustion-prone storage device can invalidate independently
  assumed resource budgets.

## Failure and assumption matrix

This list covers selected combinations relevant to the consumers. It is not an
exhaustive error enumeration or a promise to detect every model violation.

| Situation | Required distinction or assumption | Proposed evidence/check |
|---|---|---|
| Missing/denied path, path replacement, permitted writes | Identity and permission observation at one point vs authority/stability over time | Inject deletion/replacement between scan and use; compare live-path and captured-input policies |
| Short write, exhausted space, interrupted publication | Bytes accepted vs complete record vs durable record | Fail after each publication phase; reject a truncated record as completed evidence |
| Process creation failure, signal exit, missing acknowledgement | Known non-creation vs unknown execution; observed exit vs effect history | Scripted environment allows both unknown worlds; never infer rollback |
| Partial output, full pipe, inherited output descriptors | Observed prefix vs complete output; child exit vs end-of-stream | Separate finite-output, blocked-output and lingering-writer fixtures |
| Timeout or cancellation racing with completion | Deadline observation vs child exit and cleanup | Exercise both event orders; preserve both execution and cleanup knowledge |
| Clock behavior and scheduler delay | Monotonic readings, clock domain, timer delivery, scheduling bounds | State hypotheses for elapsed measurements and deadlines; test delayed delivery separately |
| Cleanup failure or crash during cleanup | Normal finalization vs crash recovery; ownership still outstanding | Retain unresolved cleanup in result; recovery can be interrupted again |
| Compiler/dependency mutation | Source provenance alone vs full declared execution inputs | Bind receipt to captured scope and record trusted inputs outside it |
| Runtime, FFI, storage or checker violates model | Model-relative theorem vs physical execution evidence | Explicit adapter trust ledger; do not interpret an unexpected outcome as theorem coverage |

Linux's documented [`write`](https://man7.org/linux/man-pages/man2/write.2.html)
permits short writes, including interruption after partial transfer.
[`fsync`](https://man7.org/linux/man-pages/man2/fsync.2.html) distinguishes file
synchronization from synchronization of its containing directory. These are
target-specific constraints on adapters, not universal laws of files. They
also do not certify a particular storage device's behavior.

Python's [`subprocess` documentation](https://docs.python.org/3/library/subprocess.html)
distinguishes timeout handling, pipe deadlock risks and output buffering;
`run`'s timeout does not bound uninterruptible initial process creation. A
supervisor policy must specify process scope and output/resource limits.
Tests against the existing Python consumer do not prove a future Lean adapter
or transfer those API assumptions to another target.

## Pinned Lean facilities and the execution boundary

The installed Lean is 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Inspected sources include
[`Init/System/IO.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/System/IO.lean),
[`Std/Sync/CancellationToken.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Sync/CancellationToken.lean),
[`Std/Async/Timer.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Async/Timer.lean), and
[`Std/Async/Process.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Async/Process.lean).

`BaseIO` and `EIO` use state-thread representations over `IO.RealWorld`, whose
underlying type is opaque; `IO` selects `IO.Error`. Filesystem and process
primitives cross `extern` boundaries. `IO.Process.output` reads stdout in a
task, stderr in the caller, then waits; the helper has no timeout argument.
`Child.kill` documents SIGTERM or its platform analogue, with process-group
scope when `setsid` was used. Requesting termination is not evidence of exit.

Std provides cancellation signaling, asynchronous timers, and process/resource
queries. These are useful adapter ingredients. Their existence does not supply
the environmental, durability and observation contracts above. A cancellation
token represents notification; a consumer must still implement its response.
`Std.Async.Sleep.stop` explicitly leaves pending waits incomplete, which can
remain blocked without further intervention. Even timer cancellation therefore
does not imply completion of a task waiting on it.
This inspection does not establish absence of every useful facility elsewhere
in Lean, Std or Lake, and no complete Lake/runtime audit was performed.

There is also reusable proof infrastructure:
[`Std.Do.WP.Basic`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Do/WP/Basic.lean)
supplies predicate-transformer interpretations for state and exception monads.
Its `EStateM` instance has both success and error postconditions with resulting
state. Thus a pure model can retain an effect even when it returns an error.
[`WPSound`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Do/WP/Sound.lean)
connects that reasoning to `Internal.Ensures` and possible returns; it does not
prove termination or external interference properties of arbitrary IO actions.
Reuse this infrastructure in the bounded state/error experiment before inventing
a replacement Hoare-logic interface. Transformer order matters: an error result
that discards the state cannot report the partial state retained by `EStateM`.
Neither representation alone models an unobserved effect outside that state.

Keep three obligations separate: proofs about mathematical behaviors; proofs
relating a program/adapter model to those behaviors; and evidence/assumptions
connecting that model to runtime, OS, filesystem, device and executed checker.
A theorem can quantify over an adapter contract without introducing an axiom
asserting that the actual OS satisfies it. Later targets may supply different
representations and proofs. Neither `IO.RealWorld` nor Linux process identifiers
should become mandatory specification fields.

## Recommended next experiments and acceptance criteria

**1. Check the observation contracts before selecting an effect encoding.**
Under #194, build small relational Lean models for both consumers. Include
partial effects, permitted interference, unresolved acknowledgement, failure
during recovery and a nonterminating/never-observed execution. Prove a bounded
sequential composition rule with explicit stability assumptions and exhibit
the failed stronger retry/snapshot laws above. Define the source/target
observation relation and show a concrete lost guarantee when it hides too much.
Acceptance requires checked connected examples, statement review, fresh source
build and axiom audit. Finite fixtures may test the models but cannot replace
the unbounded or relational specification.

**2. Compare two author interfaces over those contracts.** Implement a minimal
event/handler presentation and a direct transition-contract presentation for
the same orchestration examples. Add only the ownership/recovery rules needed
by the examples. Compare caller-written proof obligations, repeated structural
bookkeeping, and obligations discharged once by interpretation. Require a
counterexample-preserving comparison: neither interface may hide unknown
effects or assume an atomic snapshot merely to simplify its proof. Stop or
revise an interface if it moves all obligations into caller-supplied records
without reducing repeated work. This experiment does not require a universal
event type, a world-state record, or porting a complete foreign proof library.

**3. Validate a bounded adapter separately.** After the reviewed models, select
one target and implement an isolated fixture adapter with deterministic
injection at the specified boundaries. Test partial output, ambiguous
publication, concurrent mutation, timeout/completion races and cleanup failure.
Record exact tool/runtime/platform revisions and assumptions. Bound fixture
resources and state which descendant processes and output streams are covered.
Do not modify production verification or measurement tools for this experiment.

#195's Lean migration remains deferred until there is a reviewed contract for
its selected scope, connected checked models, an adapter with recorded trust
assumptions, and empirical evidence for that adapter's failure handling. A
decision to proceed may explicitly exclude crash durability or adversarial
actors if the consumer does not promise them. Those exclusions must remain
visible in its result semantics. Full completion of #196 is not a prerequisite.

## Questions retained by #196

Strategic environments need capability bounds and perhaps goals/incentives;
nondeterministic environment steps alone do not establish incentive-dependent
claims. Probabilistic guarantees need distributions and dependence assumptions;
retrying on correlated failures cannot assume independent trials. Distribution
requires explicit communication, knowledge and timing assumptions. This note's
local interleavings and timeout examples do not settle distributed progress.

Recovery may preserve safety while sacrificing availability, or restore a
weaker service; a unique fault-free baseline is not assumed. Investigation
should test which assumption changes support useful transport maps and which
change the observable contract itself. Fallible compilers/verifiers, evidence
corruption and common-cause failure remain broader research questions. Modeling
a faulty checker does not eliminate the metatheory and execution assumptions
used to trust its replacement or certificate checker.

Remaining local unknowns include the smallest useful ownership interface,
Lean support costs for infinite effect behaviors, sufficient observation of
interrupted handlers, snapshot scope across external dependencies, and the
precise target contracts needed for durable evidence. The bounded experiments
above are intended to resolve these uncertainties before an architectural
commitment.

## Evidence limits

This milestone inspected source and primary publications and constructed
paper models. No Lean files or production scripts changed, no OS fault
experiment or full build ran, and no executable refinement was established.
The ITree source used is arXiv version 2; the rely-guarantee source is the 2012
report rather than the later linked report. The cited Linux and Python pages
were accessed on 2026-10-27 and describe interfaces, not a measured runtime.
Direct access to several Open Group function pages failed; their contents
are not used to assert target behavior. The future adapter experiment must
pin the implementation and platform it actually exercises.

# Readiness to build repository helpers with Conaled

## Reassessment on 2026-10-29

Rechecked against master
[`7f88d3d05880054f437415ec186e87545a644ea1`](https://github.com/VladimirMarko/conaled/tree/7f88d3d05880054f437415ec186e87545a644ea1)
and the current issue records. The ownership map and production-migration
conditions below remain useful, but the proposed first pilot has been completed.
The original assessment is retained below as dated context, not a current list
of missing capabilities.

[#216](https://github.com/VladimirMarko/conaled/issues/216) implemented the
recommended one-attempt pilot and was integrated at `87cf92b`. Its
[report](measurement-attempt-pilot.md) now supplies the controller/adapter
assessment and retained failure evidence. The
[controller](../../Applications/Interaction/Measurement.lean) proves observation
selection, recording refinement and no re-execution within one retained state;
the [experimental adapter](../../experiments/measurement-attempt/README.md)
calls those proved decisions and has public fixtures for success, failures,
uncertainty and captured-input mutation. These were missing at the original
baseline. Do not restart that pilot from this note's earlier recommendation.

The next step remains a bounded common-runner specification under
[#195](https://github.com/VladimirMarko/conaled/issues/195), exercising both the
order-certificate benchmark and #49's numerical-execution consumer. The pilot's
cooperative regular-file output protocol is not generic stdout/stderr handling;
its publication receipt does not establish crash durability, and finite polling
does not establish a wall-clock deadline. It supplies neither shared production
support for both consumers nor an unchanged replacement for their scripts.
Preserve those public behaviors and specify input/dependency identity, output,
process, timing/resource and publication requirements before migration.
The production benchmark is unchanged from the original assessment baseline,
so its missing structured-result paths remain relevant.

Verification also advanced: #223 added routine Lake incremental verification
with a separate fresh mode; #224 bound success records to clean committed
candidates and pinned dependencies. The current
[build and audit instructions](../../README.md#build-and-audit) govern invocation.
These checks detect recorded identity mismatches but still require stable inputs;
they do not implement filesystem capture or prove the absence of transient edits.
The earlier discussion of fresh output directories describes that mode only.

Issues #6, #7, #43, #49, #194, #195 and #196 remain open. Their scopes below
still distinguish snapshot mechanics, Lean-native source handling, verification
proofs, numerical measurement and interaction research. Later reactive pipeline
work and [durability research](compositional-durability.md) do not supply the
missing production measurement adapter. The pilot supports progressing to a
scoped migration specification without waiting for the wider programme.

This reassessment inspected committed sources and issue records. It did not
rerun the pilot or renew its build, runtime-test or proof-audit results; those
remain evidence for the candidates recorded in #216.

## Original assessment on 2026-10-28

Assessment on 2026-10-28 against commit
[`624916f8b37bd46f2f1105b774269c703dd4f46f`](https://github.com/VladimirMarko/conaled/tree/624916f8b37bd46f2f1105b774269c703dd4f46f).
Relative source links refer to files inspected at that baseline. Issue bodies
and comments were consulted on that date; they can change independently.

**There is enough mathematical groundwork to start a bounded helper pilot
using the library. There is not yet evidence for a production Lean migration
of the measurement tooling.** The remaining immediate work is to connect a
selected helper's concrete observations and executable adapter to the existing
contracts. Completing the broad interaction research programme is unnecessary.
This assessment follows the separation between checked mathematical contracts
and runtime guarantees in [README](../../README.md#proof-and-execution-boundary)
and the scoped migration gate already specified in
[#195](https://github.com/VladimirMarko/conaled/issues/195).

## Which issue owns the consolidation

[#195, Develop reusable experimental measurement support and scope a deferred
Lean migration](https://github.com/VladimirMarko/conaled/issues/195), is the
measurement-support issue. Its first phase extracts demonstrated common needs
from the order-certificate benchmark and
[#49's numerical-execution feasibility checkpoint](https://github.com/VladimirMarko/conaled/issues/49).
Its second phase prefers Lean once scoped contracts and adapter evidence exist.
Phase 1 can proceed now and permits a small Python refactor. Phase 2 remains
conditional; a direct translation of subprocess calls would not satisfy it.

[#7](https://github.com/VladimirMarko/conaled/issues/7) is the related verification
issue: replace handwritten Python understanding of Lean source and imports with
Lean/Lake facilities while preserving coverage, fresh compilation and audit.
It permits retained Python orchestration and excludes formal verification of
the tooling itself. That proof work belongs to
[#43](https://github.com/VladimirMarko/conaled/issues/43).
[#6](https://github.com/VladimirMarko/conaled/issues/6) owns Git snapshot helpers.
[#194](https://github.com/VladimirMarko/conaled/issues/194) supplies the concrete
external-interaction study; [#196](https://github.com/VladimirMarko/conaled/issues/196)
owns the wider research synthesis. These are cooperating scopes, not one port.
The [workstream guidance](../../README.md#workstreams-and-shared-components)
asks consumers to link their scope owners without duplicating acceptance work.

## Reusable code already present

| Capability | Inspected declarations | What remains the caller's obligation |
|---|---|---|
| Safety through interference | [`Interaction.Safe`, `Stable`, `safe_interference_seq`](../../SquareKit/InteractionContracts.lean) | State the permitted environment relation and prove intermediate assertions stable. This endpoint theorem does not establish termination or automatically account for interruption inside an operation. |
| Observation refinement | [`Refines`, `Refines.requirement`, `Refines.trans`](../../SquareKit/InteractionContracts.lean) | Relate actual target behaviors to permitted source behaviors and preserve the property in the chosen observation. Refinement does not construct an OS adapter. |
| Predicate transport | [`RelationTransport.image`, `requirement`, `image_requirement`, composition and graph laws](../../SquareKit/RelationTransport.lean) | Distinguish a possible observation from a guarantee about every compatible world. Supply a reachable-world witness separately to exclude empty-fiber vacuity. |
| Primitive-to-script reasoning | [`Events.interpret_simulation`, `interpret_safe`, `interpret_invariant`](../../SquareKit/InteractionEvents.lean) | Prove primitive simulation and domain invariants. Finite lists cannot express reply-dependent continuations or interruption inside a handler. |
| Captured-input contract | [`Snapshot.compile_sealed`, `captured_stable`, `never_coexisted`](../../Applications/Interaction/Snapshot.lean) | Enforce the separation between captured inputs and mutable live files. `CompileCaptured` assumes the compiled receipt corresponds to the captured collection; it is not a proof of filesystem capture or compiler execution. |
| Partial effects and unknown observations | [`Evidence.no_effect_decision`, `retry_duplicates`, `interrupted_run`](../../Applications/Interaction/Evidence.lean) and [`Obligation.tryAccept_iff`, `delayed_attempt`](../../Applications/Interaction/Obligation.lean) | Supply truthful evidence, authority and fencing where promised. An acknowledgment can be absent after an effect; a local lease count does not fence an outstanding attempt. |
| Resource and progress models | [`Resources.Measured`](../../Applications/Resources/Measured.lean), [`Workload`](../../Applications/Resources/Workload.lean), [`Probability.Execution`](../../Applications/Probability/Execution.lean), [`HittingTimes`](../../Applications/Probability/HittingTimes.lean) | Connect modeled operations to the chosen cost and execution model. Transition deadlines are not wall-clock deadlines; probability laws need justified environmental distributions. |

The connected [interaction examples](../../Examples/ExternalInteraction.lean),
[interface comparison](../../Examples/InteractionInterfaces.lean), and
[predicate-transport examples](../../Examples/InteractionTransport.lean) exercise
these public results. In particular, `script_is_not_authority` refutes treating
the current event interpreter as protocol enforcement. Reuse the relational
contracts immediately; do not require every helper to use that experimental
script surface. The [interface report](external-interaction-interfaces.md)
records both the removed sequence induction and the remaining domain proofs.

The [probability/recovery comparison](probability-and-recovery-contracts.md)
and [predicate-transport report](optimization-transport-and-recovery.md) are
present in the inspected commit, despite older issue updates describing some
of that work as uncommitted. They propose further recovery experiments; their
proposals are not evidence of implemented adapters. This assessment takes no
credit for changes in other agents' worktrees or after the pinned baseline.

## What the executable consumers still need

[`benchmark-order-certificate.py`](../../scripts/benchmark-order-certificate.py)
records toolchain/platform information, captured-source hashes, process output,
return codes and elapsed time. Its `run` writes a result after `subprocess.run`
returns and after the log write succeeds. There is no local exception path
recording a timeout, failed process creation, or failed log/result write.
An unsuccessful attempt can therefore lack its structured result. Source
closure discovery and byte capture happen at separate reads; dependency caches
remain external inputs. These are concrete requirements for #195, not reasons
to declare all existing benchmark evidence invalid.

[`check.py`](../../scripts/check.py) discovers imports and scans policy before
later compiling the live source paths. Its private fresh-output directory
prevents reuse of project artifacts, but does not freeze source or dependency
inputs. The [documented check](../../README.md#build-and-audit) explicitly requires
them to remain stable. A captured-input improvement must choose whether it
promises the exact collection consumed, a coherent revision, or stability of
live inputs. The checked `never_coexisted` case shows why those differ.

Lean already supplies executable building blocks. The pinned Lean 4.35.0
[`Init/System/IO.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/System/IO.lean)
was inspected in the installed toolchain: filesystem operations, process
creation, waiting and termination cross `extern` boundaries. `Process.output`
reads output streams and waits, with no timeout parameter. Those primitives
are available for an adapter, but their types supply no refinement proof for
our captured-input, publication or cleanup contract. The previous
[pinned-facility assessment](external-interaction-contracts.md#pinned-lean-facilities-and-the-execution-boundary)
compares further Std facilities. No runtime or OS experiment was performed for
this note.

## Bounded next work and sufficient migration gates

Start with one measurement attempt and its evidence publication under #194,
then exercise its reusable support through both #195 consumers. This is a
recommendation for a pilot, not authorization in this assessment to port
production scripts. Keep the independent specification separate from the
adapter's observed behavior.

1. **Fix the supported observations.** Specify command and input identity,
   output prefixes, observed exit, timeout, unresolved child/cleanup status,
   and complete versus incomplete evidence publication. Decide which resources,
   descendants and dependencies are covered. State exclusions such as crash
   durability explicitly. A single attempt with no automatic re-execution is
   a useful initial scope: unresolved effects remain unresolved.
2. **Connect a bounded executable core.** Reuse `Safe`, `Stable`, `Refines`
   and predicate transport for the selected orchestration model. Prove the
   actual controller/recording decisions satisfy an independently stated
   result contract, including unsuccessful outcomes and reachable success.
   If reply-dependent control or authority ordering is needed, add only that
   demonstrated fragment. A model that assumes the entire desired adapter
   behavior in one premise is not the missing connection.
3. **Exercise an isolated target adapter.** Pin runtime/platform and inputs;
   document each trusted primitive and abstraction assumption. Inject failed
   spawn, partial output, timeout/completion races, publication failure and
   cleanup failure. Exercise permitted input mutation in the capture consumer.
   Check that unknown or incomplete states never become successful records.
   Tests constrain the real adapter but do not prove all OS behaviors.
4. **Approve a scoped migration specification.** Require the controller's
   refinement link, adapter evidence, public-invocation compatibility, records
   for successful and failed attempts, both real measurement consumers, and
   reproducible fixtures. New Lean claims need checked applications, statement
   review, fresh build and axiom audit; the deliverable also needs independent
   Standards/Spec review. Record remaining trust assumptions with the result.

These gates are sufficient to consider #195's selected migration scope without
closing #196. Resource-recovery research is a prerequisite only for claims
about retry cost, eventual acknowledgment or probabilistic bounds. If a helper
only returns a bounded attempt's unresolved result, those stronger claims need
not delay it. The [current recovery comparison](probability-and-recovery-contracts.md)
already distinguishes a capped observation policy from re-executing the effect.

| Owner | Work that can proceed | Additional gate for stronger claims |
|---|---|---|
| #6 | Disposable-repository Git tests and an implementation preserving live index/worktree content | Connect capture identity, scope and final verification to the snapshot contract before claiming a library-backed verified helper. A coherent Git tree does not alone establish coherent capture of a concurrently edited checkout. |
| #7 | Lean-native source/import handling and public-command regression tests | Preserve source policy, full coverage and fresh compilation. No need to wait for universal fault semantics; explicitly retain the supported stability assumptions. |
| #43 | Pure root-selection, audit-acceptance and dependency-scheduling refinement proofs | Connect those algorithms to the executed tooling and state metadata, source/artifact, process and toolchain assumptions. External-interaction laws do not prove these algorithm-specific results. |
| #195 | Shared measurement requirements and demonstrated reuse in both consumers | The scoped contract, connected executable core and tested adapter above before production Lean migration. |

The immediate gap is adapter engineering with precise contracts and a small
amount of consumer-specific formalization. More general research remains useful
for the broader library, but it should be driven by a failed law or missing
obligation in this pilot rather than made a blanket prerequisite for helpers.

## Assessment limits

This note inspects committed code, current issue scope and installed pinned
Lean sources. It adds no formal claims, production code, benchmarks or new
build result. Existing proof and review reports remain attributable to their
own candidates; source inspection here does not revalidate those builds. The
readiness judgment is conditional on the stated helper scope and must be
revisited if retry, crash recovery, adversarial interference or stronger runtime
bounds become part of its promised behavior.

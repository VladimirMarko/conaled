# WebAssembly capabilities and FRP runtime options

Research checked 2026-11-16. External statuses below describe the consulted live sources, not the repository's pinned engine. The composition principle below records the owner clarification on 2026-11-16. Implementation experiments remain proposals unless an existing issue explicitly owns them.

## Existing research and current target

The existing `docs/research/wasm-standard-subset.md`, `wasm-binary.md`, `wasm-artifacts.md`, and `wasm-word-lowering.md` already document the selected semantics, serialization, artifact/host boundary, and word representations. The [backend design challenge](wasm-backend-design-challenge/synthesis.md) also compares proof and artifact boundaries. A search of these notes and Wasm-related tracker issues found no existing general survey of versions and capability discovery; this report fills that gap.

The repository's semantic target is a selected fragment of Core 2.0 at spec revision `05ca4182176763112561ae20153975c12bd689e4`. Its emitted language uses i32 constants, local get/set, eqz, and/or/xor, and function signatures with multiple results. Modules have one function exported as `run`, with no imports, memory, tables, globals, or start function. The multi-result ABI is the relevant post-MVP feature; targeting Core 2 does not mean the compiler emits all Core 2 facilities. The artifact note records Node 24.21.0 / V8 13.6.233.17-node.53 under the pinned flake. It also states the conditional runtime theorem and canonical input/output admission boundary. Local sources: [selected semantics](wasm-standard-subset.md), [artifacts](wasm-artifacts.md), [binary correspondence](wasm-binary.md), and [word-lowering comparison](wasm-word-lowering.md).

The current host compiles the actual bytes in a worker, then checks its selected
syntax, ABI, export and descriptor binding. It has no feature catalog, negotiated
fallback or multi-version artifact chooser. `probeEngine` is a bare execution
diagnostic, not a feature enumerator. Node worker threads isolate invocations;
the generated modules do not use Wasm threads or shared memory. Each invocation
creates a worker and module instance, while `createStateful` retains explicit
state in the parent and commits only after complete successful output admission.
These facts follow from [the host](../../scripts/wasm-host.mjs) and
[worker](../../scripts/wasm-worker.mjs). No engine benchmark or new runtime test
was performed for this documentation investigation.

## Requirements belong to composed realizations

A source program requires operations and laws. A composition of backends can
supply them through native instructions, software implementations, representation
changes and host services. Native engine facilities offer alternative ways to
construct that infrastructure. Their presence can change which realization best
meets performance, storage, security or timing objectives; their absence does not
by itself remove a source-language capability. This is the owner's clarified
direction, consistent with the [shared language direction](../language-direction.md#mathematical-targets-and-external-foundations).

For example, closures might use Wasm GC, a software-managed heap in linear
memory, or specialization that eliminates allocation. An asynchronous source
might use an explicit residual-state machine, JSPI, or a continuation facility.
These are possible realization routes, not claims that those lowerings are
implemented. Each route must establish the relevant source observations and
composition laws. Requirements remaining after composition belong in the typed
admission contract. Reject a program with requested guarantees only when the
available compositions cannot discharge them; do not infer rejection from a
missing native opcode alone. Unsupported analysis remains distinct from a
proof that no realization exists.

The library assumes no Church–Turing thesis. Computability equivalence would
not establish equivalent resource usage, deadlines or physical isolation. A
sequential implementation may compute the same result yet miss a deadline met
by a parallel one. Software alone cannot discharge an external persistence or
security premise without an appropriate realization and environmental contract.
Conversely, those premises can be supplied by another component of the composed
realization; they need not be native Wasm functionality. The reasoning is relative
to each named computational model and connection, with no privileged ultimate
backend. Capabilities genuinely unavailable through the selected compositions
remain explicit requirements restricting their admitted frontends.

Thus optional Wasm features are generally optimization and implementation choices
for a fixed semantic capability. They can also determine admission for a
particular resource or environmental guarantee. Keep those two claims separate.

## Four independent meanings of version or capability

1. **Core language release.** Core 2 added multivalue, SIMD, bulk memory, and reference types. Core 3.0 was released September 17, 2025 and includes memory64, multiple memories, GC, typed function references, tail calls, exception handling, and relaxed SIMD. [Official release announcement](https://webassembly.org/news/2025-09-17-wasm-3.0/).
2. **Binary format version.** Core modules still use version `1` in their eight-byte preamble. Extensions deliberately preserve that version. The header cannot tell a loader which optional instructions or types a module needs. [Core binary module grammar](https://webassembly.github.io/spec/core/binary/modules.html#modules).
3. **Engine support and configuration.** Standardization, implementation, default enablement, and the exact deployed build are separate facts. The official feature table tracks engines; native embedders such as Wasmtime expose feature configuration, with defaults dependent on build features and target. [Feature table](https://webassembly.org/features/), [Wasmtime Config](https://docs.wasmtime.dev/api/wasmtime/struct.Config.html). The latter is currently development documentation, not evidence about our pinned Node.
4. **Embedding and interface contracts.** Browser APIs, JavaScript embedding, WASI interface releases, Component Model interfaces, permissions, and host resource limits are separate from the Core instruction set. WASI provides APIs granted by the host. [WASI introduction](https://wasi.dev/).

The proposal tracker currently places JS Promise Integration at phase 5, threads at phase 4, stack switching at phase 3, and the Component Model umbrella at phase 1. These phase labels do not imply absence of deployed implementations or released WASI interfaces. [Proposal tracker](https://github.com/WebAssembly/proposals).

## Capability discovery

There is no standard JavaScript call returning a complete supported-feature set or a numeric engine Core version. Test the capabilities actually needed, then compile/instantiate the selected artifact in the actual execution environment. `WebAssembly.validate(bytes)` answers whether that module is accepted by the engine; it does not instantiate imports or run it. A minimal valid module for each feature gives useful diagnostics, while validating the real artifact covers interactions and size constraints. [JavaScript interface namespace](https://webassembly.github.io/spec/js-api/index.html#webassembly-namespace).

The official feature page recommends Google's `wasm-feature-detect`. It uses small feature probes; the threads detector also checks that shared buffers can be posted through a message channel. This illustrates why instruction acceptance alone is insufficient. [Detection library](https://github.com/GoogleChromeLabs/wasm-feature-detect), [threads detector source](https://raw.githubusercontent.com/GoogleChromeLabs/wasm-feature-detect/main/src/detectors/threads/index.js).

For browser shared-memory execution, check the worker environment and shared-buffer availability, including cross-origin isolation deployment requirements. A successful module probe does not grant those host facilities. [Chrome's COOP/COEP guidance](https://web.dev/articles/coop-coep). For native runtimes, make feature enablement and resource policy explicit in the configured engine, then validate/load against it. [Wasmtime configuration](https://docs.wasmtime.dev/api/wasmtime/struct.Config.html).

Suggested artifact contract: keep a small application-owned manifest of required Core features, host interfaces, ABI/representation identity, and resource bounds, tied to artifact bytes. Treat it as producer metadata checked against actual loading, not as an engine negotiation standard. The conventional `target_features` metadata used by toolchains is not a standard capability-negotiation protocol. [Tool conventions](https://github.com/WebAssembly/tool-conventions/blob/main/Linking.md).

## Adaptive artifacts and online optimization

Wasm validates every function in a module, including uncalled functions. An
unsupported instruction cannot be hidden behind an untaken runtime branch.
This follows from the [module validation rules](https://webassembly.github.io/spec/core/valid/modules.html#modules).
A deployable package can instead contain a baseline loader and separate modules
for alternative feature sets. Alternative module bytes may be carried as data
without making their instructions part of the loader's instruction stream; they
must be validated when compiled as modules. This packaging design is an inference
from separate module compilation and loading, not a new standard bundle format.

This constrains the unit of code admission, not the library's ability to optimize
online. Several routes remain conceivable:

- Select precompiled alternatives at startup or repeatedly at valid execution
  boundaries. Alternatives whose instructions are all supported may also coexist
  in one module behind ordinary dispatch.
- Load and compile another module while the current realization remains active,
  then install it after admission and any required continuation transfer.
- Generate or specialize new module bytes online, retaining source-to-artifact
  evidence and checking the resulting artifact before installation.
- When dynamic module compilation is unavailable, use an admitted precompiled
  catalog or an interpreter for a suitable intermediate representation. These
  routes have their own costs and may fail a requested deadline or memory bound.

JavaScript supplies module compilation and instantiation through its embedding
API; a Core Wasm program needs an embedding service to request those operations.
The host's compilation policy and limits are therefore requirements of that
particular online-generation route. The [JavaScript interface](https://webassembly.github.io/spec/js-api/index.html#webassembly-namespace)
specifies these host operations. The current repository host does not implement
this adaptive package, online compiler or live module dispatcher.

A proposed bounded adaptive artifact would bind each alternative's bytes, ABI,
required facilities and preservation evidence to the same source observation
contract. The loader discovers facilities, admits complete regional compositions,
then ranks the admitted candidates. Reuse the existing choice and migration
contracts rather than making engine probes the authority for semantic admission.
For a stateful replacement, prepare and validate the target while the old owner
remains authoritative; commit ownership only with a valid transfer of continuation
and pending work. An unchanged state ABI can simplify transfer but does not
justify discarding pending effects or replaying consumed inputs.

Optimization costs include packaging/download size where relevant, probing,
compilation, cache storage, dispatch, adapters, instrumentation, preparation,
migration pause and simultaneous old/new storage. Compare a fixed baseline
against repeated selection over the same observations. An empirically promising
candidate is not a proof of a global optimum; a best-candidate theorem must name
its catalog and cost model. Resource/security/timing constraints are admission
conditions before ranking. Preparation failures retain the old realization where
its contract remains admissible. These are proposed implementation requirements,
not a claim that the present artifact host provides them.

## Features worth considering for FRP

The table describes native implementation options for composed realizations, not a list of facilities every supporting engine must expose. The use cases and priorities are proposed engineering directions. Language facility descriptions follow the [Core 3 release](https://webassembly.org/news/2025-09-17-wasm-3.0/) and linked proposal sources.

| Facility | Possible use in our runtime | Additional obligation |
| --- | --- | --- |
| Native i32/i64 operations | Packed words and compact transition state; likely a nearer benefit than new extensions | Prove the lowering and codecs; measure complete host-to-host transitions |
| Ordinary SIMD | Audio, animation, vector arithmetic, or batches of independent transitions | Choose array/block ABI; prove lane semantics and benchmark real kernels |
| Relaxed SIMD | Faster approximate numeric kernels | Its permitted implementation-dependent results require an explicit numerical contract |
| Linear memory and bulk operations | Persistent buffers and larger state without huge signatures | Bounds, ownership, initialization, mutation and rollback become part of the host/runtime contract |
| Multiple memories | Separate private state, exchange buffers, or modules being combined | Separation helps only if imports/exports and access permissions enforce it |
| memory64 | Large native-host datasets | No benefit for today's memory-free modules; revise address and ABI contracts when needed |
| GC and typed function references | Dynamic graph nodes, closures, typed callbacks | Source representation and graph semantics remain ours; GC does not promise bounded pause time |
| Tail calls | Recursive functional code or continuation-based scheduling | Useful when those control-flow forms are emitted; current straight-line circuits need none |
| Exception handling | Language exceptions or host adapter failures | Define failure, rollback, cancellation, and effect commitment explicitly |

Threads add shared memory and atomics; host APIs still create/schedule agents. They could evaluate independent graph partitions or numeric kernels. Deterministic event order and glitch freedom remain FRP obligations. A scheduler must decide when a logical instant is complete and which state can commit. Ordinary Wasm threads do not provide arbitrary shared GC objects; shared-everything threads are a separate proposal. [Threads design](https://github.com/WebAssembly/threads/blob/main/proposals/threads/Overview.md), [proposal tracker](https://github.com/WebAssembly/proposals).

JSPI suspends Wasm around asynchronous JavaScript imports and exposes Promise-returning wrappers. It can make existing synchronous-looking guest code cooperate with host async APIs. It does not define an FRP scheduler. [V8 JSPI explanation](https://v8.dev/blog/jspi). Stack switching is a distinct Core proposal for typed continuations, coroutines, generators, and lightweight threads; it is a future experimental option for a guest scheduler. [Stack-switching explainer](https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md).

WASI 0.3 is already stable/current in the consulted official release pages, not merely forthcoming. WASI 0.3.0 was released June 11, 2026. It supplies native async component interfaces using `async func`, `stream<T>`, and `future<T>`; the runtime carries scheduling/wakeups across component boundaries. The documentation identifies Wasmtime 46+ and jco support. This makes typed event-source and service components a plausible integration target. Pin the exact WIT/interfaces and toolchain: component support and interface-version compatibility must still be checked. [WASI releases](https://wasi.dev/releases), [WASI 0.3](https://wasi.dev/releases/wasi-p3). Such streams carry async data; they do not automatically satisfy our logical-time, simultaneous-event, replay, or cancellation laws.

## Semantic guarantees that discovery cannot establish

A feature probe establishes acceptance, not performance, deadline guarantees, faithful source semantics, replay determinism, or cancellation safety. Even Core 3's deterministic profile concerns instruction behavior: it fixes generated NaNs and relaxed-vector choices, while resource-exhaustion outcomes remain possible. The spec says profiles are fixed platform choices and discourages runtime conditioning on the current profile. Host input ordering and concurrent scheduling need independent contracts. [Core profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).

For this repository, retain the proved closed transition as the portable baseline. Evaluate enhanced kernels behind the same semantic transition contract. A persistent worker, state residency, and batched calls are conceivable runtime improvements without waiting for a new Core release. Unlike the present one-worker-per-call memory-free design, persistent state and imports require stronger abort/recovery and side-effect rules. Capability-based artifact selection can happen at load time; live switching between representations additionally requires an explicit state migration proof/contract.

## Delivered work and existing plans

Repository source baseline: `0271cd593de3496f52660bd976f7f6b5432346f4`.
Issue bodies, states and relevant delivery comments were checked on 2026-11-16.
Older roadmap checkboxes can lag behind those deliveries.

| Scope | Current status and consequence |
| --- | --- |
| [#488](https://github.com/VladimirMarko/conaled/issues/488), [#509](https://github.com/VladimirMarko/conaled/issues/509), [#511](https://github.com/VladimirMarko/conaled/issues/511), [#512](https://github.com/VladimirMarko/conaled/issues/512) | Delivered selected Core semantics, canonical word circuits, proved binary serialization and Node artifact execution. The native-word comparison in #509 is not an emitted packed-word backend. |
| [#513](https://github.com/VladimirMarko/conaled/issues/513) | Open, scheduled packed i32 add/xor/select lowering with codecs, semantics, binary extension and artifact tests. These integer instructions need no new Wasm proposal; the missing work is our lowering and its evidence. |
| [#515](https://github.com/VladimirMarko/conaled/issues/515) | Open, live two-delay migration between Boolean slots and packed Wasm words, including conversion, failed preparation and complete costs. It depends on the packed target; it is not general cross-process or crash-recoverable Wasm migration. |
| [#485](https://github.com/VladimirMarko/conaled/issues/485), [#486](https://github.com/VladimirMarko/conaled/issues/486), [#487](https://github.com/VladimirMarko/conaled/issues/487) | Delivered bounded heterogeneous regional composition, policy selection and live split/fuse/repartitioning, including pending work. These are concrete native/circuit experiments, not a general Wasm feature dispatcher. See [plans](regional-reactive-plans.md), [selection](regional-selection.md), [quiescent migration](regional-migration-quiescent.md) and [pending migration](regional-migration-pending.md). |
| [#481](https://github.com/VladimirMarko/conaled/issues/481), [#489](https://github.com/VladimirMarko/conaled/issues/489) | Open frontend/backend admission and source-to-artifact evidence work. Operations, semantic evidence and resource/progress evidence are separate requirements. #490's completed comparison did not select #489's production evidence architecture. |
| [#27](https://github.com/VladimirMarko/conaled/issues/27) | Owns the broader hybrid runtime direction: executable phases/switching, numerical contracts and scheduling experiments. Wasm emission does not complete these. The [adopted direction](frp-runtime-direction.md#adopted-revision-after-the-design-challenge) preserves independent progress of these trials. |
| [#540](https://github.com/VladimirMarko/conaled/issues/540), [#581](https://github.com/VladimirMarko/conaled/issues/581) | The [bounded pending-crash model](pending-crash-recovery-implementation.md) is implemented under an explicit atomic durable-peer contract. Physical durable-peer realization remains open in #581; [#568](https://github.com/VladimirMarko/conaled/issues/568) owns bounded retention and safe identity reuse and is being worked on in a separate session. The delivered #540 journal, receipts and lifetime identities grow with history. Wasm, WASI or component streams alone do not discharge that assumption; a composed host/storage realization could supply it under its own contract. |

The inspected Wasm issues do not schedule SIMD, GC, Wasm threads, JSPI, stack
switching or WASI integration. Those are conceivable extensions below, not
accepted deliverables. This negative finding covers repository searches for
Wasm and FRP plus the linked scope owners, not every possible issue title.

## Recommended capability admission and experiments

Retain the Core 2 proof pin for the existing fragment. Document a small emitted
feature profile, currently i32/local operations plus multivalue where used.
A newer host may execute that profile without making all its extra instructions
admissible. Extend proofs, byte correspondence and subset admission together
when adding an opcode or representation. A future move to Core 3 as the semantic
reference should review correspondence for the used rules; it is not just an
engine version bump.

For a bounded catalog of composed realizations, an admission procedure could check:

1. The source-to-artifact contract and required observations exist for this
   program, representation and exact artifacts along the selected composition.
2. Each selected module uses instructions, types and signatures accepted by its
   engine. Software lowerings may discharge source requirements before this step.
3. Its host imports, permissions and ABI are available in the execution realm.
4. Its resource and progress evidence meets this workload's requested contract.
5. The enclosing regional plan admits its conversions, buffers, ordering and
   state ownership. Only then may the existing choice machinery rank it.

A manifest is a proposed specialization of that procedure, not a replacement
for #489's unselected evidence design. Record engine build/configuration, host
context, artifact/ABI identity and probe version with cached evidence. Recheck
when that context changes. A failed probe needs a reason where available:
unsupported feature, unavailable host facility, malformed bytes or resource
refusal must not all become a claim that the source is invalid. Unknown resource
bounds cannot be treated as zero. A fallback must independently preserve the
requested observations and satisfy admission; if none does, reject explicitly.
These recommendations reuse [policy-directed choice](policy-directed-choice.md)
and the existing regional selection discipline.

For example, an FRP application could keep a scalar state transition in the
baseline representation, choose a SIMD artifact for an independent numerical
region, and use a host adapter for event ingress. This is a hypothetical design.
A device lacking SIMD would select the scalar region only if its complete plan
still met the requested throughput/storage contract. A dynamic region may choose a software heap or native GC; neither choice makes
native GC a requirement for the source language or every other region. If the chosen
representation changes during a session, preserve the current continuation and
pending ownership through a constructed transfer; rerunning initialization or
reinterpreting old state is not a valid fallback.

Recommended experiments, beyond already scheduled #513/#515 and the complete
regional workload-cost work in [#516](https://github.com/VladimirMarko/conaled/issues/516):

- Build one adaptive package with a genuine optional-feature alternative and a
  software route preserving the same observations. Exercise absent features,
  invalid artifacts, unavailable analysis and no admissible candidate. Keep the
  feature matrix specific to emitted artifacts; reuse #481 admission and #486
  choice rather than selecting a universal capability framework.
- Extend that package to bounded online replacement only after its state and
  ownership contract is explicit. Reuse #515's Wasm transfer and #487's stronger
  pending-work results where their hypotheses apply, and #516's cost discipline.
  Precompiled replacement and online code generation are separate deliverables;
  the first need not wait for an online compiler.

- Compare the current per-call worker path with persistent workers, cached
  compilation and bounded batching. Keep source state parent-owned initially;
  preserve isolation, cancellation, worker replacement and commit-after-success.
  Measure startup, copies, validation and end-to-end ticks before selecting a
  design. Moving state into guest memory is a separate ownership change.
- Add one scalar/SIMD numerical kernel only with matched accuracy and event
  observations. Batch independent work or an admitted sequence of transitions;
  do not delay observable publication merely to fill a vector. Relaxed SIMD and
  floating-point reassociation need an approximation contract where they change
  results. Neither a successful probe nor fewer instructions proves a speedup.
- Compare host workers communicating by messages with shared-memory Wasm threads
  for a bounded dependency graph. Preserve complete logical-time batches,
  deterministic commit order, cancellation retirement and backpressure. Feature
  availability alone says nothing about fairness or hard real-time deadlines.
- Trial a typed asynchronous event-source component using pinned WASI 0.3
  interfaces, or JSPI when the deployment is JavaScript-hosted. Specify how
  stream closure, failure, cancellation and outstanding reads map to FRP
  observations. Keep stack-switching experiments separate from that host adapter.

GC/typed references and tail calls become useful when a concrete dynamic graph,
closure or recursive client justifies them. Such a client may be semantically
admitted without the bounded-space service guarantee; the design must express
that distinction. Memory64 has no immediate use for today's memory-free target.
No extension is a prerequisite for improving the current discrete runtime.

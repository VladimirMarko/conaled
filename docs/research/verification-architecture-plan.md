# Connecting verification tooling to compositional semantics

This is the architecture and acceptance plan requested on 2026-11-12 after
the assessment of [#7](https://github.com/VladimirMarko/conaled/issues/7).
The inventory repair is implemented alongside this plan. The remaining stages
below are proposed work, not established verification guarantees.
[Recipe refinement #43](https://github.com/VladimirMarko/conaled/issues/43) and
[artifact reuse #222](https://github.com/VladimirMarko/conaled/issues/222)
retain their acceptance scope. External interaction contracts remain coordinated
with #194/#196; this plan does not close or replace those issues.

## Current implementation and the missing connection

The production verifier is Python orchestration, Lean source preflight, Lake
compilation and an executable Lean axiom audit. It does not instantiate the
library's commutative squares, interaction contracts or strategy semantics to
justify its filesystem and subprocess operations. Importing the library into
the audit makes its declarations available for inspection; it is not a proof
that the audit or its driver refines a specification.

Failures are handled operationally: nonzero exits stop acceptance, artifact
mismatches cause invalidation or failure, and candidate identity is checked
before and after verification. These checks do not provide a formal semantics
of filesystem mutation, process interruption or artifact publication. The
current [documented assumptions](../../README.md#build-and-audit) remain in force.

The shared [source inventory](../../scripts/project_sources.py) now supplies
coverage, candidate identity and audit ownership. It inventories all root Lean
modules and the integrated source trees, excluding `ProofAudit` from mathematical
ownership. The audit calls its JSON command from the project root and then uses
Lean's module-origin metadata. This repairs a coverage gap; it does not prove
the inventory process truthful or the filesystem stable. Standalone audits
inspect the loaded declarations belonging to that inventory. `check.sh` also
checks entrypoint reachability and compilation of the whole inventory.

## Independent acceptance meaning

Define the required property before choosing a controller or event encoding.
For an identified candidate input collection, success must establish:

1. The inventory and public import closure agree on all mathematical modules.
2. Source policy passes for the input collection actually used for compilation.
3. Every required module has successful compilation evidence after successful
   prerequisites. Fresh mode requires compilation during this run; reuse mode
   requires the separately established reuse contract.
4. The audit examines all owned kernel-safe declarations, including private and
   generated declarations, in the environment corresponding to those artifacts.
   Only the existing three foundational axioms are admitted transitively.
5. The published result names that collection, mode and audit evidence. A failed
   or unknown operation cannot supply a positive fact required for acceptance.

This specification must not be defined as whatever the existing controller
accepts. Completeness is relative to sufficient evidence and supported inputs;
it must not promise that an unresponsive compiler, OS or service will respond.
An isolated checkout is a practical discipline, not a proof of immutable inputs.

Separate the candidate's intended revision, captured bytes, bytes consumed by
the compiler, artifact bytes produced, and artifacts later imported. An equality
between two of these needs evidence. Matching path names, before/after Git
identities or untrusted digests cannot silently supply every equality.

## Semantic interfaces and composition

The proposed pure controller consumes observations and emits requests or a
decision. A production adapter executes requests and supplies observations.
Its interpretation relates concrete histories and controller state to an
independently specified verification behavior. The principal claim is conditional:
given primitive correspondence and interference contracts, accepting a concrete
run implies the acceptance property above for its identified input collection.

Use exact squares for deterministic transformations whose observations agree
exactly, such as the selected inventory representation or a pure decision core.
Use relational preservation/refinement for external operations with several
permitted outcomes. State the source and target carriers, observations and
preservation law for each connection; a square diagram alone proves nothing.
Compose established local contracts with the library's laws. Do not assume the
whole desired run is correct in the premise of its correctness theorem.

The first interfaces should expose these distinctions:

| Interface | Semantic observations and obligations |
|---|---|
| Inventory and import interpretation | Module ownership, file identity, parsed dependencies, omitted or missing sources; Lean remains the syntax authority. |
| Input capture | Identified captured collection and allowed live mutation; coherent revision and captured collection are different properties. |
| Compilation attempt | Request identity, exact inputs/options/toolchain, launch, completion or unknown completion, output availability; failed attempts may leave partial outputs. |
| Artifact publication/reuse | Produced and consumed byte identities, provenance, complete publication, invalidation; unknown evidence never authorizes reuse. |
| Audit | Owned roots and transitive dependencies for the selected checked environment; exact versus summarized enumeration has an explicit refinement obligation. |
| Result publication | Provisional evidence, observed publication and acknowledgement; interrupted publication does not retroactively erase effects. Durability requires a separate contract. |

Adapters must retain failure and uncertainty rather than reducing all outcomes
to a Boolean. A timeout does not prove that a process had no effect. Cleanup
success does not prove compilation success. A receipt write that returned is
not automatically crash-durable. Hash assumptions distinguish accidental stale
state from adversarial substitution.

## Reuse from the existing library

| Existing construction | Planned use and remaining obligation |
|---|---|
| [Interaction.Safe, Stable and safe_interference_seq](../../SquareKit/InteractionContracts.lean) | Compose stages while permitting stated environment changes. Establish stable intermediate assertions for actual captured inputs and evidence. |
| [Interaction.Refines and its composition/property laws](../../SquareKit/InteractionContracts.lean) | Transport acceptance through justified observations. Prove local correspondence; do not erase evidence needed by downstream consumers. |
| [Snapshot.compile_sealed](../../Applications/Interaction/Snapshot.lean) | Reuse the captured-input contract once the adapter really consumes that collection. Its existing live-read and mixed-revision counterexamples remain applicable. |
| [Measurement controller](../../Applications/Interaction/Measurement.lean) and [connected pilot](measurement-attempt-pilot.md) | Reuse the separation of successful observations from external facts and the pattern of executing the proved decision function. Its cooperative single-child protocol is not yet a generic compiler runner. |
| [Event interpretation](../../SquareKit/InteractionEvents.lean) | Reuse sequence simulation for fixed finite scripts where it fits. A response-dependent scheduler needs more than an unconditional list of events. |
| [Finite strategies](finite-interaction-strategies.md) and [overlapping prefix observations](interaction-prefix-observation.md) | Assess legal request/reply histories, matching, hiding and pending prefixes against a concrete compiler client. Existing Boolean relay models do not already model filesystem contents or arbitrary subprocesses. |

Select tools by the contract they discharge, not by a requirement to use squares
or games everywhere. The inventory above is a reuse shortlist, not an exhaustive
selection from the library. Before implementation, search the current library for
each concrete obligation and compare its hypotheses and observation contract with
the proposed interface. A direct relational contract can be the better choice;
introduce a richer encoding only when a checked client demonstrates what it adds.

Any game-semantic comparison should freeze the native verifier observation first:
which request remains pending, which module/artifact a response concerns, which
dependencies succeeded and which effects are known. Compare the direct controller
interpretation with a strategy interpretation on those same observations. Retain
shared internal witnesses when composing or hiding channels. A trace with legal
question/answer order may still contain a false report about artifact bytes;
protocol legality and primitive truth are separate obligations.

Start with serial fresh compilation as a checked specialization, then the current
bounded concurrent scheduler. Preserve production modes throughout migration.
Do not force the serial Boolean forwarding model to stand for arbitrary overlap,
nor make a universal game framework a prerequisite. If existing strategy
interfaces cannot express the required client, record the precise missing
contract and a scoped extension rather than claim adoption by analogy.

## Bootstrap without self-certification

Using the library to construct the verifier does not establish the truth of
its own observations. Keep an explicit bootstrap path that requires only the
pinned Lean/Lake toolchain, dependency artifacts and a small documented driver.
It freshly checks the source containing the controller proofs and runs a simple
reference enumeration/audit without relying on the optimized controller's
acceptance decision. Its filesystem, compiler, metadata and dependency-cache
assumptions remain trusted and listed.

The checked controller is then compiled and used by the production adapter.
Prefer executing its proved definitions over maintaining an independent Python
copy. If a translation or cross-language protocol is needed, give it a tested
and, where practical, proved representation contract. The Lean execution
toolchain remains a runtime trust assumption even when the controller theorem
has been kernel-checked.

Retain a cache-independent project build and a reference root scan as independent
cross-checks. They can detect divergence but are not a formal proof of the entire
bootstrap. No acceptance theorem may assume the receipt it is being used to
justify, and no cache entry can authenticate its own provenance merely by
containing a matching trace. This is a bootstrap dependency ordering, not a
restriction against the verifier being a client of the library it checks.

## Delivery sequence and acceptance gates

| Stage | Deliverable | Acceptance evidence and scope owner |
|---|---|---|
| 0: ownership repair | One inventory shared by coverage, candidate checks and audit; automatic inclusion of new root modules | Public fresh/incremental fixtures, independent root scan including a new private root declaration, forbidden transitive dependency rejection, harmless external axiom acceptance, fail-closed inventory failure. This change. |
| 1: observations and contract | Independent acceptance predicate; explicit request, response, failure and unknown states; machine-readable stage evidence | Receipt includes inventory identity, coverage, compilation mode, audit ownership/counts, input/artifact links available so far and unresolved trust assumptions. Pending/failed stages cannot appear as passed. Preserve candidate identity checks and receipt compatibility through a documented format change. #43/#222. |
| 2: connected controller | Proved root enumeration, axiom acceptance and scheduling behavior; actual adapter executes the proved decisions | Exact reference/optimized root equality; private/generated/current-module cases; failure cannot release dependents or authorize audit; successful fresh runs compile every required module. Positive examples and counterexamples precede proof development. Record any runtime representation assumptions. #43. |
| 3: captured input and reuse | One bounded production artifact-reuse path with explicit input/output correspondence | Extend the current Lake assessment at its pinned revision; reuse is conditionally equivalent to the chosen fresh property, with a connected executable adapter. Unsupported or missing evidence forces rebuilding/rejection. Keep the temporary guard until the replacement covers its contract. #222. |
| 4: composition assessment | Select library constructions against the actual verifier obligations; compare alternative interpretations only where they offer a concrete benefit | Preserve pending requests, module identities, selected effects and audit ordering under the chosen composition. Games are a candidate, not a required architecture. Separate protocol soundness from byte/provenance correspondence. No unsupported full-abstraction, fairness or termination claim. Coordinate #194/#196 and #43/#222. |
| 5: operational assessment | Reproducible report for the actual adapters and both build modes | Cold, warm, changed-leaf, changed-foundation and separate-worktree cases; elapsed time, peak memory where available, compiled/reused counts, audit time and evidence cost. Report machine/toolchain/dependency identities, repetitions and failures. #222. |

Each implementation stage requires the normal independent Standards and Spec
reviews, applicable full build/audit, and process-level regression tests.
Statement review must check that assumptions are primitive and satisfiable,
that intended models qualify, and that the theorem concerns the actual decision
procedure. A separate unused model or a caller premise asserting final success
does not meet the connection gate. Stages 1–3 should preserve the ordinary
incremental command while adding verified decisions one responsibility at a time.

Required separating cases include: a root module absent from ownership; a
generated private declaration with a forbidden dependency; a source edit after
inspection; individually captured files that never coexisted; a failed compiler
leaving partial outputs; a stale artifact with a current input trace; a reply for
the wrong module; interrupted publication with an unknown acknowledgement; and a
pending process whose cleanup does not establish success. Exercise real process
and filesystem behavior where controllable, and label injected observations.
Tests outside the semantic model remain necessary for its adapter assumptions.

The performance comparison must include diagnostic and recovery behavior, not
just successful wall-clock measurements. Preserve a nonempty successful path
alongside rejection tests. The result should make it possible to inspect, for
each acceptance claim, its theorem, the executed definition, the evidence used,
and the external assumptions still owed.

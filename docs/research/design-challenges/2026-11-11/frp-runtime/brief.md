# FRP runtime design challenge: shared neutral brief

Assessment date: 2026-11-11. Source baseline:
`1ecdea2376786920a043009a35712a5dec93723a`.

## Decision and intended capability

Assess whether the candidate compositional hybrid runtime and its staged route
serve a Lean library of compositional verified programs. The intended capability
space includes executable dynamic phase switching, categorical compilation to
alternative executable targets, asynchronous demand scheduling, continuous-time
computation under numerical contracts, external recovery, policy-directed choice,
and replacement of the backend of an already-running session. Assess both the
long-term architecture and which first deliverables best test its assumptions.

The requester wants an architectural challenge, with prior personal preferences
withheld from the judges. No prior approval, rejection, or preferred option is
provided. Do not infer a required verdict from the candidate's existence, its
level of detail, or the order of its stages. Architecture, sequence, representation
choices, boundaries, and the value of individual stages are open to challenge.
This is an investigation, not authorization to implement the runtime.

## Candidate, rationale and alternatives

Read `source/docs/research/frp-runtime-direction.md`, the neutral candidate
packet. It proposes compiled discrete/continuous phases with strict event order
and knowledge frontiers, bounded admission/backpressure, interchangeable
execution targets, and explicit optional recovery contracts. The staged route is:
A rational phase evaluation/switching; B startup selection using existing choice
support; C a bounded emitted backend artifact; D a bounded demand graph with
cancellation; E a certified continuous client; F one recoverable reactive session;
G between-ticks backend migration followed by migration with pending work.

The candidate rationale is reuse of existing source/compiler/simulation,
resource, numerical and durability constructions with local obligations rather
than a universal runtime interface. That is a hypothesis to test, not an
established composition theorem. Compare plausible alternatives, including a
smaller synchronous execution core, different placements of the state/effect
boundary, direct library composition, or other well-supported approaches. An
alternative does not need an adapter to the current architecture to merit study.

## Constraints and preserved observations

- Preserve useful existing mathematical results and concrete clients under their
  current assumptions. New implementations may coexist and may justify changing
  interfaces; present client compatibility and migration costs explicitly.
- Distinguish source behavior switching from replacing an implementation of the
  same behavior. Preserve the observations the client actually needs, including
  ordered occurrences, residual state, and conditional delivery.
- Distinguish exact denotation, approximation/error, progress, abstract resource
  bounds, empirical performance, and host/compiler/IO assumptions. Do not replace
  any of these with an unproved claim about another.
- No fixed native language, worker technology, queue protocol, storage backend,
  universal AST, or physical real-time deadline is a prior requirement.
- The architecture should permit execution and ordinary library use; no demand
  for a universal bounded runtime or arbitrary exact integration is intended.
- Existing semantics and designs are evidence to inspect, not unquestionable
  restrictions. Identify deliberate semantic changes and what they would cost.

## Evidence and independence protocol

Use ONLY the pinned source archive at
`/tmp/conaled-frp-design-evidence/source` for local repository reading. It has no
Git metadata. Its candidate report has preference/disposition language removed;
technical scopes and acceptance criteria are retained. All other archive files
are the pinned committed source. Uncommitted inputs are not part of this
assessment. Do not read the original checkout, its Git history, previous session
handoffs, other agents' reports, or live project GitHub issues/comments. These can
reveal withheld preferences. Do not follow the candidate's links to unsanitized
copies of itself or project issues. If a project fact needs clarification, ask
the coordinator, who can supply a preference-free source excerpt. External
primary literature and non-project source repositories may be researched.

Inspect the actual declarations and consumers rather than treating research
notes as conclusive. Use repository-relative file/line or declaration citations,
and pinned primary external URLs. Document any accidental exposure promptly.

Start with AGENTS.md, README development/build sections,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, GLOSSARY.md,
`docs/adr/README.md` and applicable ADRs, `docs/language-direction.md`, and the
paper-level counterexample checks in the example-driven-development skill.
Follow no-ai-slop for authored prose. You are assigned an assessment inside this
challenge; do not launch another challenge, implementation/review loop, or agents.

Relevant implementation and consumer entrypoints:

- `Applications/FRP/{Spec,Frontier,Engine,Pipeline,Lifecycle,Exclusive,RetainedLifecycle,Indefinite,DriverIO}.lean`;
  `Examples/` FRP and indefinite-service callers.
- `SquareKit/ReactiveCompiler.lean`, `FirstOrder.lean`,
  `Applications/Circuits/{Syntax,Execution}.lean`.
- `Applications/Progress/{Feedback,Reactive}.lean`;
  `Progress.Feedback.run_related` is declared in Reactive.lean.
- `Applications/Optimization/Choice/{Selection,Evidence}.lean`,
  `Applications/Parallel/PolicyChoice.lean`,
  `Applications/Sequences/LCA/PolicyChoice.lean` and their checked clients.
- `Applications/Orbifold/{CheckedMotion,NumericalExecution}.lean`,
  `Applications/Orbifold/Driver/`, numerical-motion and budget-disk-driver notes.
- `Applications/Durability/{Protocol,RetentionBanks}.lean`,
  `docs/research/accepted-history-implementation.md`.
- Current `docs/research/interaction-prefix-observation.md` and its Lean pointers
  are additional evidence for observation and branching distinctions. Read them
  if relevant; their tracker links are not permission to fetch project issues.

The compiled finite-circuit runner, scalar frontier/lifecycle, startup selector,
and numerical driver have separate contracts. Whether those can form a coherent
runtime, and whether the proposed order discovers the hard obligations soon
enough, are open questions. Do not assume that compilation proves scheduling,
that a relation computes migration, or that a fixed field count bounds storage.
Also investigate which obligations already follow from existing constructions
before proposing new proof fields or a new layer.

## Three perspectives

1. **Contracts and foundations:** determine whether proposed operations/laws
   establish the intended consequences; distinguish derivable results, missing
   premises, representation-specific restrictions and genuinely new semantics.
   Check concrete phase boundaries, partial knowledge, continuation equivalence,
   delayed feedback, effect ownership and numerical contracts.
2. **Implementation and use:** assess builder/caller obligations, state and queue
   organization, admission/backpressure, migration cost/failure, author effort,
   instrumentation overhead and executable evidence. Determine whether the
   proposed first clients exercise useful work or hide the difficult couplings.
3. **Alternatives and generality:** compare other execution and semantic
   organizations, including relevant primary-source approaches beyond local
   precedent. Test whether demand-driven/hybrid scope, global graph scheduling,
   and the proposed stage dependencies are justified. Preserve the goal while
   considering changes to the candidate.

These lenses target different failure modes; none owns facts exclusively. Do not
coordinate verdicts or read one another's reports before all initial reports
are saved. The coordinator will synthesize only after reading all three.

## Permitted work and outputs

Read-only investigation and small, isolated executable counterexample scripts
are permitted. Put any experiment in your own subdirectory of
`/tmp/conaled-frp-design-evidence/scratch/`. Use the Nix shell for project commands;
read README first. No full Lean build, dependency download, benchmark or shared
build-cache mutation is requested. Ask the coordinator if a focused Lean check
is necessary; a paper counterexample may be sufficient if clearly labeled.
Do not modify the candidate, create/update issues or contact other sessions.

Write your initial report to your assigned report path. Include:

- A recommendation and strongest evidence for retaining the candidate.
- Concrete findings with stable identifiers, consequences and source evidence;
  distinguish established mismatch, plausible risk and unanswered question.
- Smallest useful correction or alternative, retained/changed guarantees, and
  a discriminating test for unresolved choices.
- Missing evidence, prior involvement/exposure, tool/model metadata available
  to you, and validation limits. Do not claim model diversity or proof checking
  from independent report writing.

Preserve initial reports after completion; later clarifications go in separately
named supplements. Aim for a focused assessment, not an exhaustive FRP survey.
The final shared brief, neutral packet, reports, any supplements and synthesis
will be preserved using the repository's research-publication workflow. That
publication review is separate from these three design judgments.

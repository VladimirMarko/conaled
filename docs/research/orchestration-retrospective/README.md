# Retrospective on the preservation-architecture orchestration

Assessment at `c4cbfdea38817f64760fb03319a94d25422dc65a`, after [#417](https://github.com/VladimirMarko/conaled/issues/417) and [#128](https://github.com/VladimirMarko/conaled/issues/128)
closed. This covers the [shared-meaning experiments](../shared-meaning-experiment-results.md),
[semantic-tradition waves](../semantic-traditions-next-work.md), and their
application and checker follow-ups under [#235](https://github.com/VladimirMarko/conaled/issues/235). It does not attribute every pre-existing library
component to this orchestration.

The waves produced a substantial collection of reusable mathematics, constructed
models, and bounded executable tools. They established many concrete ways to
compose correct parts. They did not establish that a new author can economically
assemble a large mixed setting, port an arbitrary proof development, or use the
intended frontend language. Completed issue counts cannot answer those questions.

Three separately run agent assessments informed this synthesis:
[foundations](foundations-initial.md), [use and scaling](use-initial.md), and
[alternatives and neglect](alternatives-initial.md). The assessors received the
same neutral brief and pinned source, inspected reports and selected code, and
did not read one another's drafts before saving their initial conclusions. They
did not rerun builds or independently repeat the literature studies. Agreement
does not establish model diversity or replace the earlier formal acceptance
reviews. The initial reports are preserved unchanged.

## What was built

| Area | Concrete result | Remaining boundary |
|---|---|---|
| Dependent reasoning and equality | [Reference typing judgments](../reference-dependent-calculus.md) for contexts, substitutions and intensional identity elimination, with a forward translation into an explicit extension of the guarded engine; [pair contracts](../denotation-boundaries-and-settings.md) and [selected-path comparisons](../relational-and-selected-path-boundaries.md) distinguish representation equations from specified identities | No general reverse translator, arbitrary Agda importer or joint higher/smooth model |
| Shared meanings and compilation | [Optional proof and computational capabilities](../shared-meaning-experiment-results.md) use one shared map of semantic evidence; [resource-mode compilation](../mode-based-adjoint-compiler.md) has an adjunction for its unrestricted/linear modes, finite combinator grammar and degree-preserving model | New primitives and models still need proofs that they satisfy the interfaces; these are not full institution categories or a universal intermediate representation |
| Alternative semantic foundations | The [tradition successor map](../semantic-traditions-next-work.md) records nominal binding, random-function spaces and represented sampler substitution, finite Horn-clause support, classical control, modal access and dependent extension, and finite interaction/hiding | Each has its own admitted fragment and observation; no general winner was established |
| Internal partial computation | The [internal solver](../internal-selected-certificate-solver.md) constructs tracked assemblies (objects and maps equipped with realizability evidence), classification of admissible partial maps, lifting, and a countdown solver retaining its selected certificate; its completeness property extends maps from finite cuts to full cuts in every assembly context | This is not a construction of the entire effective topos; not all external states are uniformly realizable, and tracker existence is separate from runtime adequacy |
| Concrete applications | [Witness-sensitive parser policies](../shared-meaning-experiment-results.md), [functional reactive programming (FRP) execution](../frp-runtime-follow-up.md), [geometry comparisons](../geometry-realization-experiment-results.md), [numerical error composition](../semantic-traditions-first-wave.md), a [bounded exact-rational driver](../numerical-driver-checkpoint.md), and [approximate feedback wiring](../approximate-wiring-experiment.md) | Abstract costs are not host costs; exact geometry does not automatically provide numerical input acquisition or a complete simulator |
| Emitted artifacts and acceptance | [Pure and cached ConLeche acceptance](../relative-cached-acceptance.md) of the canonical fourteen-record emitted family, with exact resulting environments and malformed-input controls; the report also records checker-source intake and compiled execution reproduction | Acceptance for that family is unconditional; model existence retains a `SetTheory V` premise, source comparisons retain compatibility assumptions, and general checker equivalence and native binary correctness are not proved |

Two results deserve particular weight. The probability work constructed the
random-function space model and exhibited two sampling constructions with equal
marginals but different joint laws. The internal synthetic domain theory (SDT)
work constructed the tracked operations and objects satisfying its cut-extension
completeness property in every assembly context. Those were missing mathematical capabilities, not
additional wrappers around an existing interpreter.

Other successes were discoveries that no new infrastructure was needed. Existing
[relational compilers](../semantic-traditions-first-wave.md) handled first-in,
first-out queues (FIFO) and intervals; [indexed theory maps](../indexed-relational-transfer.md)
handled cursor results whose capacity changes; [strict-map transport](../context-dependent-partial-computation.md)
connected selected solutions under its stated compatibility hypotheses. Here an
external solution means one specified outside the internal mathematical model,
not a deployed external application.

In this report, the **native route** means direct use of existing library APIs
and general laws. The **shared route** uses the additional compositional
interfaces being tested. Both can reuse proofs. This use of “native” is unrelated
to native machine-code execution. Retaining the direct route was a positive
outcome of the comparisons.

## What the evidence taught us

**Specify the observation before choosing the abstraction.** A selected parse,
a proof tree, a probability law, a service history and a higher path are different
contracts. Replacing a selected witness with the mere assertion that some
witness exists can erase distinctions the client requires. Likewise, retaining
only marginal distributions can lose a joint law’s correlations.
Conversely, Horn support and the finite-interaction quotient demonstrate useful
contracts that deliberately forget selections or histories. Preserving maximal
data is not a universal specification. Distinct representations can have equal
meanings. Consequently, a specification’s equality need not require equality of
representations.

**Local laws can remove repeated global proofs.** The indexed compiler derives
whole-term preservation from primitive certificates; constructor/observer laws
derive contextual behavior; cached transition lemmas assemble the exact checker
run. This is actual reuse. Authors using the native route can also exploit it: the scaling trial
did not justify forcing all clients through a more elaborate interface.

**Organizing interpretations does not construct a model.** The implemented
[institution-inspired interfaces](../shared-meaning-experiment-results.md)
require proof translation and computational realization to commute with the
same map of semantic evidence when those capabilities are supplied. They organize
supplied interpretations; they do not construct their models or establish that
separately admitted capabilities coexist. Joint admission is still a major
obligation for the intended dependent, higher and smooth applications.

**Semantic, operational and resource claims require different evidence.** A
constant can have a specified denotation while lacking an executable reduction
rule. An evaluator may get stuck if it must evaluate that constant, as the
[canonicity diagnostic](../executable-canonicity-obligations.md) shows. An unused
body can remain unevaluated. A selected event history is not independent evidence that a
physical operation occurred. A rational error theorem does not bound arithmetic
bit growth. These distinctions exposed useful obligations rather than reasons
to exclude noncomputable specifications.

**The proof's quantifier domain matters.** Review found missing
[monoidal coherence laws in an early linear fixture](../progressive-institution-capabilities.md),
a [pure-term substitution argument applied to mixed syntax with runtime continuations](../semantic-traditions-first-wave.md),
and an [SDT plan](../internal-selected-certificate-solver.md) that confused separate
pointwise witnesses with one tracked construction working uniformly over a context. Corrected code and rejecting examples now record the
repairs. The successful examples we had did not expose every omission; the
repairs required checking the intended laws and the scope of the arguments.

## What received less attention than the ambition requires

The principal imbalance is between the breadth of bounded constructions and the
evidence for their combined use. That is an allocation judgment, not a finding
that the accepted component theorems are false.

1. **A substantial independent consumer.** Feedback from an independent agent’s
   [Agda formalization of Myers’s orbifold theory](../architecture-scaling-study/orbifold-consumer-assessment.md)
   changed the geometry work and exposed requirements for interpreting that source. It
   did not establish successful adoption of the intended library. The original
   source-to-higher/smooth-model-to-classical comparison remains under [#100](https://github.com/VladimirMarko/conaled/issues/100)/[#36](https://github.com/VladimirMarko/conaled/issues/36),
   with the [#102](https://github.com/VladimirMarko/conaled/issues/102) source-transfer repair/retest requirement and the [#103](https://github.com/VladimirMarko/conaled/issues/103)
   dependent smooth-interpretation checkpoint intact. Adjacent positive results do not complete it.
2. **Authoring and frontend access.** The large language ambition is still ahead
   of the implemented fragments. Source acquisition and surface studies remain
   [#115](https://github.com/VladimirMarko/conaled/issues/115)–[#117](https://github.com/VladimirMarko/conaled/issues/117). The [#107](https://github.com/VladimirMarko/conaled/issues/107) repair is user-paused. The [#108](https://github.com/VladimirMarko/conaled/issues/108) fresh-agent test
   awaits a reviewed interface freeze and an unprepared fresh theorem. Neither
   may be silently resumed or described as completed by other author trials.
3. **Scaling of total effort.** In the [scaling trial for #358](../dependent-operation-scaling.md),
   both fresh agent authors completed three cumulative task stages and a repair.
   Across their reported task intervals, the native route took less summed time;
   the shared route used fewer Lean checks and reported shorter intervals for
   stage C and repair. Both reused generic proofs. Exact model and reasoning
   configurations were unavailable, and timing was not synchronized. One agent
   per route, coupled scale dimensions and unmeasured prior design effort prevent
   causal or asymptotic claims. Discovery, setup, model admission,
   review and maintenance costs are not captured by short client proofs.
   The dedicated equivalent-task Lean/Felix caller-effort comparison ([#25](https://github.com/VladimirMarko/conaled/issues/25)) also
   remains open. Local upstream comparisons do not settle that broader benchmark.
4. **Alternatives that change the questions.** The earlier requirement for a
   second existing library client before investigating an alternative was a
   documented discovery bias. Probability,
   SDT, nominal binding, support, control and games reduced that bias.
   The sample still favors finite generated syntax and selected outputs.
   Matching logic, local universes, richer modal/higher combinations and other
   deferred traditions remain possibilities, not disproved approaches. Assigning a broad
   tracking issue and a trigger for reconsideration does not establish that
   anyone is actively investigating the direction.
5. **System-level acquisition and execution.** Bounded runtimes exist, but proving
   that inputs satisfy a model’s assumptions, choosing useful numerical
   representations, connecting formal operations to real devices, and combining
   components with different contracts remain separate work. The
   [exact-rational numerical driver measurements](../numerical-driver-checkpoint.md)
   show why theorem-level error control alone does not settle practicality.
6. **Status and discovery.** Historical wave summaries necessarily describe
   intermediate states, but parent issues can also lag. At assessment time
   [#289](https://github.com/VladimirMarko/conaled/issues/289) still described [#371](https://github.com/VladimirMarko/conaled/issues/371)/[#386](https://github.com/VladimirMarko/conaled/issues/386)–[#389](https://github.com/VladimirMarko/conaled/issues/389) as unfinished, although the solver was
   accepted. Older lists of unresolved obligations point to [#193](https://github.com/VladimirMarko/conaled/issues/193) as their tracking
   issue although it is closed. This requires reconciliation; it must not be reported as missing
   mathematics. The [recovery of accepted prepared-query code](../completed-work-delivery.md)
   for [#305](https://github.com/VladimirMarko/conaled/issues/305) and
   [#306](https://github.com/VladimirMarko/conaled/issues/306) from a branch that had
   not reached master is a related reminder that reviews alone do not ensure
   delivery and discoverability.

The [scaling evidence](../dependent-operation-scaling.md),
[external-consumer assessment](../architecture-scaling-study/orbifold-consumer-assessment.md),
[tradition selection criteria](../semantic-traditions-next-work.md) and
[driver measurements](../numerical-driver-checkpoint.md) support these limits.
The separately authored assessment reports identify exact source locations and additional examples.

## Consequences for the next assessment

Retain the successful libraries, independently defined specifications and native
specializations. The evidence favors starting with small interfaces, adding
optional capabilities when a client needs them, and proving local compatibility laws. It does not choose a single mandatory foundation or
prove that no better formulation exists.

Before another broad implementation wave, assess one intended consumer whose
requirements cross an unresolved boundary. Trace its original source theorem, without weakening its requirements, through
source admission, model construction, interpretation, realization and required
observation. Translations may change its representation; this is not a requirement
for identical source text. Mark each connection as constructed, assumed or missing. This should
respect existing pauses and compare the available native route.

If making a productivity claim, choose a new recurring obligation, allow both
routes to reuse existing general laws, and measure the additional work each route
requires. Include model/setup and repair costs. Vary scale dimensions separately
to distinguish their effects, and use multiple fresh authors per route to assess
variation between participants. Do not infer a benefit from a growing theorem count or a deliberately
weak native baseline.

Review a small sample of dormant alternatives for capabilities outside the
current client set. Requiring an adapter to the incumbent design would recreate
the discovery bias that later waves reduced by admitting independently motivated
alternatives.

These are assessment recommendations, not new tickets or implementation
authorization. At this assessment snapshot, further implementation scheduling
for this orchestration was stopped after [#417](https://github.com/VladimirMarko/conaled/issues/417)/[#128](https://github.com/VladimirMarko/conaled/issues/128) closure. The diagnostic
investigation in [#418](https://github.com/VladimirMarko/conaled/issues/418) and measurement-tooling work in [#195](https://github.com/VladimirMarko/conaled/issues/195) were deferred. The next strategic question is how
economically a new consumer can discover and compose the available guarantees.

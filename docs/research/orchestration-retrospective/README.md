# Retrospective on the preservation-architecture orchestration

Assessment at `c4cbfdea38817f64760fb03319a94d25422dc65a`, after #417 and #128
closed. This covers the architecture, shared-meaning, semantic-tradition and
later application waves. It does not attribute every pre-existing library
component to this orchestration.

The waves produced a substantial collection of reusable mathematics, constructed
models, and bounded executable tools. They established many concrete ways to
compose correct parts. They did not establish that a new author can economically
assemble a large mixed setting, port an arbitrary proof development, or use the
intended frontend language. Completed issue counts cannot answer those questions.

Three independent assessments informed this synthesis:
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
| Dependent reasoning and equality | Independently specified reference judgments, a checked forward translation, derived structural laws, distinct pair contracts and selected higher-witness comparisons | Not a general reverse translator, arbitrary Agda importer or joint higher/smooth model |
| Shared meanings and compilation | Optional proof, realization and relational capabilities sharing one evidence map; indexed local laws derive substitution, interpretation and emission results; a resource-mode fragment has an actual adjunction | New primitives and models still require their own admission proofs; these are not full institution categories or a universal IR |
| Alternative semantic foundations | Nominal binding, random-function spaces and represented sampler substitution, Horn support, classical control, modal access and dependent extension, finite interaction/hiding | Each has its own admitted fragment and observation; no general winner was established |
| Internal partial computation | Tracked assemblies, admissible partial-map classification, lifting monads, all-context completeness, iteration and a constructed selected-certificate solver | Not all external states are uniformly realizable; tracker existence is separate from runtime adequacy |
| Concrete applications | Witness-sensitive parser policies and cost models, FRP execution and retention, geometry and representation comparisons, numerical error composition, a bounded rational driver and approximate feedback wiring | Abstract costs are not host costs; exact geometry does not automatically provide numerical input acquisition or a complete simulator |
| Emitted artifacts and acceptance | Bounded producer/validator connections, exact pure and cached acceptance of the actual emitted family, model consumers and malformed-input controls; supplied checker source and native reproduction | Explicit semantic and execution trust boundaries remain; no general checker equivalence or binary-correctness result |

The [shared-meaning report](../shared-meaning-experiment-results.md),
[tradition successor map](../semantic-traditions-next-work.md),
[completed internal solver](../internal-selected-certificate-solver.md),
[geometry comparison](../geometry-realization-experiment-results.md) and
[cached acceptance report](../relative-cached-acceptance.md) give the precise
contracts and source entry points.

Two results deserve particular weight. The probability work constructed the
function-space model and distinguished equal marginals from unequal joint laws.
The internal SDT work constructed the uniform tracked operations and complete
objects its solver required. Those were missing mathematical capabilities, not
additional wrappers around an existing interpreter.

Other successes were discoveries that no new infrastructure was needed. Existing
relational compilers handled FIFO and intervals; indexed theory maps handled
capacity-changing cursor results; existing strict-map transport handled the
external selected-solution client. Retaining the native interface was a positive
outcome of those comparisons.

## What the evidence taught us

**Specify the observation before choosing the abstraction.** A selected parse,
a proof tree, a probability law, a service history and a higher path are different
contracts. Truth or existence can forget distinctions those clients require.
Conversely, Horn support and the finite-interaction quotient demonstrate useful
contracts that deliberately forget selections or histories. Preserving maximal
data is not a universal specification. Distinct representations can have equal
meanings. Consequently, a specification’s equality need not require equality of
representations.

**Local laws can remove repeated global proofs.** The indexed compiler derives
whole-term preservation from primitive certificates; constructor/observer laws
derive contextual behavior; cached transition lemmas assemble the exact checker
run. This is actual reuse. Native authors can also exploit it: the scaling trial
did not justify forcing all clients through a more elaborate interface.

**Organizing interpretations does not construct a model.** Institutions and
compatible squares help ensure that proof translation and computation use the
same meaning. They cannot supply missing model constructors or prove that
independently admitted capabilities coexist. Joint admission is still a major
obligation for the intended dependent, higher and smooth applications.

**Semantic, operational and resource claims require different evidence.** A
meaningful constant can be operationally stuck when demanded. An unused body can
remain unevaluated. A selected event history is not independent evidence that a
physical operation occurred. A rational error theorem does not bound arithmetic
bit growth. These distinctions exposed useful obligations rather than reasons
to exclude noncomputable specifications.

**The proof's quantifier domain matters.** Review found missing structural
coherence in an early linear fixture, a substitution argument applied outside
its syntax, and an SDT plan that confused pointwise witnesses with uniform
contextual constructions. Corrected code and rejecting examples now record the
repairs. Finite examples alone would not have caught every omission.

## What received less attention than the ambition requires

The principal imbalance is between the breadth of bounded constructions and the
evidence for their combined use. That is an allocation judgment, not a finding
that the accepted component theorems are false.

1. **A substantial independent consumer.** The external Agda/Myers feedback
   changed the geometry work and exposed meaningful admission requirements. It
   did not establish successful adoption of the intended library. The original
   source-to-higher/smooth-model-to-classical comparison remains under #100/#36,
   with the #102/#103 gates intact. Adjacent positive results do not complete it.
2. **Authoring and frontend access.** The large language ambition is still ahead
   of the implemented fragments. Source acquisition and surface studies remain
   #115–#117. The paused #107 repair and protected #108 fresh-author test must
   not be silently resumed or described as completed by other author trials.
3. **Scaling of total effort.** In #358 both authors completed the three scales
   and repair. Native took less reported total stage time; shared used fewer
   checks and had lower reported late-stage times. Both reused generic proofs.
   One author per route, coupled scale dimensions and unmeasured prior design
   effort prevent causal or asymptotic claims. Discovery, setup, model admission,
   review and maintenance costs are not captured by short client proofs.
   The dedicated equivalent-task Lean/Felix caller-effort comparison (#25) also
   remains open. Local upstream comparisons do not settle that broader benchmark.
4. **Alternatives that change the questions.** The earlier requirement for a
   second incumbent consumer was a documented discovery bias. Probability,
   SDT, nominal binding, support, control and games materially corrected it.
   The sample still favors finite generated syntax and selected outputs.
   Matching logic, local universes, richer modal/higher combinations and other
   deferred traditions remain possibilities, not disproved approaches. A broad
   owner and a re-entry condition are not evidence of active investigation.
5. **System-level acquisition and execution.** Bounded runtimes exist, but input
   admission, useful numerical representations, physical adapters and mixed
   component applications remain separate work. The rational driver measurements
   show why theorem-level error control alone does not settle practicality.
6. **Status and discovery.** Historical wave summaries necessarily describe
   intermediate states, but current parents can also lag. At assessment time
   #289 still described #371/#386–#389 as unfinished, although the solver was
   accepted. Older residual ledgers point to #193 as an owner although it is
   closed. This requires reconciliation; it must not be reported as missing
   mathematics. The earlier recovery of accepted unpublished branch work is a
   related reminder that reviews alone do not ensure delivery and discoverability.

The [scaling evidence](../dependent-operation-scaling.md),
[external-consumer assessment](../architecture-scaling-study/orbifold-consumer-assessment.md),
[tradition selection criteria](../semantic-traditions-next-work.md) and
[driver measurements](../numerical-driver-checkpoint.md) support these limits.
The independent reports identify exact source locations and additional examples.

## Consequences for the next assessment

Retain the successful libraries, independently defined specifications and native
specializations. The evidence favors progressively requested capabilities and
local compatibility laws. It does not choose a single mandatory foundation or
prove that no better formulation exists.

Before another broad implementation wave, assess one intended consumer whose
requirements cross an unresolved boundary. Trace its unchanged statement through
source admission, model construction, interpretation, realization and required
observation. Mark each connection as constructed, assumed or missing. This should
respect existing pauses and compare the available native route.

If making a productivity claim, measure a recurring obligation the existing
helpers do not already absorb. Include model/setup and repair costs, allow both
routes to reuse public general laws, and separate scale dimensions or repeat
authors. Do not infer a benefit from a growing theorem count or a deliberately
weak native baseline.

Review a small sample of dormant alternatives for capabilities outside the
current client set. Requiring an adapter to the incumbent design would recreate
the discovery bias that the later waves corrected.

These are assessment recommendations, not new tickets or implementation
authorization. Scheduling remains stopped after #417/#128 closure and the
recorded #418/#195 follow-up disposition. The next strategic question is how
economically a new consumer can discover and compose the available guarantees.

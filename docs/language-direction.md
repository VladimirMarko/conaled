# A language whose mathematical setting is a first-class parameter

**Make the mathematical setting a first-class parameter of programming and
proof.** Authors should be able to express a construction or argument in
familiar mathematical language, identify the structure and principles it uses,
and reuse it in every setting that supplies them. This is a shared long-term
direction for categorical compilation and internal-language reasoning.

Agreed with the project owner on 2026-10-19. This document records the ambition
and the criteria by which to develop it. The language's architecture remains
open: checked work in both workstreams should progressively constrain its
shape. It is not a claim that the current library already provides this language.

## The author should be able to factor out the setting

Internal languages let mathematicians reason using familiar variables,
functions, constructions and logical arguments inside different mathematical
settings. Reusing that reasoning makes analogies visible. An author can
recognize that a construction only needs products, or that a proof uses
intuitionistic logic together with a particular differential principle, and
then extract that common requirement.

Our language should support that act of discovery. The author should work with
the mathematics, with the alterations that the chosen setting actually demands.
Routine manipulation of encoded syntax, variable indices, interpretation
wrappers and derivation trees should belong to the implementation. Making
those operations look prettier is insufficient if the author must still carry
the same bookkeeping through every argument.

The desired abstraction includes meaning and admissible reasoning. Functions,
equality and quantifiers may receive different interpretations in different
settings, while retaining the specified behavior that justifies a shared
argument. Semantic differences must remain expressible. Higher identity,
constructive existence and crisp-context restrictions cannot be erased merely
to make every setting look alike.

Equality and pair laws belong to the specification of the mathematical setting.
A representation can use a different equality when its interpretation validates
that specification. Clients at the semantic interface must respect the
specified equivalence; compiler clients inspecting representations have a
different contract. Interpretations may be relations or retain witnesses rather
than be functions into a single carrier. The representation must retain enough
data for the chosen specification, including relevant identity witnesses.
Individual developments should state the preservation obligations they use;
this does not require an exhaustive equality taxonomy in every issue.

## Compilation and proof share this requirement

| Categorical compilation | Internal reasoning |
|---|---|
| A program uses particular operations. | A proof uses particular constructions and rules. |
| A target supplies the required operations and laws. | A setting validates the required constructions and principles. |
| Compilation interprets the program. | A model interprets the argument. |
| Preservation establishes the stated correctness contract. | Soundness establishes validity in that model. |
| Changing targets can preserve the program. | Changing settings can preserve the argument. |

The requirements belong to the reusable construction or proof. A selected
target or setting supplies evidence that it meets them. We want authors to be
able to state these requirements, tooling to help reveal them, and reusable
interpretations to discharge them. Inference or minimization of requirements
is a design question, not an assumption that every weakest requirement can be
computed automatically.

Changes of setting need their own preservation contracts. A result may
transport along one map of models but not another. The language should make
the reusable argument and the missing obligation visible without requiring
authors to reconstruct the semantics at each use.

Clarified with the project owner on 2026-11-15: support both interpreting a
shared argument in multiple settings and transporting constructions and proofs
between settings whenever their mathematical requirements hold. Separate
interpretations establish validity in their respective models; transport also
needs a connection preserving the structures, judgments and witnesses used by
the argument. Neither achievement alone establishes the other. Research should
develop both routes, identify their hypotheses and composition laws, and retain
explicit ownership of missing capabilities or mathematical obstructions.

Existing constructions are starting points for expansion into wider and more
powerful frameworks. Assess those frameworks by the additional mathematics and
reusable arguments they support, while recovering existing clients under their
original contracts. Reuse does not require retaining the current interfaces
unchanged, and a bounded comparison does not set the language's expressive limit.
The [six-functor investigation](research/six-functor-language.md) tests these
goals on coherently varying settings and their realizations.

This goes beyond sharing a parser or concrete notation between workstreams.
The common design problem is which constructions and reasoning principles can
be abstracted, how their requirements compose, and which interpretations
preserve them. Shared implementation should follow demonstrated commonality;
the two workstreams need not be forced into identical fragments.

## Mathematical targets and external foundations

Clarified with the project owner on 2026-11-12. A compilation target may be a
mathematical setting without a runnable implementation. A realization connects
two specified settings under an explicit preservation contract. Realizations
may compose when their interfaces, observations and assumptions align. There
is no mandatory hierarchy ending in an inherently physical or final backend.

Mathematical interpretation, artifact generation, abstract-machine execution
and hardware implementation are examples of settings and connections to study,
not four fundamental levels or a universal ordering of stronger capabilities.
An abstract machine may be realized by a hardware model, which may itself be
related to another implementation model. Further layers are permitted without
changing the general problem of establishing the relevant semantic connection.

The connections need not all be code translations or functions. State/trace
simulations, approximation bounds and witness-preserving interpretations have
different contracts. Prove their applicable composition laws; a shared notion
of realization does not make their observations or guarantees interchangeable.
Do not impose one maximal record or a fixed pipeline on ordinary clients.

Describe computable realization relative to a named computational model.
Distinguish an existence theorem from supplied executable code, termination or
progress, and resource guarantees. A finite artifact can name an oracle without
implementing it. Noncomputability under one model can rule out a realization
into that model while leaving other mathematical interpretations valid. These
are obligations on particular connections, not a separate kind of realization.
Target execution may use a different evaluation strategy when the selected
observations are preserved.

A formal relation between a device model and an abstract machine does not by
itself establish that an actual device satisfies that model. State empirical
and environmental assumptions when applying the theorem. Another implementation
or simulation layer may refine those assumptions, but does not automatically
discharge them. This distinction concerns evidence for the premises, not a
privileged class of physical arrows or a claim about the nature of our universe.

Explore unusual settings as mathematics and as tests of the compiler's
abstractions. Their value need not depend on a runnable product. Oracle-relative
computation, synthetic computability, quantum semantics and idealized
noncomputable operations provide candidate examples and counterexamples.
Quantum computation is not presumed to be hypercomputation. A change in
computational capability does not automatically validate a new rule of deduction,
and a physical backend does not uniquely determine a mathematical foundation.

The compiler's current implementation and verification use Lean. This does not
select native Lean judgments as the mandatory external evidence interface.
The choice of external foundations remains open. Compare interfaces that retain
source judgments, required principles and witnesses through several justified
interpretations, including non-identity changes of setting. A direct Lean route
is a specialization only where the judgments and meanings align. Merely wrapping
all foreign obligations in native Lean propositions does not establish that the
interface preserves the desired source capabilities.

Keep compiler implementation language, verification metatheory, source logic,
target semantics and physical-realization assumptions distinguishable. Checking
an interpretation in Lean establishes the stated result relative to its audited
dependencies; it does not supply unrestricted mutual interpretation of Lean and
Agda, reflection from one model, or a foundation-free checker for every logic.
Do not solve portability by silently narrowing all sources to a fixed common
logic. State missing interpretations and capabilities, retain usable direct
clients, and compare alternatives before selecting a general interface.

[#493](https://github.com/VladimirMarko/conaled/issues/493) owns the comparative
programme and bounded formalization studies linked in the
[research agenda](research/language-research-agenda.md#mathematical-targets-and-foundation-relative-interfaces).
The completed [MMT study](research/mmt-compiler-evidence.md) and
[evidence-interface comparison](research/compiler-evidence-comparison.md) are
inputs, not architecture adoption. #489's production bridge still requires the
owner's selected evidence contract and source fragment. The tracker owns current
readiness and completion status.

## What remains open, and what guides the design

Lean can remain the host and trusted checker. Explicit syntax and derivations
are possible implementation mechanisms; they are not the intended ceiling on
the author's experience. A language hosted in Lean can still make its own
settings and judgments first-class. No decision to leave Lean, change its
kernel, or adopt a standalone surface language follows from this direction.

Lean's native axioms can express assumptions within its existing logic. They
do not replace its equality or kernel rules when a mathematical setting changes.
The broader capability requires checked interpretations of the supported
language. Existing proof-audit requirements remain in force, and ordinary Lean
clients must retain their direct interfaces without additional setup.

Use future compilation and internal-language work to answer concrete questions:

- Can the same construction or proof serve distinct settings with its required
  capabilities stated and satisfied, without duplicating the argument?
- Can an author recognize and extract a common abstraction without manipulating
  its representation as syntax throughout the proof?
- Does using an additional principle expose an additional requirement? Does a
  setting lacking it produce a precise obligation rather than silently importing
  a stronger ambient logic?
- Does a change of interpretation preserve the intended result through an
  explicit checked contract, including relevant equality and witness data?
- Which differences between settings are mathematically essential, and which
  recurring author obligations should the implementation absorb?

These are design tests for successive bounded developments, not a requirement
to build a universal language before delivering useful mathematics. Record what
each development teaches us about the language and revise proposed interfaces
accordingly. A small working fragment can be valuable while its author interface
remains below the long-term goal.

For the MVP, the project owner accepts an agent-productivity advantage as
sufficient (2026-11-07). Human-productivity evidence is not an acceptance gate.
Compare agents under matched mathematical contracts and record completion,
repair effort and resource use where available. Separate infrastructure setup
from repeated authoring costs. The completed bounded author trials establish
feasibility; their small samples and incomplete effort records do not establish
a general productivity advantage.

## Developing library and compiler capabilities together

Start a capability with its mathematical meaning, required structure and intended
observations. The domain library supplies reusable constructions and laws;
compiler interpretations assemble those laws for supported source expressions.
A frontend connects the author's language to those expressions and judgments.
Lean currently supplies the implementation language and verification metatheory.
A future Lean source frontend has its own preservation obligations; denotational
specification alone does not discharge them or remove foundational assumptions.

For work connecting these facets, choose a representative client with a direct
mathematical specification and a compiled realization. Reuse existing cases when
they already establish the connection. Check whether a different source or
interpretation can reuse the laws, and state exactly which observations survive
replacement. Library clients should be able to use the construction without
compiler bookkeeping; compiler clients should reuse its laws without rebuilding
the domain proofs. Mathematical requirements determine the supported fragment.
Useful library development can proceed before a frontend expresses it.

Use the observed missing capability to place the next change: mathematics in
the library, systematic interpretation in the compiler, and author expression
in the frontend. Assess costs, approximations and witness preservation under
their own contracts. Equal denotations alone do not establish equal execution
costs. Apply these checks where integration is intended, without requiring every
library theorem to acquire a compiler route.

For a capability change intended to connect library and compiler use, apply
these completion criteria in the task and its review:

1. State the mathematical contract, required structure and observations, naming
   the existing constructions and laws to reuse.
2. Check a direct client and a compiled or interpreted client against that
   contract. Reuse retained cases when they suffice; check a replacement or
   second interpretation where it tests a claimed reuse benefit.
3. Inspect what remains with callers: repeated proofs, representation or binding
   bookkeeping, and unsupported judgments. Place each consequential gap with
   its library, compiler or frontend owner; use existing issues where they fit.
4. Record what to adopt, retain or defer from the evidence, including the
   preserved guarantees and any distinct resource or witness obligations.

Keep this evidence in the existing task/review handoff and relevant API examples.
Create a separate design record only when it serves a further decision. A useful
scoped result can be complete while a linked follow-up remains open; a future
consumer alone does not justify a shared interface or broad migration.

The [mapped-aggregate client](../Examples/MappedAggregate.lean) supplies a first
replacement case. Its independent specification sums `(x + 2) * (x + 2)` over
the input and applies a scalar report. One source duplicates the shift; another
uses a source `let`. The [library replacement laws](../Applications/Incremental/MappedAggregate.lean)
derive equality of initialized states, subsequent repair states and boundary
deltas, and workload outputs from pointwise agreement of scalar meanings.
They reuse existing compiler-to-library preservation theorems. The repair law
covers arbitrary retained states, so switching sources requires no conversion
or reinitialization. Correctness relative to raw inputs still uses the existing
state invariant.

Under the unit primitive tariff, the two sources cost five and three per scalar
evaluation. The checked workload saving is twice the input length plus twice
the number of assignments, including repeated writes. This is a modeled cost,
not a Lean runtime benchmark. It separates semantic substitutability from
representation-dependent efficiency while preserving the existing library client.

This case needed no new common interface or duplicate domain proof: small
replacement theorems expose consequences of existing laws. Author work remains
in constructing typed terms, choosing an explicit source `let`, and connecting
the source meaning to the ordinary formula. These are concrete frontend and
automation opportunities; this example provides neither Lean quotation nor an
automatic sharing transformation. It justifies reusing the replacement laws
for this scalar/aggregate interface, without establishing portability of arbitrary
Lean definitions or a general author-productivity advantage.

## Selecting research by semantic requirements

Agreed with the project owner on 2026-10-30: evaluate literature against the
language ambition above. Familiarity within this repository, citation counts,
and the number of published variants do not establish suitability. Compare a
tradition's semantic commitments and explanatory power before spending effort
comparing its algorithms. Existing integrations are evidence about particular
constructions, not a representative survey of the available mathematics.

Prefer compositional denotational accounts whose meaning is specified
independently of a chosen execution mechanism. Operational semantics can help
establish implementation correctness, adequacy and resource properties. Read
work presented operationally for useful mathematics, while asking which
independent semantic contract it supports. Neither popularity nor presentation
style alone settles that question.

Separate discovery, comparison and integration. Begin external discovery from
the ambition and required author capabilities before using the local inventory
to assess fit. Include approaches that might replace or subsume our architecture;
do not filter them out because they need a difficult Lean encoding or cannot
produce a small example immediately. Compare explicit assumptions, composition,
extension obligations, preserved equality and witnesses, and author effort.
Record omitted traditions and uncertainty. Propose discriminating experiments
that our current approach could fail, rather than only examples it already fits.
#235 retains continuing discovery and integration ownership, coordinated with
#36, #200 and #8. [#280](https://github.com/VladimirMarko/conaled/issues/280) owns
the completed bounded external discovery and research-priority assessment.
The [external comparison assessment](research/external-language-comparison.md)
records the completed first pass, its omissions and proposed matched experiments.
The [subsequent assessment](research/external-discovery-assessment.md) revises
the next sequence toward proof-derived requirements (#286) and representation
extensions with explicit model/witness contracts (#287). Keep dependent
coherence tied to concrete author failures. The completed paper comparisons of
[proof-derived requirements](research/proof-requirement-comparison.md) and
[representation extensions](research/representation-extension-comparison.md)
retain extraction as a complementary authoring service and a bounded extension
certificate with separate witness-descent obligations. They establish neither
an implemented importer/model framework nor measured author benefit. Further
implementation needs a concrete client and its own scope under #235.

The [research agenda](research/language-research-agenda.md) gives these next
steps explicit owners: compositional theory extensions (#288), dependent
semantics and coherence (#289), and reusable theories and proof transport
(#290). Their first tasks and lower-priority studies may challenge the current
architecture; an immediately available adapter is not a condition for taking
a competing theory seriously. These programmes organize research without
committing the language to a universal foundation.

The [checked representation-extension study](research/all-model-representation-extensions.md)
now supplies bounded all-model expansion and selected-section descent. Keep
their obligations separate: admitting a representation for every model does
not supply a natural representative selector or make every selected section
descend. Clients still owe the relevant compatibility and equivariance laws.

The [dependent coherence comparison](research/dependent-coherence-comparison.md)
separates the author's judgment-interpretation boundary from the construction
of semantic models. Strict semantic substitution alone does not repair source
annotations or establish that interpretation contract. Keep the independent
memo's dependent higher-witness test as an adoption condition, and compare
local universes, direct strict models and chosen-universe constructions against
it. A bounded Type-family specialization must not replace that requirement.
The [three-perspective reassessment](research/dependent-architecture-reassessment.md)
keeps author requirements, interpretation, model construction and comparisons
as interacting responsibilities rather than fixed independent layers. Derive
what follows from existing universal properties before adding assumptions;
separate primitive signatures and constructor capabilities where the arguments
permit it. Stronger laws can constrain existing operations as well as accompany
new ones. Compare alternative foundations when current judgments impose
recurring presentation work. Interpretation comparisons must act coherently on
types, terms and dependent witnesses. A setting constructed from presentation
data varying within a context needs its own reindexing contract; externally
selected models do not establish that capability. These are research criteria,
not a decision to adopt a particular structural core or framework.

The [structure audit](research/dependent-structure-audit.md) now derives
comprehension and generated empty substitutions from existing laws. Reuse
those results before introducing stronger assumptions. Terminal uniqueness and
the choice of morphisms remain explicit requirements where a construction
needs them. The [nested internal-setting test](research/internal-setting-construction.md)
also establishes a bounded positive case for context-varying presentations,
including their selected dependent payloads under repeated substitution.
The [judgment experiment](research/dependent-judgment-representation.md) now
supplies a source boundary without all-model annotation indices. Authors'
derivations inherit interpretation, substitution and strict-map preservation;
model builders prove the primitive operation laws once. Keep source-typing
effort, coherent comparison scope and old-client migration explicit.
The [frozen author trial](research/dependent-author-interface-trial.md) establishes
completion of the same selected J argument through both interfaces. Candidate
authoring avoids semantic-code indices, while the baseline's motive helper
already handles its branch alignment. A missing candidate root-tail helper
was repaired in [#323](https://github.com/VladimirMarko/conaled/issues/323).
The [successor trial](../experiments/guarded-j-retest/trial/evaluation.md)
records both fresh authors completing the nested-J contract without assistance
or interface changes, with exact submission replay. The original trial remains
unchanged. Adopt the guarded boundary for the tested contract; retain the
baseline and do not infer lower total author effort or broad migration from
these small comparisons.
The [constructor experiment](research/dependent-constructor-admission.md)
checks this discipline for object-language dependent sums. Its operations and
inverse laws derive dependent elimination and compatibility, while exact
reduct recovery retains old selected witnesses. Judgmental eta is an explicit
capability requirement. A further law-only extension shows that new requirements
can also constrain existing operations. Admit each extension against its
semantic contract; forward inclusion and reduct recovery alone do not prove
conservativity or expansion of every old model.
The [checked higher source test](research/dependent-higher-identity.md) retains
the frozen memo's witness observations. The subsequent
[cubical construction](research/cubical-model-construction.md) and
[strict 2-groupoid construction](research/strict-two-groupoid-checkpoint.md)
now supply bounded Lean interpretations with nontrivial higher observations.
Those constructions discharge the specified higher-consumer gate; they do not
establish an arbitrary higher-type-theory importer or universal model framework.
Keep their model evidence separate from source checking and author trials.
The [categorical assessment](research/concrete-dependent-coherence.md) keeps
strictification conditional on a named model-construction benefit. Construct
the required hypotheses for that consumer when strict stability is the missing
capability or the transfer removes demonstrated recurring coherence work.

The [theory-network comparison](research/theory-network-comparison.md) likewise
keeps publication and view composition separate from encoding adequacy and
changes of logic. A total assignment of declarations must preserve their laws
and selected data; a framework's composition theorem does not discharge those
obligations for a new encoding.

The [requirement-discovery trial](research/proof-requirement-author-trial.md)
compares independent manual and prepared-ledger authors on frozen tasks. Both
retained reusable proofs and selected data; their sufficient witness interfaces
differed. Use a dependency ledger as optional, reviewable evidence about a
particular proof. Removing a proof detour requires a checked replacement proof,
and choosing a more general interface remains a separate design task. This
bounded trial does not establish causal savings or a preferred architecture.

The duality agenda in #266–#270 is promising but remains a set of hypotheses,
not a ranking established by an external comparison. Investigating variance,
inclusion, implication and explicit coercion evidence likewise does not commit
the language to global implicit subtyping. #257's evidence contracts remain
useful if the optional #260 elaborator is declined. Before activating #260,
compare explicit evidence and constraint-based alternatives on the same author
tasks, select the semantic algebra and preservation obligations, and record why
inference earns its additional assumptions. Experience with Java or Haskell
alone cannot decide the suitability of Dolan's algebra. Type-class encodings of
subtype relations do not establish a need for global value subsumption; see the
[video clarification](research/language-design-and-type-systems.md#the-supplied-video).

## Construction, observation and verified presentations

The constructor–destructor investigation adds a design test: where the laws
permit it, can authors change between constructor-oriented and observer-oriented
presentations without rewriting the underlying equations or losing their meaning?
Treat source organization as a candidate verified view, not an obligatory choice
of one universal intermediate language. Preserve ordinary clients and the
semantic distinctions of fragments that do not fit the same presentation.

Make the observation contract explicit when extending a language. Adding a
representation under an unchanged contract differs from adding an observer that
can distinguish previously equivalent representations. Old theorems remain
scoped to their stated assumptions and observations; stronger observations need
compatibility proofs, and may require a richer representation. New type
interpretations must meet their stated admissibility laws, and new operations
must supply the compatibility proofs needed to reuse existing client theorems.
Neither retaining old equations nor adding axioms alone establishes arbitrary
metatheorem preservation.

Investigate whether local construction/observation laws compose into reusable
semantic interpretations, and whether forward representation transport and
backward observation transport fit the existing preservation architecture.
Explore symmetric producer/consumer proof syntax while keeping logic, polarity,
evaluation order and their equality laws explicit. These are questions to test
against existing indexed and witness-sensitive examples, not commitments to a
Chu model, a distributive-law framework, a sequent calculus, or a fixed execution
strategy for every setting.

The [duality findings and agenda](research/duality-language-directions.md)
distinguish checked results, source theorems, design inferences and conjectures.
#256 supplies a bounded syntax transformation; it does not establish an
isomorphism between arbitrary data and codata, a generic semantic lifting, or
infinite productivity. The completed #266–#270 studies test that agenda;
#262 retains semantic-type extension work, coordinated with #235/#36/#200/#8.

The [#268 composition experiment](research/compositional-constructor-observer-laws.md)
now demonstrates this discipline for finitary derivative templates: local
constructor compatibility yields interpretations of arbitrary finite composites,
with separate renaming and substitution laws. Weighted concatenation and a
pointwise extension recover their prior meanings. This supplies one usable
instance, not a universal rule format. The completed #271/#274 results extend
finite composition to fixed indexed families, index-changing constructors and
exact parser result fibers. They do not supply arbitrary dependent-context
substitution or changes of index base.

The [recent workstream assessment](research/construction-observation-research-assessment.md)
connects these results to the wider research agenda. #277 derives a supported
local rule from either equation presentation; #276 lifts exact equations through
finite contexts; #278 proves constructor/observer interaction obligations against
an independent meaning. #284 separately constructs coordinate-guarded recursive
solutions and their transport. #285 relates higher-order costed execution to an
independent function denotation and rejects recovering step counts from that
denotation. These are several checked contracts, not one universal lifting
mechanism. The new theory-extension, coherence and proof-transport programmes
must recover these capabilities or explain their different scope.

Completed #279 provides independent author evidence for the tested vector and
parser interfaces. It does not measure equation-table authoring, discovering a
proof's requirements, or general dependent reasoning. Those remain distinct
author tasks; existing successful trials need not wait for the wider design
space to be settled.

## Evolving preservation laws and usable specializations

The [preservation inventory](research/preservation-contract-inventory.md) is a
revisable set of architectural tests. New clients may expose missing judgments,
comparison data or composition laws. When a client does not fit, retain its
native contract and identify the mismatch: an additional assumption, a missing
adapter, a new compatible layer or an existing interface that needs revision.
Track unresolved work with a scoped owner. The initial examples do not define
the limit of the family, and recording a gap does not resolve it.

A justified expansion may require retrofitting foundations and existing
consumers. Evaluate that change against both the new client and prior concrete
specializations. Recover the prior guarantees under the same assumptions,
including witnesses and observations. Use checked migrations or specialized
facades when interfaces change. Keep executable and resource claims explicit;
semantic preservation alone does not establish implementation performance.

Generality must remain usable by authors and agents. Compare direct/native
and shared/specialized solutions to the same representative tasks. Record the
concepts and obligations the author must supply, internal wrappers or casts,
diagnostics, assistance and successful completion. Preserve familiar concrete
operations where they suffice; authors should not need unrelated structures
or the entire framework to use a specialization. Checked examples establish
meaning, while independent author trials test whether the public interface and
documentation expose that meaning effectively. Agent trials are evidence about
those trials, not a claim of usability for every human author.

[#235](https://github.com/VladimirMarko/conaled/issues/235) owns continued
compatibility, retrofits and specialization usability within
[#200](https://github.com/VladimirMarko/conaled/issues/200), coordinated with
#36's models and #8's categorical foundations. The bounded
[#231](https://github.com/VladimirMarko/conaled/issues/231) experiment must hand
off its applicability findings and remaining work there. Revisit the record
when new families or author difficulties appear and at experiment completion.
Closing one experiment does not close the architectural programme; any successor
must retain explicit ownership of unresolved work.

## Elegance, author capability and language constraints

Evaluate mathematical structure, its encoding in Lean, and the experience of
using that encoding separately. An elegant construction can have an awkward
host-language realization; concise Lean code can also conceal restrictive
assumptions. Record the layer responsible for a difficulty and the evidence for
that diagnosis. Distinguish missing mathematical structure, interface design,
documentation, language expressiveness, elaboration behavior and author
capability. A failed attempt alone establishes neither a language limitation
nor the impossibility of a practical encoding.

Apply this separation to planning and adoption decisions too. Immediate syntax
or author-effort savings are one benefit alongside reuse across consumers and
compilation targets, stronger guarantees, fewer repeated proof obligations, and
foundations for the future language. Assess these benefits against implementation,
migration and maintenance costs. Distinguish demonstrated reuse from a proposed
future consumer; changing agent capabilities or a future frontend can change
encoding costs without changing the mathematical value. Neither current author
difficulty nor speculative future reuse settles the priority by itself.

Report a trial's concrete result and adoption decision separately from unanswered
research questions. State what to adopt, retain, refine or defer, for which tasks,
and what work remains with callers. A demonstrated reduction in repeated caller
work can justify bounded reuse without establishing a universal productivity
advantage. Account for library preparation and maintenance costs; require broader
evidence before recommending a broad migration. Do not summarize a useful scoped
result as merely inconclusive because a general comparison remains unresolved.

Research and bounded author trials can proceed alongside each other. Freeze
the interface, mathematical contract and permitted assistance for each trial;
retain the attempts as a baseline when the interface later changes. Use failures
to identify missing abstractions as well as local repairs. Reassess changed
interfaces with affected tasks and fresh held-out tasks, preserving author
independence and separating preparation cost from author effort. A trial does
not commit the project to its tested architecture or rank unexplored designs.
The [agenda](research/language-research-agenda.md#author-trials-alongside-architectural-research)
records completed evidence and the distinct prerequisites of pending trials.

Author trials measure effectiveness for recorded authors, tasks and tools.
Retain model/version, configuration and resource budget, available documentation,
Lean/toolchain revision, assistance, attempts and outcomes. Record unavailable
metadata explicitly. Agent capability can change with newer models or the
choice of cheaper workers. Separate present adoption cost from mathematical
quality and long-term generality; difficulty for a current agent is evidence
to investigate, not by itself grounds to reject an elegant design. Near-term
usability still matters when selecting a practical implementation.

Prefer useful specializations of shared constructions over disconnected levels
of interface sophistication. A specialization should discharge recurring
requirements, infer routine structure or supply a common interpretation; its
guarantees should follow from the general laws. Preserve the concrete client's
capabilities and assumptions, shared vocabulary, and a path to the general
interface. Compare wrapper and conversion costs as well as convenience: several
interfaces can fragment use and undermine the value of a common abstraction.
Elegance and ease of use need not conflict, but record the trade-off when they do.

Revisit abstractions when new consumers expose missing laws, stronger assumptions,
repeated adapter work or author difficulties, and when language/tooling or author
capabilities change. At workstream planning checkpoints, also reconsider promising
alternatives that individual tasks may not surface. #235 owns this reassessment;
these checkpoints do not create a scheduled automation. Preserve prior evidence
and compare unchanged tasks where possible so improvements in a model, toolchain
and design are not conflated.

A proposed replacement should identify the benefit, migration and refactoring
cost, affected consumers, and checked recovery of established specializations.
Small fixes to documentation or inference may suffice; a deeper redesign may be
worth its cost. Neither current usability nor mathematical elegance alone settles
that choice. Record decisions and remaining constraints without treating a
current Lean encoding as the limit of the mathematical direction.

### Elaboration resource budgets

Treat Lean recursion limits as finite, adjustable engineering budgets. Preserve
the mathematical interface and try a modest local increase before restructuring
a useful abstraction solely to fit the default. Scope overrides to the affected
declaration or module, retain heartbeat and process-time safeguards, and record
the motivating client and measured behavior. Recursion depth, heartbeats, wall
time and memory measure different constraints; report only what was measured.
Increasing a recursion budget does not weaken kernel checking or set the runtime
complexity limit of compiled functional programs.

Keep shared mathematical proofs and inexpensive computational specializations
when they improve reduction or concrete use. Multiple entry points can coexist
when their purpose and recovery contract are clear; independently maintained
implementations need a benefit that justifies their duplicated obligations.
Compare implementation maintenance and recurring caller costs before removing
a specialization or adding another public interface.

Investigate repeated budget escalation, widespread caller overrides or rapidly
growing work. Consider better reduction boundaries, explicit comparison lemmas,
specializations and a minimized upstream reproducer where evidence warrants it.
Broader evidence can justify changing a module or repository default; passing at
512 is not an architectural acceptance criterion. Keep normal production limits
finite and allow them to grow with legitimate developments.

The [complete-client measurements](research/representable-elaboration-costs.md#complete-client-diagnosis-under-a-separate-process-bound)
from #648/#661 support retaining the shallow native specialization and shared
proof. A direct regression passes at a higher recursion limit, but the full
client comparison also exposes heartbeat and async-setting differences.
Sampled passing budgets are not exact minima. The
[application reassessment](#resource-observations-and-adoption) records local
allowances and explicit proof boundaries with different outcomes; it supplies
no basis for a blanket default increase.

## Complementary presentations and reconstruction

Use complementary presentations when different definitions make different
constructions, proofs or computations easier. Connect them with proved maps
and recovery laws so callers can reuse the mathematics through the interface
that fits their task. Prefer convenient specializations derived from shared
constructions; preserve useful direct clients and access to the general API.

The [Lawvere development](lawvere-theories.md) provides exact action/algebra
round trips, algebra/model category equivalences and nonskeletal theory
comparisons. The [matroid presentations](research/matroid-presentations.md)
recover labelled finite matroids, while [geometric reconstruction](research/geometric-matroids.md)
recovers a finite simple matroid from its flat lattice with explicit relabelling.
These are examples of different recovery contracts, not evidence that every
pair of useful presentations is equivalent.

When designing, revisiting or integrating such interfaces:

- Identify the additional mathematics or author capability each presentation
  supports. Separate mathematical restrictions from Lean encoding/elaboration
  friction, missing proofs and current author effort.
- State the primitive operations and laws independently of the desired result.
  Derive reconstruction, universal properties and shared construction laws
  where they follow; a field asserting the final comparison does not establish
  that derivation. State genuinely additional compatibility assumptions.
- Prove the appropriate maps and recovery statements. Distinguish definitional
  or propositional equality, equivalence of object types, categorical
  equivalence, and one-way preservation. Include morphisms, substitution,
  identity/composition and dependent witnesses where the claimed contract
  uses them. Choose the strength the mathematics supports.
- Identify information forgotten by each map. Retain labels, ground sets,
  selected operations, multiplicities, probability mass or resource observations
  when clients need them. Test proposed recovery against separating examples;
  restrict hypotheses or retain richer data when recovery is impossible.
- Check established clients under their original assumptions and observations,
  alongside a new use of the general construction. Include relevant empty,
  nullary, nonliteral-representation and composite-transport cases. Measure
  adapter/setup obligations separately from recurring caller effort; conversion
  wrappers alone do not demonstrate shared proofs or improved usability.

Apply these criteria proportionally to the claimed change. A useful one-way
interpretation need not become an equivalence, and a shared proof need not
supply a bridge between its models. Preserve those distinctions in acceptance.
For incoming formalizations, assess whether their presentation adds capability,
can be recovered through existing shared interfaces, or reveals a missing
construction. Record deferred work with an owner while retaining useful source
mathematics and validation; acceptance of a bounded slice does not require
completing every architectural opportunity it exposes.

[#235](https://github.com/VladimirMarko/conaled/issues/235) coordinates continuing
applications. The [#636 reassessment](#reassessment-after-library-and-ctb-applications)
compares the initial examples with subsequent library and accepted CTB work;
the [interface search](research/reconstructible-presentations-search.md) retains
its source contracts, rejected routes and residual owners. Reassess when another
consumer exposes duplicated proof, erased information, stronger assumptions or
recurring adapter costs, and when changed tools or authors warrant a new bounded
comparison. Existing issue owners retain their individual acceptance criteria.

The [representable-classification programme #647](https://github.com/VladimirMarko/conaled/issues/647)
now includes coherent recovery, effective descent and ordinary bundle
classification. [#666](https://github.com/VladimirMarko/conaled/issues/666) owns
continuing descent/torsor/quotient applications. Compare direct families/display
maps, local universes and natural models under concrete semantic contracts;
use fibred categories, pseudofunctors and sheaf/stack descent where their
additional structure is required. The accepted results do not supply recovery
for arbitrary systems, selected-filler equality, general type-former closure or
univalence. Those obligations remain with their scoped owners in the inventory.

## Current evidence and ownership

### Reassessment after library and CTB applications

The [#636 reassessment](https://github.com/VladimirMarko/conaled/issues/636)
retains the recovery and primitive-law criteria above. The later applications
support conditional adoption of shared constructions, with native entry points
chosen according to the caller's available data. They do not support compulsory
migration, universal equivalences or general productivity claims. The
[discovery inventory](research/reconstructible-presentations-search.md) records
retained alternatives and rejected routes; the comparison below identifies the
mathematics and costs behind this decision.

| Application and source contract | Recovery and shared proof | Caller and maintenance consequence |
|---|---|---|
| Initial [Lawvere #611–613](lawvere-theories.md#recovering-algebras-and-models) | Action/algebra records have exact round trips; algebra/model and nonskeletal theory comparisons are categorical equivalences. Product universal properties recover all maps, including nullary operations. | Scalar, packaged-algebra and arbitrary-target model APIs remain useful. Explicit carriers, arities and dependent comparisons sometimes remain necessary; the equivalences do not make all representations definitionally equal. |
| [Sums and tensors #616](research/lawvere-combinations.md) | `sumIsColimit` constructs the coproduct in `Operations`; `tensorMapEquiv` classifies commuting pairs. Primitive interchange derives commutation of all operations. Unary schemes and their models recover through the shared construction. | Canonical presentations cover arbitrary finitary operation theories but add syntax. Compact presentations retain their direct clients. Nonskeletal uniqueness keeps the generator comparison; no strict coproduct of raw chosen theory morphisms is asserted. Increment/doubling and unequal constants separate sum from tensor. |
| [Matroids #620/#628](research/matroid-presentations.md) and [geometric recovery #626](research/geometric-matroids.md) | Circuit elimination derives augmentation; submodularity derives local rank laws. Both reuse the labelled finite-matroid hub and its routes. Geometric recovery uses simplicity and explicit atom relabelling. | Keep standard and local-axiom inputs: convenience depends on which laws are already known. Ground normalization handles arbitrary ambient subsets. Loop/parallel multiplicity controls forbid recovering arbitrary labelled matroids from abstract flat lattices. These are object-type and order equivalences, without a chosen category of matroid morphisms. |
| [Shared Sigma filling #627](research/shared-sigma-filling.md) | First/second filling and primitive pairing/substitution laws derive whole-section uniformity once. Both adapters recover the selected native operation by `rfl`. | Setup and model-specific box laws are paid per model; callers retain their native cap/face hypotheses. Prop-valued boundary witnesses permit the shared congruence proof. Relevant higher witnesses and a cross-model interval bridge are separate obligations. |
| [Rational kernels #635](research/rational-kernel-recovery.md) | Finite additivity and the Markov law derive table normalization from rational singleton masses. Full table/kernel round trips retain composition and coordinate changes. | Native probability inputs trade row-sum proofs for rationality certificates; small direct tables can remain simpler. Choice makes reconstruction noncomputable. Existing executable tables/samplers remain, and equal support does not recover mass, seeds, paths or costs. |
| [Accepted CTB R2](research/textbook-integration.md#current-ctb-continuation-accepted-receiving-integration), `99a2974c`, index `3ac996cc` | Indexed/pairwise sorting agrees without order laws; adjacent order needs transitivity. Lawful counts recover permutation. Set/cache refinement derives laws and histories from operational equations; queue/resource clients retain occurrences and actual execution observations. | Keep positional proofs, cache/order premises and separate stability and cost contracts. The tree-membership reuse repair and weaker left-separator map lemma remove concrete duplication without replacing the algorithms. Source acceptance and runtime extraction retain their separate receipts; later book progress does not enlarge R2's validation scope. |

These results strengthen mathematical capability and remove specified repeated
proofs. The reports record setup and conversion obligations, but provide no
controlled comparison establishing general author productivity. The earlier
matched author trials below retain their narrower evidential scope.

The subsequent classification/descent applications test the same distinction
with arrows and independently supplied local data. [Shared representable
classification](research/shared-representable-classification.md) derives coding
and comparison naturality while native decoders and selected fillers remain.
[Sheaf display descent #667](research/sheaf-display-descent.md) exercises arbitrary,
possibly noninvertible maps independently of torsors. [Torsor and quotient
recovery](research/torsor-stack.md) reuse shared element/slice geometry and
principal-sheaf transport, while actions, target preservation and site hypotheses
retain their own proofs. The [dense chart-site comparison #668](research/site-comparison.md)
adds those hypotheses for an actual alternate site; empty observations lose
distinct stabilizers.

[Ordinary bundle classification #672](research/smooth-bundle-classification.md)
reuses #640's reconstruction and #641's maps/pullbacks, then supplies all-map
categorical recovery, chart-choice and base-change comparisons. Non-Hausdorff,
nontrivial-cover and independent-target consumers retain the original scope.
[Transverse-pullback preservation #97](research/transverse-pullback-preservation.md)
requires additional full-algebra local factorization and sheaf gluing; ordinary
point agreement or full faithfulness alone does not provide stagewise existence.
[Associated bundles #669](research/associated-sheaf-bundles.md) reuse effective
display/torsor descent, retaining arbitrary group homomorphisms, fiber maps,
independent local data and all-map universal properties. Their selected ordinary
regular/singleton comparisons leave general discrete and positive-dimensional
geometry to [#676](https://github.com/VladimirMarko/conaled/issues/676) and
[#677](https://github.com/VladimirMarko/conaled/issues/677), respectively.

The guidance decisions are:

- **Retain** deriving laws from primitive inputs, precise recovery strength,
  information-loss controls and original-client compatibility. The cases above
  exhibit different valid contracts; no one equivalence schema covers them.
- **Make convenience conditional** on the input facts and repeated obligations
  actually removed. Search existing proofs before adding a facade: #634 initially
  missed `FiniteKernelEquality`, and found parser-witness transport already served.
  A connected direct interface can be the better entry point.
- **Keep domain assumptions with their constructions.** Simplicity, rationality,
  selected operations, coverage and site universes justify particular recoveries.
  Retaining a counterexample rejects its specified route, not every richer
  construction. Preserve the interval, multiplicity, mass and cubical controls.
- **Remove stale milestones and reject unsupported migration.** Coherent
  recovery and descent now have accepted implementations. Retaining computational
  specializations and direct algorithms remains justified; no categorical
  wrapper is required for each algorithm. The inspected cases do not show that
  the criteria forced spurious equivalences or migration. They did expose a
  proposed duplicate kernel facade, corrected by searching existing proofs.
  Future textbook/application work can inform another bounded assessment.

### Resource observations and adoption

The [elaboration policy](#elaboration-resource-budgets) is retained. Modest local
allowances and explicit comparison proofs both have successful applications;
failed escalation alone does not establish a mathematical obstruction. Inspect
the complete elaborated statement when changing an encoding so that a cheaper
client still retains its original maps, hypotheses and observations.

| Evidence | Observed result and adopted response |
|---|---|
| [#648/#661 complete clients](research/representable-elaboration-costs.md#complete-client-diagnosis-under-a-separate-process-bound) | Original-async specialization passes all four clients; direct interpretation exhausts heartbeats even unprofiled at depth 1024. Synchronous execution makes both constructor forms fail. Retain the shallow specialization and shared proof; the small wrapper deletion does not justify migration. Record async mode, recursion, heartbeats and process bounds separately. |
| [#665 recovery](research/torsor-stack.md) and [#670 cocycles](research/torsor-cocycle-classification.md) | Two quotient comparisons retain local 400k heartbeats; a different comparison needed named reductions even after a failed 400k trial. Cocycle extraction uses defaults, but larger smooth repeated-comparison consumers failed at 200k/400k/800k; the accepted smaller-site composite and other smooth controls have distinct scope. |
| [#641 maps](https://github.com/VladimirMarko/conaled/issues/641), [#640 reconstruction](https://github.com/VladimirMarko/conaled/issues/640), [#668 site comparison](research/site-comparison.md) | Abstract evaluation/action/transition lemmas removed concrete normalization failures without final budget increases. Direct #641 evaluation and #668 counit trials also failed at 800k; those failures are not passing costs. Shared projection-sheet geometry and comparison laws preserve the original clients. |
| [#606 constructors](research/constructor-recomputation.md) | Four generic Pi/Path composition laws pass at defaults after isomorphism cancellation. A section proof retains 400k and a concrete Cartesian consumer 1.6m; a direct two-step recursion-1024 trial reached its external bound without a Lean result. Full-body comparison remains distinct from the fixed-body equality owned by #671. |
| [#97 realization](research/transverse-pullback-preservation.md), [#672 classification](research/smooth-bundle-classification.md) | #97 retains a measured local 400k allowance for `lift_in_normalOpen`. #672's concrete manually restated comparison failed at 200k/400k; exact `type_of%` specialization passed at defaults with its full type inspected. These are different encodings and constructions, not a controlled cross-design benchmark. |
| [#669 association](research/associated-sheaf-bundles.md#elaboration-costs) | Two extension-descent packaging declarations retain local 400k after 200k failures. Generic cocycle-map extensionality replaces a concrete proof that failed at 200k/400k. The full smooth two-scaling section comparison failed through a 1.6m trial; a kernel-checked opaque pair equal to those exact maps passed at defaults in 1.57s. It retains the original nontrivial torsor, arbitrary stages/sections and both nonidentity maps. Torsor-only opacity failed and was not adopted. |

Passing budgets are not measured minima. Failed runs, warm integrated validation,
fresh compilation and declaration timings cannot be combined into a productivity
ranking. These observations establish neither a Lean bug nor runtime complexity.
Broader tuning or another encoding experiment needs a concrete affected consumer;
this assessment creates no duplicate optimizer programme.

### Earlier author trials and continuing direction

The [preservation architecture assessment](research/preservation-architecture.md)
records a first bounded comparison of direct and shared author routes. Existing
indexed certificates hide dependent equality bookkeeping while preserving the
result type; a simple effect bound remains shorter through its native invariant.
Keep both interfaces available. These checked examples and agent trials inform
specialization design without establishing general human usability or a single
interface for all preservation families.

The [toolkit author trials](research/toolkit-author-effectiveness.md) extend
that evidence to an established DList client and a new reverse-list realization.
Two independent authors retained full sequence and ordered-summary contracts
through direct and shared routes. The record separates successful specialization,
local normalization and audit-harness repairs, and defines #235's repeatable
reassessment protocol without inferring a capability trend from one configuration.

The existing [compiler](../Compiler.lean) and
[first-order compiler](../FirstOrder.lean) provide target-dependent compilation
interfaces. The [internal graph proof](../SquareKit/Internal/Graph.lean) and
[synthetic scalar proofs](../SquareKit/Internal/SyntheticScalar.lean) provide
restricted derivations. The [geometric product rule](../SquareKit/GeometricProductRule.lean)
connects a source derivation to model mathematics. These are sources of design
constraints and checked examples, not evidence that arbitrary Lean arguments
already transport across settings.

[#36](https://github.com/VladimirMarko/conaled/issues/36) owns the constructed
internal-language/model objective. The [internal-language research record](research/internal-languages-lean.md)
tracks its interfaces and evidence. The [compilation extension agenda](extensions.md)
and broader [Felix workstream](https://github.com/VladimirMarko/conaled/issues/8)
supply the other side of this shared direction. Keep scoped acceptance criteria
in GitHub Issues; this document establishes the direction against which those
choices should be assessed, without prescribing a speculative implementation
sequence.

The [2026-10-24 language architecture research](research/language-architecture-research.md)
records the owner's constraints for continued embedded development, the proposed
`slean` dialect and multiple surfaces, Agda reuse, Lean self-modeling, and
composable internal settings. It investigates semantic contracts and low-cost
design tests without selecting a replacement implementation or fixed pipeline.

Landin's [*The Next 700 Programming Languages*](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/landin-next-700.pdf)
separates a common expressive framework from choices of abstract entities and
primitives. The project's ambition extends that separation to the structure
and logical principles supporting programming and proof. This is our design
direction, not a claim that Landin specified the proposed language.

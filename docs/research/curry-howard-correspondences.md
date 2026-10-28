# Curry–Howard correspondences and transport between settings

Research date: 2026-10-28. Local evidence: checkout
`1f1db074eca229cab995591deb2b32db3f899c00`. This is a research assessment and
proposal for bounded experiments, not an adopted architecture or a claim that
all the constructions below are implemented.

Curry–Howard supplies a family of precise connections between proof systems
and typed calculi. Category theory extends this through internal languages and
models; homotopy theory gives dependent identity types geometric meaning.
Linear logic connects further to protocols and resource-sensitive computation.
There are useful connections to topology, physics, linguistics, games, and
verification, but no canonical list of six mutually equivalent subjects.
Each connection needs its own fragment, equations, and preservation contract.
[Proofs and Types](https://paultaylor.eu/stable/Proofs%2BTypes),
[Lambek and Scott](https://assets.cambridge.org/97805213/56534/excerpt/9780521356534_excerpt.pdf),
[HoTT book](https://homotopytypetheory.org/book/),
[Baez and Stay](https://math.ucr.edu/home/baez/rosetta.pdf).

The [logic correspondence atlas](logic-correspondence-atlas.md) extends this
assessment with fragment-by-fragment routes, local and Mathlib reuse, and
contrasting experiments across further logic families.

For conaled, the main opportunity is to make these contracts reusable:
translate an argument or program together with the structure and principles
it needs, then interpret it in another setting. Robert Harper's work fits
this goal particularly through judgments-as-types, typed compilation,
logical relations, phase distinctions, and cost-aware type theory. A useful
first investigation is a bounded proof/program correspondence using existing
compiler syntax; a second is a discrete temporal fragment; a third is modular
representation and cost transport. These priorities are project recommendations,
not conclusions claimed by the cited papers.

## What a correspondence promises

The elementary dictionary is familiar, but its operational part matters:

| Logic | Typed programming | Relevant equation or operation |
|---|---|---|
| Assumptions | Typed variables | Context formation and substitution |
| Implication introduction/elimination | Lambda abstraction/application | Beta reduction removes an introduction followed by elimination |
| Conjunction | Product | Pairing/projection, beta and eta laws |
| Disjunction | Sum | Injection/case analysis |
| Truth / falsity | Unit / empty type | Canonical inhabitant / elimination |
| Universal quantification | Dependent function | Substitution in an indexed result |
| Constructive existential witness | Dependent pair | Witness and its evidence remain available |
| Cut | Substitution or composition | Cut elimination corresponds to computation in the chosen calculus |

This dictionary describes specified constructive systems. General recursion
cannot be added indiscriminately to a logic of total proofs: a fixed point at
every type would inhabit the intended empty type. Classical control has a
computational interpretation, but requires different operators and observational
contracts. [Girard, Lafont, and Taylor, chapters 2–7](https://paultaylor.eu/stable/Proofs%2BTypes),
[Wadler, Propositions as Types](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf).

Use the following distinctions when recording results:

- **Syntactic correspondence:** translations of derivations and terms, with
  inverse laws relative to an explicitly chosen equality. If the two are
  defined as the same inductive family, say that; it is a presentation choice.
- **Sound interpretation:** source derivability implies target validity.
  It does not imply reflection or that every target object is expressible.
- **Completeness or equivalence:** a separate result, relative to specified
  syntax, models, morphisms, and equations. Completeness for all models does
  not imply faithfulness of an arbitrary selected model.
- **Operational simulation:** evaluation or reduction is preserved, possibly
  through several target steps. Type preservation alone does not establish it.
- **Adequacy, full abstraction, and realizability:** distinct requirements
  concerning observable results, contextual distinctions, or computational
  witnesses. None follows from a suggestive dictionary.

These distinctions are a proposed reporting discipline for the project's
existing [transport route](../../GLOSSARY.md) vocabulary. They keep soundness,
reflection, and executable realization separate, as required by
[ADR 0002](../adr/0002-relations-and-synchronization.md) and
[ADR 0010](../adr/0010-composition-and-proof-audit.md).

## Beyond logic and functional programming

| Connection | Precise mathematical content to investigate | Transfer opportunity and boundary |
|---|---|---|
| Curry–Howard–Lambek | Simply typed lambda calculus with products and beta/eta equations has cartesian closed categorical semantics; the syntactic category supplies a free construction. | Interpret shared syntax in different cartesian closed settings. Proving equality in one concrete model need not prove syntactic equality. [Lambek–Scott](https://assets.cambridge.org/97805213/56534/excerpt/9780521356534_excerpt.pdf) |
| Dependent logic and categorical internal languages | Contexts, substitution, dependent types, and quantifiers require dependent categorical structure; higher-order intuitionistic logic has topos interpretations. | Move internal proofs through maps preserving the fragment's structure. Coherence of substitution must be proved. A generic functor does not preserve all quantifiers. [Lambek–Scott](https://www.site.uottawa.ca/~phil/papers/LS11.final.pdf), [van den Berg–Garner](https://research-portal.uu.nl/en/publications/topological-and-simplicial-models-of-identity-types/) |
| Homotopy type theory | Types behave as spaces, terms as points, identities as paths, iterated identities as higher paths, and dependent types as fibrational data. | Transport along paths and equivalences while retaining higher evidence. Univalence relates equivalences to identity in a suitable universe; it does not identify arbitrary spaces or provide a general compiler. [HoTT book, chapters 2 and 4](https://hott.github.io/book/hott-online.pdf) |
| Linear logic and concurrency | Linear propositions can specify sessions; proofs describe communicating processes and cut connects endpoints. | Derive protocol implementations and compose them with proved communication properties. Deadlock/progress results depend on the process calculus and composition discipline. [Wadler, Propositions as Sessions](https://www.research.ed.ac.uk/files/18383989/Wadler_2012_Propositions_as_Sessions.pdf) |
| Topology and quantum processes | Monoidal diagrams describe composition and tensor; cobordisms and linear operators provide different categorical settings. | Interpret the same diagram in multiple models; a topological quantum field theory supplies a functor from a cobordism category to a linear setting. This is not an equivalence of all topology with all physics. [Baez–Stay](https://math.ucr.edu/home/baez/rosetta.pdf) |
| Linguistics | Lambek's ordered type calculus treats grammatical combination through residuals and composition. | Compile derivations to parse witnesses or semantic composition while preserving word order. Exchange, weakening, and contraction cannot be imported silently. [Lambek, The Mathematics of Sentence Structure](https://www.cs.cmu.edu/~fp/courses/15836-f23/misc/Lambek58.pdf) |
| Games and interaction | Strategies give semantic models of programs; suitable games yield full abstraction for PCF. | Compare interactive behavior and contextual equivalence. This is a model theorem for a language, not identification of every strategy with executable code. [Abramsky–Jagadeesan–Malacaria](https://ora.ox.ac.uk/objects/uuid%3A41199322-fb8b-4704-aa1f-7bc479046a2a) |

The topology/physics row and the homotopy row are different connections.
Cobordisms model processes between boundaries; identity types model paths
between points. Likewise, linear logic's tensor and ordinary conjunction have
different structural rules. The project should share operations only where
these distinctions are preserved. This is the central constraint on turning
the table into implementations.

## Transfer routes that should not be missed

The following inventory includes routes adjacent to Curry–Howard. They belong
in the research agenda because they move useful artifacts between domains,
even when they are not proof/type equivalences.

| Route | Artifact transported | Required contract or failure to expose |
|---|---|---|
| Natural deduction ↔ typed terms | Proof objects and programs | Round trips modulo chosen proof/term equations; substitution compatibility |
| Sequent proofs → programs or processes | Cuts, focused derivations, communication | Reduction simulation; evaluation order and process scheduling kept explicit |
| Logical clauses → goal-directed execution | A logic program, query, and answer witnesses | Uniform proofs connect provability with goal-directed search for specified Horn-clause and hereditary-Harrop fragments. This supports logic-programming interpreters and proof-producing query engines; completeness for the chosen fragment does not guarantee termination of a search strategy. [Miller–Nadathur–Pfenning–Scedrov](https://www.lix.polytechnique.fr/~dale/papers/apal91.pdf) |
| Typed syntax → categorical model | Programs and equations | Structure-preserving interpretation; reflection only when separately justified |
| Change of model or base | Internal arguments | Naturality/substitution comparisons and preservation of used connectives |
| Classical proofs → control/CPS | Proofs using classical principles | Translate into a calculus with control or a negative/CPS translation; state answer types and observations. [Griffin](https://www.cl.cam.ac.uk/~tgg22/publications/popl90.pdf) |
| Ordinary → linear calculus | Duplicable functions and data | Make contraction/weakening available through the exponential modality. [Proofs and Types, appendix B](https://paultaylor.eu/stable/Proofs%2BTypes) |
| Effects → monadic or adjoint semantics | Stateful, partial, nondeterministic, or other computations | Preserve evaluation strategy and effects; ordinary total-function beta/eta reasoning can be invalid. [Moggi](https://person.dibris.unige.it/moggi-eugenio/ftp/ic91.pdf) |
| Modal proof → staged program | Time-indexed derivations | Phase-correct substitution, residualization, and stage-respecting evaluation. [Davies](https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf) |
| Specification → reactive program | Constructive temporal proof | Causality, productivity, and any claimed eventual delivery. See the next section. |
| Specification → automaton, monitor, or game | Temporal formula | Trace-language preservation; synthesis additionally requires an implementable winning strategy. [Vardi–Wolper](https://www.cs.rice.edu/~vardi/papers/lics86.pdf) |
| Related implementations → shared client theorem | Representation relation and operation proofs | Fundamental theorem/logical relation, with abstraction respected. [Sterling–Harper](https://arxiv.org/abs/2010.08599v3) |
| Semantic model → normalization procedure | Semantic values and reification | Reification/evaluation correctness, normalization, and decidable equality for the specified fragment. [Sterling's thesis](https://csd.cmu.edu/sites/default/files/phd-thesis/CMU-CS-21-142.pdf) |
| Program → cost or approximation model | Behavior together with quantitative evidence | Equality for behavior may coexist with an inequality or relation for cost; preserve those different orders. [calf](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf), [Decalf](https://arxiv.org/abs/2307.05938) |
| Computational meaning explanation → proof validation | Programs classified by semantic types | A realizability/soundness construction connecting operational behavior to the logic. [Angiuli–Harper–Wilson](https://arxiv.org/abs/1604.08873v2) |

This inventory is a coverage check, not a demand to implement every row now.
For example, effects and algebraic cost already have local consumers, whereas
quantum and linguistic interpretations would need a concrete application to
justify implementation. Differential categorical structure is another local
consumer, but merely calling differentiation a Curry–Howard extension would
not supply the chain rule or an AD preservation proof.

## Which programming language corresponds to temporal logic?

There is no unique answer until the logic and intended observation are fixed.
For **constructive linear-time temporal logic**, modal functional reactive
languages are a direct answer. For a **next-only fragment**, staged lambda
calculi are another. For **classical LTL used as a property language**, automata
and reactive synthesis are often the relevant computational route.

| Intended meaning | Candidate and evidence | What must remain explicit |
|---|---|---|
| Compute now versus at a later stage | Davies's `λ○` and Mini-ML○ connect constructive next-time logic to multi-level binding-time analysis and partial evaluation. [Paper](https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf) | Staging is not automatically a live stream runtime or a wall-clock guarantee. |
| Time-varying values and types | Jeffrey's functional reactive types use discrete-time FRP combinators as constructive temporal proof rules and support streams of types. [Paper](https://asaj.org/papers/lics14.pdf) | Fix time indexing and admissible dependencies; arbitrary functions on complete streams can inspect the future. |
| Productive recursion together with eventual completion | Lively RaTT separates the LTL time-step modality from the guarded-recursion modality, and supports until types, events, and fair streams. [Bahr–Graulund–Møgelberg](https://arxiv.org/abs/2003.03170v2) | Identifying the two modalities admits nontermination where an inductive until type was meant to require termination. |
| Recursive semantics and infinite objects | Sterling and Harper's guarded computational type theory combines guarded recursion with dependent types, clock quantification, and universes. [Paper](https://arxiv.org/abs/1804.09098) | A guarded fixed point establishes the relevant guarded behavior, not every external liveness or fairness property. |
| Check a temporal property of executions | Translate temporal formulas to automata and check accepted traces. [Vardi–Wolper](https://www.cs.rice.edu/~vardi/papers/lics86.pdf) | Verification, satisfiability, and realizability ask different questions. |

As a **proposed discrete, constructive reading**, `next A` supplies `A` at the
next step; `always A` supplies an appropriate continuing family of `A` values;
`eventually A` requires a finite arrival witness and an `A` at arrival; and
`A until B` supplies `A` while waiting and eventually a `B`. The exact types,
contexts, and eliminators must come from the selected calculus. In particular,
an indefinitely pending event cannot count as a witness of eventual arrival.
The separation in Lively RaTT is a design constraint for this proposal,
not an optional implementation detail.

A useful negative example for synthesis is a specification requiring the
current output to equal the next environment input. Some complete traces
satisfy it, but a causal implementation cannot guarantee it against every
unrestricted environment. A satisfying trace therefore does not by itself
supply a reactive program. Similarly, a monitor may detect a safety violation
on a finite prefix while an unbounded eventuality remains unresolved.
These are explanatory examples, not claims about an existing conaled backend.

For this project, start with discrete time and a small next/until fragment.
Keep its clock explicit when connecting it to the existing real-time FRP
specification. A later investigation can compare branching-time logic,
metric time, synchronous circuits, and timed session protocols. This note does
not establish complete language correspondences for those variants.

## What Lean and conaled already formalize

Lean itself uses propositions as types, but its native `Prop` has definitional
proof irrelevance, restricted elimination into data, and runtime erasure.
A proof of `∃ x, P x` is therefore not interchangeable with a computational
`Sigma` witness for extraction. Native equality proofs are also proof-irrelevant;
proof-relevant higher paths must be represented separately.
[Lean reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).

The owner's initial hypothesis needs this qualification: the repository already
formalizes parts of the correspondence explicitly, although it does not thereby
supply a packaged general equivalence between logic, programs, categories,
and homotopy theory.

| Local evidence | Existing capability | Boundary for this research |
|---|---|---|
| [Compiler.lean](../../Compiler.lean) | Intrinsically typed `Term : Ctx → Ty → Type`, target-parametric compilation, and semantic soundness | The `Sound` interface supplies a Set-valued meaning; it is not a proof that every cartesian closed category is faithfully represented. |
| [STLC naturality](../../SquareKit/STLCNaturality.lean), [STLC relations](../../SquareKit/STLCRelations.lean) | Full-source naturality and relational compilation preservation, including related inputs at function types | Reuse these theorems; the new question is proof relevance, modal abstraction, or a new observation contract, not rebuilding basic logical relations. |
| [Internal logic](../../SquareKit/Internal/Logic.lean), [graph proofs](../../SquareKit/Internal/Graph.lean) | Explicit internal derivations and model soundness, including graph forward/backward reasoning | `Derives` in the logic is `Prop`-valued. It supplies validity evidence, not a freely inspectable computational proof tree in `Type`. |
| [Dependent functions](../../SquareKit/Internal/DependentFunctions.lean), [dependent examples](../../Examples/DependentSource.lean) | Bounded dependent source/model developments | A correspondence theorem must name the supported substitution, equality, and dependent constructors. |
| [Groupoid identity](../../SquareKit/Internal/PathTransport/GroupoidIdentity.lean), [second identity examples](../../Examples/SecondIdentity.lean) | Explicit higher-identity and groupoid-related structures | These are bounded models and examples, not native Lean univalence or a universal HoTT compiler. |
| [FRP specification](../../Applications/FRP/Spec.lean), [traces](../../Applications/FRP/Trace.lean) | Real-indexed behaviors, locally finite events, prefix/refinement and execution contracts | `Behavior α := ℝ → α` and offline time warping do not enforce causality. `Event.never` precludes identifying all events with constructive eventualities. |
| [Resources examples](../../Examples/Resources.lean), [potential accounting](../../Applications/Resources/Potential.lean) | Resource composition and generic `run_potential`, `run_potential_exact`, and `run_constant_charge` theorems | Basic potential telescoping already exists. New work should address abstraction, noninterference, or persistence discipline; modeled cost does not automatically describe allocation or wall-clock runtime. |

A useful explicit Curry–Howard development would therefore add missing
**theorems about a chosen correspondence**, not reprove that Lean accepts
`fun x => x : A → A`. Candidate obligations are proof/program translations,
substitution compatibility, inverse laws modulo equations, and reduction
simulation. If proof trees are computational artifacts, represent them in
`Type`, or construct program witnesses independently and relate them to the
existing `Prop` judgment. Merely relabeling `Derives` cannot recover erased
proof distinctions.

## Robert Harper: what to absorb and what needs adaptation

Harper's work is a corpus, not a single framework to adopt wholesale. The
following reading order is chosen for current project needs. The fit judgments
and proposed adaptations are ours.

| Work | Useful contribution | Fit and adaptation |
|---|---|---|
| [Practical Foundations for Programming Languages, second edition](https://www.cs.cmu.edu/~rwh/pfpl/) | Organizes languages around judgments, statics, dynamics, and type structure. | Use as a design discipline for bounded embedded languages: say what is a judgment, what computes, and what equality means. It is not itself the project's categorical transport architecture. Consult the author's errata when formalizing an example. |
| [Harper–Honsell–Plotkin, A Framework for Defining Logics](https://publish.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-23/index.html) | LF encodes judgments as types and derivations as inhabitants, with dependent types supporting binding and hypothetical judgments. | Closest foundational reference for object logics in Lean. Require an adequacy theorem relating the chosen encoding to intended judgments. Borrow the method without assuming an LF implementation or higher-order abstract syntax ports directly into Lean inductives. |
| [Typed Closure Conversion](https://www.cs.cmu.edu/afs/cs/project/fox/mosaic/papers.html) and [Compiling Polymorphism Using Intensional Type Analysis](https://dash.harvard.edu/bitstreams/7312037c-54af-6bd4-e053-0100007fdf3b/download) | Typed intermediate languages retain information across representation changes; closure conversion separates code from environments. | Study when the graph emitter grows higher-order or representation-sensitive features. Keep typing and semantic preservation as separate obligations; these papers do not make every type-preserving compiler behavior-preserving. |
| [Sterling–Harper, Logical Relations as Types](https://arxiv.org/abs/2010.08599v3) | Proof-relevant parametricity and phase-separated module reasoning; related implementations can be assembled using a third implementation carrying representation evidence. | Direct fit for reusable relational backends and abstraction boundaries. Preserve witness data when proof relevance matters; ordinary `Prop` relations alone do not reproduce the full construction. |
| [Niu–Sterling–Grodin–Harper, calf](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf) | Dependent cost reasoning uses a phase distinction separating cost from behavior and an internal noninterference principle. | Compare one existing resource example with a cost-aware interpretation. Ask which client proofs can be reused when cost changes but behavior does not. This is a proposed adaptation, not a claim of a current modal calf model in Lean. |
| [Grodin–Niu–Sterling–Harper, Decalf](https://arxiv.org/abs/2307.05938) | Directed cost comparison supports effectful computations; a bound can itself be a program, with behavior agreeing in the behavioral phase. | Relevant to probabilistic and higher-order resource contracts. Begin with an explicit ordered model and its composition laws; retain effect semantics when comparing costs. |
| [Grodin–Li–Harper, Abstraction Functions as Types](https://arxiv.org/abs/2502.20496v4), POPL 2026 | Modal fracture/gluing packages concrete implementation, abstract behavior, and their abstraction map; a sealing effect supports modular cost bounds. | Especially close to semantic squares. First reconstruct a small explicit abstraction-map example. The paper assumes univalent dependent type theory; its entire internal theory is not available merely because Lean has structures and quotients. |
| [Sterling–Harper, Guarded Computational Type Theory](https://arxiv.org/abs/1804.09098) | A language and metalanguage for recursive and infinite computational objects. | Relevant to FRP and recursive semantic models; compare clock and guarded-context requirements with a temporal fragment before sharing an interface. |
| [Angiuli–Harper–Wilson, Computational Higher Type Theory I](https://arxiv.org/abs/1604.08873v2) | Cubical realizability connects higher-dimensional type structure with computation. | Study computational meaning explanations for the higher-identity work. Adapting a bounded object model respects Lean's checker; replacing host equality or adding univalence as a host axiom does not. |
| [Sterling, First Steps in Synthetic Tait Computability](https://csd.cmu.edu/sites/default/files/phd-thesis/CMU-CS-21-142.pdf), supervised by Harper | Uses categorical/gluing methods for dependent-type metatheory, including normalization. | A later route from model structure to elaboration or normalization algorithms. First identify which existing fragment needs that theorem; avoid constructing a general metatheory without a consumer. |

Two July 2026 preprints deserve follow-up rather than silent omission:

- [Potential Functions as Types, v2](https://arxiv.org/abs/2607.08547v2)
  connects abstraction/potential functions, credit/debit type operators, and a
  graded substructural language, Giralf, interpreted in Calf. Its inference
  result covers a limited class of programs. Assess one amortized data structure
  against existing resource contracts before adopting its language machinery.
- [Directed proof-relevant logical relations in simplicial HoTT, v1](https://arxiv.org/abs/2607.08154v1)
  separates directed reduction from equality and relational comparison using
  simplicial type theory. This may inform reduction-aware transport, but its
  directed quotient syntax and modal assumptions require a separate model
  assessment; the abstract is not evidence of a Lean port.

The [PFAT artifact guide](https://www.cs.cmu.edu/~runmingl/pfat/README.html)
reports Agda 2.8.0, standard library 2.3, and cubical library 0.9. Its modules
cover fracture/gluing, squares, potential functions, a batched queue, and Giralf
embedded in Calf. This is concrete implementation evidence to inspect, not a
port-ready Lean dependency; no artifact build was run in this research.

The publication status and version labels above follow the authors' records
and arXiv metadata as checked on the research date. The preprints were surveyed
for their stated contributions; their full metatheory and artifacts have not
been audited here. [Harper's current papers](https://www.cs.cmu.edu/~rwh/index.html),
[author-maintained calf bibliography](https://www.cs.cmu.edu/~runmingl/calf.html).

The main compatibility boundary is foundational. Conaled keeps Lean as host
and checker and audits additional axioms. Harper's techniques can inform
explicit syntax, semantic models, and proof interfaces without importing every
principle of their source type theories. The [language direction](../language-direction.md)
already calls for settings to expose their admissible reasoning. The proposed
experiments follow that direction and do not require reversing an ADR.

## A reusable transport contract

For a proposed route `T : Source → Target`, record the following as separate
fields or theorems. This is a design checklist, not a proposed universal Lean
structure to implement before there are examples.

1. **Fragment and requirements.** Context rules, type/term constructors,
   logical principles, universes, effects, clock rules, and permitted axioms.
2. **Judgments and witnesses.** What is translated: syntax, typing, equality,
   reduction, satisfaction, or proof-relevant evidence? Identify any erasure.
3. **Substitution.** The comparison between translating a substitution and
   substituting translated terms, including coherence for dependent types.
4. **Meaning.** A semantic map or relation and a theorem connecting
   `meaningTarget (T t)` with `meaningSource t`. Use equality, isomorphism,
   a directed inequality, or a relation according to the actual contract.
5. **Operations and observations.** Reduction simulation, termination,
   productivity, causality, or contextual behavior where claimed. State which
   events or resources are observable and which assumptions ensure progress.
6. **Strength and composition.** State preservation separately from reflection,
   completeness, inverse laws, and full abstraction. Prove route composition
   only when intermediate meanings and comparisons align.

A cartesian source that duplicates a variable cannot target a purely linear
setting without extra structure. A constructive witness cannot be recovered
from erased existence evidence by renaming a type. An equality between outputs
does not imply equal resource use. These are useful negative cases because
they reveal the exact additional requirement that a transport route needs.

## Prioritized experiments and decision criteria

These experiments are proposals. Their deliverables should become scoped
GitHub Issues only after their boundaries are selected; this research does not
create tracker commitments.

| Priority | Bounded experiment | Evidence that would justify further work |
|---|---|---|
| First | Products and implication: relate explicit natural-deduction proof objects to the relevant existing typed-term fragment. | Type-preserving translations, substitution lemma, round trips modulo named equations, and beta/cut simulation. Reuse one construction in two independently supplied interpretations. Show a target missing required structure is rejected explicitly. |
| First | Discrete temporal fragment with next and a terminating until/event witness. | A causal stream transformation plus a finite-arrival example; a never-arriving event fails the liveness contract. State how its observation relates to current real-time FRP. Keep guarded recursion separate if added. |
| Next | One abstract data type with two concrete representations and a shared client proof, informed by Logical Relations as Types and Abstraction Functions as Types. | Representation invariance, composition of operation contracts, and reuse without exposing implementation details. Compare caller effort with the current relational-square interface. |
| Next | Add modular cost abstraction to that example, reusing existing potential-accounting proofs. | Same behavior with distinct costs; a proved bound composes through clients without revealing private potential. A second linear-history telescoping proof alone adds no new capability; persistent branching needs its own resource discipline. Separate a direct ordered-model reconstruction from any claim of realizing all Calf/Decalf modalities. |
| Then | One linear/session protocol interpreted as a process and a trace contract. | Dual endpoint composition and the precise progress theorem supported by the chosen calculus. Include a composition that would require extra sharing or recursion rules. |
| Then | Compare a new proof/program interpretation with the existing groupoid transport routes. | Reuse existing transport, concatenation, substitution, and route composition from [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean); test an additional interpretation and exhibit information lost by replacing path witnesses with mere equality or orbit sets. Do not require univalence for a claim that only needs groupoid structure. |
| Consumer-driven | A staged specialization or normalization backend, and a temporal monitor route. | Stage-correct residual code or a proved normalizer; separately, formula-to-monitor trace soundness. Neither result is mislabeled as reactive synthesis. |

Success should be measured against the [author-facing design tests](../language-direction.md):
can a user state the mathematical construction once, see its requirements,
and reuse it without managing encoded syntax throughout the proof? A correct
translation that adds repetitive derivation-tree work may be an intermediate
result, but it does not meet that interface goal by itself.

## Reading sequence and unresolved questions

Read **Proofs and Types, chapters 2–5**, then **Lambek–Scott's categorical
lambda-calculus material** for the initial proof/program/model triangle.
Read **LF** and the relevant **PFPL** chapters while designing the first
bounded syntax. For FRP, read **Jeffrey** and **Lively RaTT** together; use
**Davies** to keep staging in view. For reuse and cost, read **Logical Relations
as Types**, **calf**, **Abstraction Functions as Types**, then **Decalf**.
The HoTT book and computational higher type theory belong beside the local
higher-identity work, with their foundation assumptions written down explicitly.

The remaining questions are concrete: which existing syntax fragment is the
best initial carrier, which proof equations users need to observe, whether
program witnesses should be separate from current validity judgments, which
clock/observation connects temporal syntax to current FRP, and how much of
Harper's modal abstraction discipline can be reconstructed over existing
squares before introducing additional language machinery. These require
checked examples and statement review, not a larger dictionary alone.

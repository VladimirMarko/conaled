# Logic fragments, computational interpretations, and transport routes

Research for [issue #201](https://github.com/VladimirMarko/conaled/issues/201),
within [#200](https://github.com/VladimirMarko/conaled/issues/200).
Evidence checked 2026-10-28 against conaled
`c4f469dd2dfdf4dce471fb355b9ab478d3d62dd5`, Lean 4.35.0, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

This atlas answers a narrower question than “which language corresponds to
this logic?”: **which fragment, which artifact, which translation, and which
theorem?** A formula can classify a proof term, direct proof search, describe
executions, or constrain an implementation. These uses yield different routes.
Temporal logic is one family among the entries below.

The [initial Curry–Howard assessment](curry-howard-correspondences.md) supplies
the introductory dictionary and Harper reading plan. This document adds
contrasting families, explicit classification axes, a declaration-level reuse
map, and follow-up scopes. It proposes no universal AST, mandatory compilation
pipeline, kernel extension, or package split. Missing entries are uninvestigated,
not impossible. Entry identifiers are stable handles for adding evidence;
they are not names of new library abstractions.

## Reading and extending an entry

Each entry records a **fragment/profile**, **counterpart**, **direction and
strength**, **assumptions or exclusions**, and **local reuse/gap**. The source
link identifies the primary paper, author-hosted book, or formal source file;
section/theorem locators identify the result being used. Published years refer
to the work, not a search engine's crawl date. Versioned arXiv links identify
the surveyed preprint; other linked copies were checked on the date above and
may subsequently change. Historical papers are evidence for their stated
systems, not assertions that their algorithms are today's best implementations.

For additions, keep the independently variable fields below, name the exact
source theorem or construction, and identify an observation that the route
preserves or forgets. Record a negative case or a boundary example. A new
semantic model alone must not be relabeled as extraction or full abstraction.
The local map is a scoped source inspection, not an exhaustive search of all
Lean libraries or a fresh build of external artifacts.

| Route kind | What is produced | Strength to record separately |
|---|---|---|
| Proof construction | A derivation with a computational term | Typing, substitution, reduction simulation, normalization, inverse laws |
| Proof search / logic programming | A successful derivation and answer substitution | Soundness and completeness of the search discipline; termination and a concrete search strategy are additional claims |
| Interpretation | A semantic object, arrow, predicate, or strategy | Soundness; faithfulness/reflection and definability/fullness are additional claims |
| Model checking | A truth decision or certificate for a specified model | Agreement with satisfaction; no program synthesis follows |
| Synthesis | An implementation or winning strategy | Realizability against the stated environment and observation discipline |
| Extraction | Executable witness data obtained from a proof | Computational adequacy and erasure assumptions, not just provability |
| Refinement / approximation | A new implementation, abstract state, or bound | Which direction of simulation or order is preserved; exactness is optional |

## Independent classification axes

Families overlap. A language may be dependent, affine, effectful, and temporal
at once. The following are fields of a comparison, not mutually exclusive
categories. These axes follow the rule presentations in the sources cited in
the entries; their selection here is a project design proposal.

| Axis | Questions that change the contract |
|---|---|
| Structural rules | Is exchange allowed? Can assumptions be discarded or duplicated? Are these permissions global, per context, or controlled by a modality/grade? |
| Connectives | Implication versus linear implication; cartesian versus tensor product; additive versus multiplicative choice; quantifiers and their domain restrictions |
| Dependency | Do types depend on terms? Does substitution act on types and contexts? Which variables may appear across modal boundaries? |
| Equality and proof relevance | Definitional reduction, propositional equality, beta/eta congruence, contextual equivalence, paths, bisimulation, or a directed preorder? Are witnesses retained? |
| Universes | No type quantification, predicative universes, impredicative polymorphism, or univalence? Is a “type of all types” being mistakenly assumed? |
| Recursion and effects | Total induction, guarded/corecursion, arbitrary fixed points, state, control, probability, nondeterminism; which evaluation strategy? |
| Time and information | Discrete/dense, linear/branching, finite/infinite traces; clock divergence; causal dependency; agent observations; adversarial versus probabilistic choice |
| Logical principles | Intuitionistic/classical, excluded middle, choice, extensionality, proof irrelevance, identity reflection; object theory versus Lean metatheory |

For the simple resource profiles used below, **U** allows exchange, weakening,
and contraction; **L** allows exchange only; **A** also allows weakening;
**R** also allows contraction; **O** preserves order and allows neither
weakening nor contraction. These are context disciplines, not a classification
of every logic called “relevant” or “ordered.” Additive branching and modalities
require their own rules. In dependent contexts, exchange is permitted only
when dependencies remain well-formed.

## Proof objects, predicates, and internal languages

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| P1. Intuitionistic propositional natural deduction: `→, ∧, ∨, ⊤, ⊥`; U, proof-relevant terms, no general recursion | Simply typed lambda calculus with functions, products, sums, unit and empty type. [Girard–Lafont–Taylor, *Proofs and Types* (1989/1990), chapters 2–5 and 10](https://paultaylor.eu/stable/Proofs%2BTypes) gives proofs-as-terms and normalization. | Derivations ↔ typing derivations for the selected presentation; elimination of an introduction detour ↔ computation. Quotient by specified conversions before claiming inverse equality. Arbitrary fixed points would invalidate the empty-type interpretation. | L1 supplies substantial typed syntax and interpretations, but not an explicit natural-deduction translation, syntactic substitution/reduction theorem, or proof of normalization. |
| P2. Intuitionistic predicate logic interpreted constructively; U with term-dependent families, `∀, ∃` | Dependent functions and dependent pairs in [Martin-Löf, *Intuitionistic Type Theory* (1984), propositions, contexts, `Π` and `Σ` rules](https://www.cse.chalmers.se/~peterd/papers/MartinL%C3%B6f1984.pdf). | A proof of `∀x:A. B(x)` acts on an input; a constructive `Σx:A. B(x)` retains witness and evidence. This is an interpretation in the specified constructive type theory, not identification of every first-order formula with every dependent type. Universes and identity rules must be chosen explicitly. | L2 has only a bounded logical/dependent fragment. Host `Exists : Prop` is not a computational `Sigma`. |
| P3. Classical propositional implication and falsity; U plus classical control | Typed Idealized Scheme in [Griffin, *A Formulae-as-Types Notion of Control* (1990), sections 3–4](https://www.cl.cam.ac.uk/~tgg22/publications/popl90.pdf). | Classical proof rules acquire control operators; typed evaluations in the paper terminate. Control/CPS changes the computation and answer context. This is not a translation of excluded middle to a pure terminating function that decides arbitrary predicates. | L1 offers a pure term carrier, not control syntax, continuations, or a CPS simulation. |
| P4. Classical first-order predicate calculus, including quantification over individuals | Relational structures and semantic validity. [Gödel, *Die Vollständigkeit der Axiome des logischen Funktionenkalküls* (1930)](https://link.springer.com/article/10.1007/BF01696781) establishes completeness for first-order logic; the original finite/countable setting is sufficient here. | Provability ↔ validity over the relevant class of nonempty structures. This is semantic completeness, not an algorithm deciding validity, and not extraction of witnesses from arbitrary classical existence proofs. A general classical predicate proof-to-control calculus is a further route, not established by this entry. | M1 provides first-order syntax, substitution, realization and semantic compactness. Its model-theoretic results must not be called a local proof-term extraction interface. |
| P5. Product/arrow type theories modulo beta/eta; dependent extensions separately | Cartesian closed internal languages; dependent products as right adjoints to pullback. [Lambek–Scott, *Introduction to Higher Order Categorical Logic*, Part I](https://books.google.com/books?id=6PY_emBeGjUC); [Seely, *Locally cartesian closed categories and type theory* (1984), section 4](https://math.mcgill.ca/rags/LCCC/LCCC.pdf). | Syntax → model is sound under its structural laws. Free/syntactic categorical constructions justify a correspondence of theories and structured categories, not faithfulness of every selected model. Dependent interpretation additionally needs coherent substitution; chosen pullbacks alone do not prove strict coherence. | L1/M2 already give operations, maps and closure. L2 covers particular dependent/sheaf comparisons. A universal dependent-language equivalence is not present in these modules. |
| P6. Intensional identity types, dependent contexts and universes; higher identities retained | Paths, equivalences, transport and higher groupoidal structure. [*HoTT Book* (2013), chapters 2, 4 and 6](https://hott.github.io/book/hott-online.pdf). | Type-theoretic constructions have homotopical interpretations; univalence relates equivalences to identities in a suitable universe, with higher inductive types additional structure. This is not an equivalence between all topological spaces and Lean's native types. | L3 retains arrows/2-cells as explicit data. Lean equality is proof-irrelevant; no native univalence, unrestricted higher inductives, or general HoTT interpretation is supplied. |
| P7. Deductive systems with binding/hypothetical judgments | LF's judgments-as-types. [Harper–Honsell–Plotkin, *A Framework for Defining Logics* (1987 report; JACM 1993)](https://publish.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-23/index.html). | Object derivations → inhabitants of a dependent logical framework; an adequate encoding relates canonical inhabitants back to intended derivations. Adequacy is specific to the encoded system. Framework type checking alone does not establish that the encoding expresses the intended logic. | L2 is an existing object-language seam. A new encoding should prove its adequacy and preserve ordinary Lean interfaces; adopting LF's binding representation wholesale is not required. |

The full first-order completeness paper P4 is bibliographically verified via
the publisher; its scanned full text was not available in this web session.
The entry records the classical completeness result at its stated level,
without importing an uninspected constructive proof or modern generalization.
P5's book link is the authors' publisher-supplied description; dependent
interpretation details were checked in Seely's paper. For strict substitution
and higher identity, the coherence issue is supported separately by
[van den Berg–Garner, *Topological and Simplicial Models of Identity Types* (2012)](https://research-portal.uu.nl/en/publications/topological-and-simplicial-models-of-identity-types/).

## Resource-sensitive proofs, processes, and proof search

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| S1. Classical linear propositions with session constructs; L and explicit exponentials | CP process calculus and GV functional sessions. [Wadler, *Propositions as Sessions*, JFP version, sections 3–4](https://www.research.ed.ac.uk/files/18383989/Wadler_2012_Propositions_as_Sessions.pdf). | Proofs become processes; cut connects dual endpoints and cut reduction realizes communication. The GV→CP translation preserves typing. Progress/deadlock claims apply to the paper's disciplined composition, not arbitrary process graphs, added recursion, or a deployed scheduler. | L1's cartesian variable reuse cannot be assumed linear. L4's traces can be observations for a future process interpretation; neither is already CP/GV. |
| S2. Affine and relevant resource qualifiers; A and R independently, alongside U/L, polymorphism and mutable references | `λURAL` and its control-effect extension in [Tov–Pucella, *A Theory of Substructural Types and Control*, author long version, sections 3–5](https://users.cs.northwestern.edu/~jesse/pubs/substructural-control/CtlURAL-long-bw.pdf). | A permits dropping but not duplication; R permits duplication but not implicit dropping. A parameterized continuation-composing translation preserves typing; Theorem 5.10 proves safety under section 5.3's parameter properties. Source operational semantics is defined through the translation. | A concrete programming interpretation for both disciplines, not an equivalence with every relevant logic. “Used” need not mean eventual runtime consumption in a diverging program. L5's numeric accounting does not enforce these context rules. |
| S3. Associative ordered Lambek calculus, nonempty antecedents; O, product and left/right residuals | Categorial grammar and ordered composition. [Lambek, *The Mathematics of Sentence Structure* (1958), calculus and cut-elimination sections](https://www.cs.cmu.edu/~fp/courses/15836-f23/misc/Lambek58.pdf). | Grammatical derivations compose typed words; cut is admissible. Residuation supplies algebraic interpretations. Do not silently add empty contexts, exchange, or unrestricted copying, and do not infer a complete account of natural language. | L6 has finite-word recognition, but regex recognition is not a proof of Lambek derivability. An adapter must retain ordered derivations and their interpretation. |
| S4. First-order and higher-order Horn clauses; hereditary Harrop extensions | Goal-directed logic programming, including the logical basis of Prolog-like search and `λProlog`. [Miller–Nadathur–Pfenning–Scedrov, *Uniform Proofs as a Foundation for Logic Programming* (1991), Theorem 1 and sections 4–6](https://www.lix.polytechnique.fr/~dale/papers/apal91.pdf). | For the specified program/goal grammars, provability ↔ existence of a uniform proof. Horn results admit classical provability; hereditary Harrop results use intuitionistic/minimal provability. This is completeness of a proof discipline, not termination or completeness of depth-first Prolog with cut. | L2 has substitution machinery but no inspected uniform-proof engine. An implementation would need search scheduling and answer-witness contracts, beyond sound object derivations. |
| S5. First-order multiplicative/additive linear logic with equality and positive least/greatest fixed points (`μMALL`); no exponentials | Focused proof search with induction/coinduction. [Baelde, *Least and Greatest Fixed Points in Linear Logic*, v4 (2010), normalization and focusing results](https://arxiv.org/abs/0910.3383v4). | Weak normalization and a complete focused proof system for that logic. Neither strong normalization of arbitrary execution nor general-purpose decidable search follows. Fixed-point positivity and invariant/coinvariant obligations matter. | M3 supplies semantic fixed points; it does not implement this calculus or its focused proof certificates. |

The common resource words hide different contracts. Linear algebra in the
matrix backend means additivity/scalar compatibility, not linear use of a
variable. A tensor-based process language therefore needs its own resource
context even if its denotation eventually uses matrices.

## Modal reasoning, staging, effects, and knowledge

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| D1. Constructive necessity/possibility and lax modality, separated valid/ordinary hypotheses | Dual-context modal terms and monadic metalanguage. [Pfenning–Davies, *A Judgmental Reconstruction of Modal Logic*, May 2000 manuscript, sections 4–8](https://www.cs.cmu.edu/~fp/papers/mscs00.pdf). | Judgmental presentations characterize the selected intuitionistic modal principles; proof terms give a computational interpretation, including lax logic's monadic reading. Box introduction cannot depend on arbitrary ordinary hypotheses. Different Kripke frame conditions do not all induce this calculus. | M2's adjunctions are semantic ingredients; L2's ordinary substitutions need a modal restriction, not merely another unary formula constructor. |
| D2. Constructive next-time fragment for binding time | `λ○` and Mini-ML○. [Davies, *A Temporal-Logic Approach to Binding-Time Analysis* (1996)](https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf). | Next-time typing corresponds to multi-level binding-time analysis; time-ordered normalization and operational binding-time correctness justify residualization. Stages are evaluation phases, not physical seconds or delivery deadlines. | L1 could carry a chosen staged extension, but current emitter correctness does not establish staging or a partial evaluator. |
| D3. Computational lambda calculus with a computation type `T A`; effects explicit | Strong-monad semantics. [Moggi, *Notions of Computation and Monads* (1991), computational metalanguage and categorical models](https://person.dibris.unige.it/moggi-eugenio/ftp/ic91.pdf). | Syntax → a selected computational model preserves its equational theory. Different monads express different effects; ordinary value-level beta/eta equations cannot automatically be applied to effectful computations. No equivalence of all monadic effects is claimed. | M2 supplies categorical infrastructure and L7 kernel composition, but neither gives a generic host-effect transport theorem. Compare call-by-value versus call-by-name before sharing an equation. |
| D4. Multi-agent epistemic logic, individual/group/common knowledge; classical satisfaction over runs and local histories | Distributed-system knowledge semantics. [Halpern–Moses, *Knowledge and Common Knowledge in a Distributed Environment* (1990), sections 3–8](https://www.cs.cornell.edu/home/halpern/papers/common_knowledge.pdf). | Protocol executions → an indistinguishability model in which knowledge assertions are evaluated. Their coordination/impossibility results depend on communication and observation assumptions. This is a program-analysis semantics, not a canonical language whose programs are proofs of S5. | L8's universal observation-fiber predicate is a useful ingredient. It lacks agents, admissible-run models, common-knowledge closure, and a protocol correspondence. |
| D5. Propositional spatial logic for finite trees: composition, its residual, and unit | Tree satisfaction, sound/complete sequent calculus, and decision procedure. [Calcagno–Cardelli–Gordon, *Deciding Validity in a Spatial Logic for Trees* (2003)](https://www.microsoft.com/en-us/research/publication/deciding-validity-in-a-spatial-logic-for-trees-2003/). | For this bounded language, satisfaction and validity are decidable and the calculus is complete for the tree interpretation. Spatial composition describes pieces of a tree; it is not automatically Euclidean geometry, a heap, or a concurrent process. | L6 offers finite-word observations, not this tree model. No inspected local spatial formula satisfaction or decision theorem realizes this paper. |

D1 and D4 are deliberately separate: constructive necessity disciplines
available assumptions, whereas epistemic knowledge quantifies over states an
agent cannot distinguish. The same box notation would conceal that difference.
Spatial logics also require a specified composition operation and resource
model; using the project's geometric libraries does not itself supply one.

## Temporal variants, automata, and semantic fixed points

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| T1. Constructive discrete linear time with time-indexed types | Functional reactive types. [Jeffrey, *Functional Reactive Types* (LICS 2014)](https://asaj.org/papers/lics14.pdf). | FRP combinators serve as constructive temporal proof rules and define streams of types. This is the paper's discrete-time interpretation, not a license for arbitrary future-reading stream functions. | L4 contains real-indexed behaviors and separate observation contracts. A discrete clock and causality bridge are missing. |
| T2. Guarded recursion plus inductive until/eventuality | Lively RaTT. [Bahr–Graulund–Møgelberg, *Diamonds Are Not Forever*, v2 (2020)](https://arxiv.org/abs/2003.03170v2). | The LTL step is a submodality of the guarded-recursion step; the calculus supports liveness while retaining guarded recursion. Equating the modalities destroys intended termination of until types. | L4's `Event.never` cannot be a constructive eventual-arrival witness. Existing progress assumptions can be observations to compare, not omitted requirements. |
| T3. Classical propositional LTL on infinite words | Automata-theoretic verification. [Vardi–Wolper, *An Automata-Theoretic Approach to Automatic Program Verification* (LICS 1986)](https://www.cs.rice.edu/~vardi/papers/lics86.pdf). | Formulas → automata accepting their satisfying executions; verification becomes an automata problem. A satisfying word is not a causal strategy against all environment inputs. Finite-word recognizers alone do not implement omega acceptance. | L6/M4 give finite-word machinery; Büchi/parity acceptance and its formula translation need separate evidence. |
| T4. Branching-time CTL on finite transition graphs, with path quantifiers | State-labeling model checker. [Clarke–Emerson–Sistla, *Automatic Verification of Finite-State Concurrent Systems Using Temporal Logic Specifications* (1986), section 3](https://ix.cs.uoregon.edu/~michal/Classes/04u/fsv/readings/ClarkeEmersonSistla-86.pdf). | Model + formula → satisfaction decision, with correctness and complexity for the given finite graph representation. Fairness extensions need the stated fairness conditions. It neither synthesizes a scheduler nor identifies CTL proofs with ordinary FRP terms. | M3 gives fixed-point semantics; L4 supplies trace contracts, but no inspected CTL syntax/checker. |
| T5. Dense-time MITL with non-punctual interval constraints | Timed-automata verification. [Alur–Feder–Henzinger, *The Benefits of Relaxing Punctuality* (1996)](https://www.cis.upenn.edu/~alur/JACM96.pdf). | The paper establishes decidability/EXPSPACE-completeness for its dense-time logic and an automata-based verification method. Its exclusion of punctual constraints matters; a theorem for this semantics is not a blanket theorem about every MTL variant, finite timed word, or sampled trace. | L4's real time and timing intervals do not provide timed automata or this satisfaction relation. Clock divergence and signal/event semantics require explicit matching. |
| T6. Modal `μ`-calculus, positive least/greatest fixed points on transition systems | Disjunctive formulas and modal automata. [Janin–Walukiewicz, *Automata for the Modal μ-Calculus and Related Results* (1995)](https://www.labri.fr/perso/igw/Papers/igw-mu-aut.pdf). | Every formula has a semantically equivalent disjunctive form; corresponding automata characterize expressive power over transition systems. This is a satisfaction/expression theorem, not extraction of a total function from each fixed-point formula. | M3 provides monotone least/greatest fixed points. Positivity checking, formula semantics, automata acceptance and preservation remain new obligations. |
| T7. Reactive-module synthesis from LTL specifications, finite input/output domains | Programs constructed through Rabin tree automata. [Pnueli–Rosner, *On the Synthesis of a Reactive Module* (1989), publisher abstract](https://doi.org/10.1145/75277.75293). | Existence of a realizing program is characterized by validity of a quantified branching-time formula; finite domains admit a construction algorithm. This includes environmental input branching, unlike finding one satisfying word. | L6/M4 finite-word recognition is insufficient. Timing/observation conventions and the full strategy construction require further audit before implementing this route. |

T7 records the result at the publisher abstract's scope. It does not select a
Mealy/Moore timing convention or claim a local synthesis backend. The complete
construction and its assumptions remain a follow-up; T4's checker alone does
not supply it.

## Hoare, separation, dynamic, and probabilistic reasoning

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| V1. Propositional Hoare logic for while-program partial correctness | Relational program semantics and inference rules. [Kozen–Tiuryn, *On the Completeness of Propositional Hoare Logic*, abstract and introduction](https://ecommons.cornell.edu/server/api/core/bitstreams/c66d7eea-b379-4f26-b633-f69f3e43e4fa/content). | Relationally valid rules are derivable under the paper's expressiveness conditions; the atomic-premise case needs no such assumptions. Partial correctness constrains terminating outcomes, not termination itself. | L8 already gives a Galois connection and sequential predicate transport. It does not yet supply this Hoare syntax or relative-completeness proof. |
| V2. Heap separation logic with `emp`, points-to, separating conjunction/implication and imperative commands | Local reasoning about disjoint heap regions. [Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures* (LICS 2002), assertions and inference rules](https://www.cs.cmu.edu/~jcr/seplogic.pdf). | Hoare-style derivations imply safety/correctness in the chosen heap semantics; framing requires its locality and variable side conditions. Resource composition is partial/disjoint, unlike cartesian conjunction. Recursive predicates do not alone yield a complete automatic prover. | L8 is an underlying relation/predicate seam, but no separation algebra, heap ownership model, or frame-rule theorem is established by it. |
| V3. Propositional dynamic logic of regular programs: sequence, choice, iteration, test | Kripke relational semantics with program-indexed modalities. [Parikh, *A Completeness Result for a Propositional Dynamic Logic* (1978 report)](https://dspace.mit.edu/entities/publication/a356e67e-9413-446f-8f76-e16aa8745385). | The presented axioms are complete for PDL and its stated converse extension. `[a]P` expresses a condition on all terminating `a` outcomes; the modal formula is not the program `a`. | L8 directly supplies the universal relation transformer and composition law. Iteration/test syntax and a completeness proof are separate. |
| V4. Quantified differential dynamic logic for distributed hybrid systems | Hybrid programs with quantified assignments, differential equations and changing dimension. [Platzer, *A Complete Axiomatization of Quantified Differential Dynamic Logic* (2012)](https://logic.kastel.kit.edu/ap/pub/QdLax.pdf). | Sound and complete **relative to quantified differential equations**, not an absolute decision procedure or automatic controller extraction. Continuous dynamics and state changes need the paper's semantics. | Existing smooth/geometry libraries may supply particular equations; L8 supplies relation transport. No inspected bridge interprets QdL or turns disk-motion proofs into this calculus. |
| V5. Probabilistic program semantics; measurable programs with random input | Partial measurable-function semantics and continuous linear operators on measures. [Kozen, *Semantics of Probabilistic Programs* (1981)](https://www.cs.cornell.edu/~kozen/Papers/ProbSem.pdf). | Two specified semantics are equivalent; behavior is determined by action on fixed inputs. This is a denotational correspondence under the paper's measurability/domain assumptions, not a unique probability-as-types language. | L7 and M5 provide kernels and composition. Matching sample spaces, subprobability/termination mass, and observations is an additional adapter. |
| V6. Propositional probabilistic dynamic logic, PPDL, quantitative rather than Boolean combination alone | Arithmetic assertions/program operators and a deductive calculus. [Kozen, *A Probabilistic PDL* (1985)](https://www.cs.cornell.edu/kozen/Papers/PPDL.pdf). | Small-model and decision results apply to the stated formulas involving well-structured programs. Expected-value reasoning differs from nondeterministic possibility; this entry claims no transfer to arbitrary Boolean combinations, demonic choice or continuous sampling. | L7 supplies distributional meaning; a PPDL syntax and satisfaction-preserving compiler are not supplied. |
| V7. Probabilistic guarded-command language with nondeterminism and refinement | Specifications progressively refined to programs. [McIver–Morgan, *Correctness by Construction for Probabilistic Programs*, v1 (2020)](https://arxiv.org/abs/2007.15246v1). | A correctness-preserving refinement relation supports the paper's derivation of sampling algorithms. Direction matters: resolving nondeterminism is refinement, not generally semantic equality. The cited derivation is not a completeness theorem for arbitrary probabilistic specifications. | L7 gives concrete finite kernels and probabilistic delivery contracts. No general pGCL refinement/extraction interface follows from those results. |

## Quantities, abstraction, games, and physical interpretations

| ID and fragment/profile | Counterpart and primary result | Direction, strength, and assumptions | Reuse / missing bridge |
|---|---|---|---|
| Q1. Metric sensitivity types with scaled modalities and probabilistic effects | Fuzz's functional calculus. [Reed–Pierce, *Distance Makes the Types Grow Stronger* (2010), metric preservation result](https://www.cis.upenn.edu/~bcpierce/papers/dp.pdf). | Typing bounds how outputs differ for related inputs; the probabilistic interpretation supports differential privacy. Soundness is relative to chosen metrics/effects and is not completeness of inference for all sensitive functions. Sensitivity bounds and execution costs are different quantities. | L9 has enclosures and L7 probability. Neither provides Fuzz's metric logical relation or a privacy guarantee. |
| Q2. Dependent cost-aware types with a behavioral phase; directed/effectful extension separately | Calf and Decalf. [Niu et al., *A Cost-Aware Logical Framework* (2022)](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf), [Grodin et al., *Decalf*, v4 (2026)](https://arxiv.org/abs/2307.05938v4). | Calf separates cost from input/output behavior; Decalf compares effectful computations by an intrinsic order, with behavioral equality in the behavioral phase. These are model/type-theory contracts, not equality of physical runtime. | L5 already proves generic accounting. A modal abstraction/noninterference bridge would be new; duplicating potential telescoping would not. Foundation/version assessment continues under #208. |
| Q3. Concrete collecting semantics → abstract ordered semantics | Abstract interpretation and fixed-point approximation. [Cousot–Cousot, *Abstract Interpretation* (POPL 1977)](https://cs.nyu.edu/~pcousot/COUSOTpapers/POPL77.shtml). | An abstraction relation/Galois connection supports sound approximation of program behavior. Reflection and precision are separate; widening addresses convergence and may lose further information. This is an analysis route, not a Curry–Howard equivalence. | L9 already supplies concrete dependency-loss counterexamples and enclosure compilation; M3 supplies lattices and adjunctions. Reuse before proposing a general abstract interpreter. |
| Q4. PCF with higher-order functions and recursion, observational equivalence | Game semantics. [Abramsky–Jagadeesan–Malacaria, *Full Abstraction for PCF* (2000)](https://ora.ox.ac.uk/objects/uuid%3A41199322-fb8b-4704-aa1f-7bc479046a2a). | The paper's game model, with its observational treatment, is fully abstract; definability applies to its specified recursive strategies. This does not make every game or winning strategy a PCF program. | No inspected local game model or contextual-equivalence bridge. Relation transport alone omits interaction structure. |
| Q5. Strongly compact closed structure with biproducts, based on a category with involution | Quantum proof nets. [Abramsky–Duncan, *A Categorical Quantum Logic*, v1 (2005)](https://arxiv.org/abs/quant-ph/0512114v1). | Strong normalization and a full, faithful presentation of the **free** structured category. Interpretation into a concrete quantum model is another map and need not remain faithful. This logic is not ordinary cartesian logic with a “quantum” primitive. | M2 supplies monoidal infrastructure; matrix backends do not by themselves supply dagger/compact/biproduct proof-net semantics or quantum compilation. |
| Q6. Cobordisms and quantum processes as monoidal categories | Diagrammatic comparison and topological quantum field theory. [Baez–Stay, *Physics, Topology, Logic and Computation*, v1 (2009)](https://arxiv.org/abs/0903.0340v1). | Shared categorical structure gives precise analogies; a chosen TQFT is a structure-preserving functor. No equivalence of all topology, physics, logic and computation is asserted. Cobordisms between boundaries differ from identity-type paths between points. | A horizon example for operation-specific backends, not a current project consumer or missing mandatory implementation. |

Q2 intentionally refers to the separately maintained Harper assessment rather
than treating all versions of Calf/Decalf as the same theory. Q1 and Q3 show why
“quantitative” cannot be one undifferentiated backend: sensitivity compares
nearby inputs; an enclosure contains possible results; cost counts selected
operations. Their orders and composition laws differ.

## Local and Mathlib reuse map

These identifiers describe **inspected evidence**, not global absence claims.
Local names are verified in the linked files at the conaled revision above.
Mathlib links pin the dependency revision; declarations were read from the
matching installed checkout. A directory's existence is not counted as an
implemented correspondence.

| Key | Reusable declarations and exact scope | Gap exposed by the atlas |
|---|---|---|
| L1 | [Compiler](../../Compiler.lean): `CategoricalCompiler.Term`, `Target`, `Sound`; [STLCNaturality](../../SquareKit/STLCNaturality.lean): `Model`, `Preserves`, `naturality`, `preserves_comp`, `naturality_comp`; [STLCRelations](../../SquareKit/STLCRelations.lean): `compile_preserves`. The source has one base atom; interpretations vary its meaning. | Semantic preservation/composition already exists, including function relations over related inputs. The compiler's semantic beta/eta results are not syntactic normalization or an explicit proof/program inverse. New atomic sorts or resource/modal contexts need stated scope. |
| L2 | [Logic](../../SquareKit/Internal/Logic.lean): `FormulaCore` has equality, relations, conjunction and existence; `Derives : … → Prop`, `formula_subst`, `sound`. [DependentSheafSoundness](../../SquareKit/Internal/DependentSheafSoundness.lean): `type_sound`, `term_sound` for its bounded dependent fragment. | Not full intuitionistic predicate syntax, inspectable proof-relevant derivations, or a universal dependent model. Preserve the existing validity interface while adding computational witnesses separately if needed. |
| L3 | [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean): `Route.transport`, `transport_concat`, `substitution_transport`, `comp_assoc`; [SecondIdentity](../../Examples/SecondIdentity.lean): explicit distinct 2-cells, `cell_distinct`, `observation_encode`. | Transport and composition are implemented. New work must add an actual interpretation/comparison or retained-identity observation, not repackage these laws as a missing foundation. |
| L4 | [FRP Spec](../../Applications/FRP/Spec.lean): `Behavior`, `Event`, `Event.never`; [FRP Trace](../../Applications/FRP/Trace.lean): `observe_persists`, `interleavings_agree`, `Delivery.Fair`, `eventual_observation`. | Locally finite real-time events and conditional delivery are not a constructive temporal type system. Preserve schedule/fairness hypotheses, and distinguish continuous denotations from causal implementations. |
| L5 | [Potential accounting](../../Applications/Resources/Potential.lean): `run_potential`, `run_potential_exact`, `run_constant_charge`; [checked callers](../../Examples/PotentialAccounting.lean). | New modal encapsulation or a persistent-branching resource discipline could add capability. A second linear-history queue bound alone does not. |
| L6 | [Language machines](../../Applications/Languages/Machines.lean): `Machine.Correct`, `Machine.run_correct`, `regexMachine_correct`, `Machine.lookup_unfold`. | Correctness is for finite words/depth observations. This is not omega acceptance, CTL, timed automata, Lambek derivation search, or a synthesis game. |
| L7 | [Finite kernels](../../Applications/Probability/FiniteKernel.lean): `comp`, `kernel_comp`, `kernel_deterministic`, `table_steps_meaning`; [Productivity](../../Applications/Probability/Productivity.lean): `AlmostSureProductive`, `almostSureProductive_iff`. | Finite-table semantics and almost-sure progress do not imply pathwise termination, expected-time bounds, or general probabilistic proof extraction. |
| L8 | [RelationTransport](../../SquareKit/RelationTransport.lean): `image`, `requirement`, `image_requirement`, `requirement_comp`, `requirement_converse_graph`, `requirement_restricted_converse`. | A reusable forward-existential/backward-universal predicate pair and Galois connection already exist. Universal preconditions are vacuous on states with no outputs; no termination or reachable-world assertion is built in. |
| L9 | [Interval arithmetic](../../Applications/Intervals/Arithmetic.lean): `Contains`, `add_contains`, `mul_contains`; [higher-order intervals](../../Applications/Intervals/HigherOrder.lean): `compile_contains`, `iterateTwice_contains`. [ADR 0007](../adr/0007-incremental-and-enclosure.md) records dependency loss. | Sound enclosures deliberately differ from exact decoding/equality. They neither enforce sensitivity types nor justify identifying extensionally equal programs' analyses. |
| M1 | [Mathlib first-order syntax](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Syntax.lean): `FirstOrder.Language.Term`, `BoundedFormula`, `Term.subst`; [semantics](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Semantics.lean): `Term.realize_subst`; [satisfiability](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Satisfiability.lean): `Theory.isSatisfiable_iff_isFinitelySatisfiable`. | Reuse model-theoretic syntax/semantics where it fits. Compactness and satisfaction are not a computational derivation datatype or a normalizer. |
| M2 | [Mathlib closed categories](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean): use `CartesianMonoidalCategory` plus `MonoidalClosed`, not the deprecated separate `CartesianClosed` class; [dependent products](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean): `ExponentiableMorphism`, `pullbackPushforwardAdj`, `ev`, `coev`. | Structural models are available; coherence, source soundness and required preservation remain the adapter's job. Do not require CCC structure for fragments needing only composition/tensor. |
| M3 | [Mathlib fixed points](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/FixedPoints.lean): `OrderHom.lfp`, `gfp`, `lfp_induction`, `gfp_induction`, `lfp_eq_sSup_iterate`; [Galois connections](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/GaloisConnection/Defs.lean): `GaloisConnection`. | Monotonicity is packaged in `OrderHom`; countable iteration needs the theorem's Scott-continuity assumption. Neither gives a formula parser, positivity checker, nor finite-time model checker automatically. |
| M4 | [Mathlib DFA](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/DFA.lean): `DFA.eval`, `accepts`, `accepts_reindex`, `accepts_comap`, `accepts_inter`. | State/alphabet changes and finite-word Boolean operations already have language contracts. Infinite-word acceptance is a separate interface. |
| M5 | [Mathlib kernel composition](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Composition/Comp.lean): `ProbabilityTheory.Kernel.comp`, `comp_apply`, `lintegral_comp`, `comp_assoc`. | Reuse measurable semantics, while checking the measure-class hypotheses of each theorem. A kernel is mathematical meaning, not necessarily an executable sampler. |

Lean's own `Prop` is proof-irrelevant and erased at runtime, with restricted
elimination into data. Therefore L2's proof validity and P2's retained witnesses
must be connected deliberately. The host proof audit admits only `propext`,
`Classical.choice`, and `Quot.sound`; object-level modalities or univalence
cannot be silently installed as host axioms.
[Lean reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/),
[project audit contract](../../README.md#proof-and-execution-boundary).

## Comparison examples that expose lost information

These are proposed statement tests, not newly checked Lean examples.

| Comparison | Positive case | Boundary or negative case |
|---|---|---|
| P1 versus S1/S2 | Identity consumes its argument once and fits all simple resource profiles. | `λx. (x,x)` needs contraction; `λx. ()` needs weakening. Neither becomes available solely because the denotation happens to be a function. |
| P2 versus host existence | An explicit dependent pair yields its witness and evidence. | A classical `Exists` proof cannot generally be eliminated to executable witness data. A noncomputable choice does not establish extraction. |
| D4 versus ordinary predicates | For an observation `obs`, require `P` on every admissible world with that observation, using L8. | Observing `P` in the actual world does not establish that all indistinguishable worlds satisfy it; an impossible observation also needs a reachability condition. |
| T1/T2 versus T3/T4 | A finite-arrival witness establishes the chosen constructive eventuality; a model checker decides a property of a supplied model. | A satisfying complete trace that predicts tomorrow's unrestricted input is not a causal strategy. `Event.never` is not evidence of eventual arrival. |
| V1/V3 versus progress | Sequential predicate transport composes exactly by `requirement_comp`. | For the empty transition relation every universal postcondition holds vacuously. Total correctness needs an additional termination/totality contract. |
| V5–V7 versus nondeterministic reachability | Probability kernels retain weights; a nondeterministic relation retains possible outputs. | Discarding weights loses expectation and almost-sure claims. Almost-sure termination still allows exceptional nonterminating paths. |
| Q3 versus exact equality | An interval may soundly enclose every result of an expression. | Two equal scalar functions can yield unequal enclosures after dependency loss; reflection cannot be inferred. |
| P6 versus sets; S3 versus unordered grammar | Retain path/2-cell data and word order in their respective models. | Passing to mere equality/orbit sets or permuting a sentence forgets information needed by the original judgment. |

## Prioritized follow-up scopes

These are candidate issue scopes, not new tracker mutations or a fixed
implementation queue. Existing scope owners should absorb them where they fit.
Ranking uses project consumers, preserved information, and the abstraction
stress each example introduces.

1. **Proof objects versus validity, under #203.** Reuse L1's term syntax and
   full-source naturality; choose the product/arrow fragment and add a
   proof-relevant natural-deduction bridge with substitution and beta/cut
   simulation. Specify whether round trips are definitional or modulo equations.
   Demonstrate reusable author-facing construction in two interpretations.
   Do not count existing semantic beta/eta as the missing operational theorem.
2. **Predicate transport versus temporal observation, coordinated with #204.**
   Use L8 for a finite transition system with a partial-correctness assertion
   and a separate reachability/eventuality assertion. Show an empty or unfair
   execution satisfies the former but fails the latter. Compare a checker
   certificate with a constructive program witness. This tests two route kinds
   without requiring a general temporal language.
3. **Resource discipline plus client abstraction, coordinated with #208/#174.**
   Compare duplicable, affine and linear use of one abstract resource while
   reusing L5's cost accounting. Acceptance requires a retained-use or
   noninterference property and a shared client proof; repeated telescoping
   is insufficient. State whether persistent branching can duplicate credits.
4. **Probabilistic versus relational refinement.** Map one finite kernel from
   L7 to its support relation, prove the exact forward observation theorem,
   and exhibit two kernels with equal support but different expected costs.
   A probability-sensitive refinement should distinguish them. This tests
   deliberate information loss and consumers in probabilistic delivery.
5. **Ordered derivations versus recognition.** Choose a small S3 grammar,
   interpret its derivations to semantic composition, and connect successful
   parses to L6's word observations. Retain order and parse evidence; test an
   exchange step that the source forbids. This evaluates proof search without
   pretending a recognizer returns every proof.
6. **Dependent and path-sensitive interpretation.** Reuse L2/L3 and M2 for one
   additional model comparison. Show precisely which witness survives and
   which is lost by a set-valued observation. Add a substitution-coherence
   theorem only where the existing routes do not already provide it.

A later consumer may justify spatial tree checking, heap framing, metric-time
verification, epistemic protocol analysis, or quantum proof nets. Each should
first name the missing observation and the source theorem it intends to
reconstruct. The survey does not rank them as foundational prerequisites.

## Open questions and maintenance boundaries

- **Relevant logic:** S2 provides an operational calculus with relevant
  qualifiers, not a complete map of relevance logics R, E, ticket entailment,
  or their algebraic models. Which use discipline has a concrete consumer?
- **Classical predicate extraction:** P4's semantic completeness does not answer
  which control/realizability translation should interpret an arbitrary
  classical quantified proof. Fix a proof calculus, witness class, and answer
  type before choosing that route.
- **Epistemic computation:** D4 supplies analysis of knowledge and coordination.
  A proof-term calculus for a selected epistemic system remains unassessed;
  absence here is not evidence that none exists.
- **Temporal scope:** CTL*, unrestricted MTL under each time semantics,
  distributed synthesis, and branching-time proof calculi require separate
  entries. T3–T6 must not be generalized to them by name similarity.
- **Program logic:** separation semantics for higher-order store, concurrent
  separation logics, and constructive dynamic/game logics need their own
  model and extraction assessments. V2/V4 do not settle them.
- **Normalization versus observation:** can the selected source quotient retain
  enough directed computation for a useful reduction theorem while supporting
  current semantic maps? Quotienting all observations together would answer
  the wrong question.
- **Author effort:** can clients write one ordinary construction, with the
  implementation inferring or exposing its requirements, rather than manually
  assembling proof trees? This is the [shared language criterion](../language-direction.md),
  not a theorem supplied by the atlas.

Before treating an entry as implemented, replace its gap with a link to a
specific source-level theorem, checked contrasting examples, and validation
record. Recheck the dependency revision before relying on Mathlib names.
Preserve soundness, reflection, definability, operational behavior, and
quantitative bounds as separate claims throughout.

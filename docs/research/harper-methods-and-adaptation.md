# Harper's methods: reuse, foundations, and bounded adaptations

Assessment for [#209](https://github.com/VladimirMarko/conaled/issues/209),
2026-10-28. Local declarations were inspected at
`c4f469dd2dfdf4dce471fb355b9ab478d3d62dd5`, with Lean 4.35.0.
This delivers a research and integration assessment. The experiments below
are proposed contracts for #210 and #211, not new Lean theorems or an adopted
language architecture. It extends the [correspondence survey](curry-howard-correspondences.md).

Implementation update: the proposed experiments below are retained as the
research snapshot. The [shared FIFO client](abstract-fifo-client.md) and
[modular cost contract](modular-fifo-costs.md) now record #210/#211's bounded
adaptations and checked examples. Their guarantees use explicit Lean interfaces;
they do not implement the cited frameworks' full phase or sealing mechanisms.

The immediate opportunity is **client proof reuse across representations and
cost models**. Existing relational compilation and potential accounting already
provide much of the mathematical infrastructure. Harper and collaborators supply
methods for making the abstraction boundary part of the language and theorem,
so clients cannot depend on the private information being abstracted. Start by
reconstructing a bounded instance of that guarantee over existing squares.
Importing a complete modal, cubical, or simplicial metalanguage would add
obligations that this first experiment does not need.

## Source assessment and reading order

The conclusions in the last column are project judgments. “Low”, “medium”, and
“high” describe additional mathematical/interface obligations, not elapsed-time
estimates. Source claims concern each paper's specified calculus, not arbitrary
Lean programs. An object language is the language being studied; the
metalanguage is where its syntax, interpretations, and metatheorems are expressed.

| Source and evidence | Construction, assumptions, and object/meta boundary | Local use, missing capability, and adaptation cost |
|---|---|---|
| **PFPL**, second edition, Cambridge 2016; [author's corrected edition, supplements, and errata](https://www.cs.cmu.edu/~rwh/pfpl/) | Organizes language definitions through judgments, statics, dynamics, and type structure. Its calculi are objects of mathematical study, not changes to the host checker's rules. The continuation, module, and cost-dynamics supplements let readers isolate relevant fragments. | **Absorb now, low:** give each new embedded fragment a judgment/equality/operation contract and consult the relevant errata. `Compiler.Term` and internal derivations already follow parts of this discipline. The gap is consistency of the contracts across new routes, not a missing universal language implementation. |
| **Harper–Honsell–Plotkin, LF**, [A Framework for Defining Logics](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf), especially encoding and adequacy | Dependent LF types classify object judgments; inhabitants encode derivations. Hypothetical judgments and binding use the framework's function structure. Adequacy relates canonical LF inhabitants to the intended object derivations; type checking alone does not establish that an encoding expresses the intended logic. | **Absorb method, low; adapt encoding, medium:** #203 can give a proof-relevant natural-deduction/STLC bridge and substitution theorem. Existing `SquareKit.Internal.Derives` is a validity judgment in `Prop`. A new inspectable proof object belongs in `Type`; unrestricted higher-order abstract syntax is not automatically an admissible Lean inductive definition. |
| **Minamide–Morrisett–Harper, Typed Closure Conversion**, [POPL 1996 paper](https://sv.c.titech.ac.jp/minamide/papers/popl96.pdf) | Translates simply typed and polymorphic lambda calculi to typed code/environment packages. The environment representation is hidden; polymorphic closures need additional type-sharing information. This is a source-to-target type-preservation construction in a metatheory. | **Adapt on emitter demand, medium:** local STLC functions are represented by host functions, not explicit closure layouts. A future higher-order emitter should prove typing, environment substitution, and semantic simulation separately. Retaining types across a pass is useful; it does not itself prove behavior or cost preservation. |
| **Harper–Morrisett, Compiling Polymorphism Using Intensional Type Analysis**, [POPL 1995 paper](https://dash.harvard.edu/bitstreams/7312037c-54af-6bd4-e053-0100007fdf3b/download) | Makes runtime type analysis explicit in a typed intermediate language so representation choices need not use one universal boxed layout. Type information has an operational role in the object language. | **Defer implementation, medium/high:** require an actual representation-sensitive backend and an explicit observation policy first. It informs #128, but type inspection can invalidate a parametricity claim that assumed representations were unobservable. Do not combine it silently with an abstract-module theorem. |
| **Harper–Mitchell–Moggi, Higher-Order Modules and the Phase Distinction**, [POPL 1990 paper](https://www.cs.cmu.edu/~crary/819-f09/HarperEtal89.pdf) | Separates compile-time and runtime components of higher-order modules, with a phase-sensitive equational theory and categorical account via the Grothendieck construction. Module equality is not simply runtime-value equality. | **Absorb distinction now; adapt only when needed, medium:** distinguish model selection/static capabilities from dynamic data in embedded interfaces. Existing `Target` parameters and `Model` are useful counterparts, but they are not a formal module calculus with sharing/generativity. A namespace or Lean structure alone establishes no phase theorem. |
| **Sterling–Harper, Logical Relations as Types (LRAT)**, [2021 version, §§2–5](https://arxiv.org/html/2010.08599v3) | ModTT is the object module theory; ParamTT and a gluing model support its phase-sensitive, proof-relevant parametricity. A lax modality handles generativity/effects. §4 supplies queue representation independence through a simulation structure, going beyond a truth-valued relation. | **Adapt next, medium:** reuse `STLCRelations.compile_preserves` for the existing fragment, then test a common client over two implementations. The new result must hide implementation details or retain needed witness data. A copied fundamental theorem over `Prop` relations would not reproduce ModTT's module/effect theorem. |
| **Niu–Sterling–Grodin–Harper, calf**, [POPL 2022 paper, §2.7 and model construction](https://www.cs.cmu.edu/~rwh/papers/calf/popl22.pdf) | Treats cost as a computational effect in dependent type theory. Its extensional/intensional phase distinction yields noninterference: suitable behavioral observations cannot inspect added cost. The paper gives a semantic justification and Agda case studies. | **Adapt next, medium:** measured results and erasure already exist locally. The gap is a client class and theorem ensuring that cost cannot change behavior through observation. A pair `(value, cost)` permits unrestricted Lean functions to read cost; erasure alone supplies no noninterference theorem. |
| **Grodin–Niu–Sterling–Harper, Decalf**, [v4, 2026-05-20](https://arxiv.org/abs/2307.05938v4), publication [POPL 2024](https://www.cs.cmu.edu/~runmingl/calf.html) | Cost comparison becomes an intrinsic preorder whose behavioral phase reduces to equality. Bounds can themselves be effectful programs; the model uses augmented simplicial sets. This avoids assuming a separately extractable numeric cost for every effect. | **Adapt a restricted order first, medium; defer full model, high:** an ordered measured interpretation can serve deterministic #211. Probabilistic consumers require an explicitly selected comparison of effectful computations. Equality of expected cost, pointwise bounds, and a program preorder are different contracts. |
| **Grodin–Li–Harper, Abstraction Functions as Types (AFAT)**, [v4, POPL 2026, Theorem 2.5 and Corollary 3.4](https://arxiv.org/pdf/2502.20496v4) | In univalent dependent type theory, fracture/gluing expresses concrete and abstract parts plus an abstraction map. Modularity constrains clients; a sealing effect supports cost bounds when private implementation details affect cost. | **Adapt bounded semantic content first, medium:** squares already package a commuting implementation/specification comparison. Add a representation-independent client theorem and a public cost interface hiding potential. Prove those claims directly in Lean before claiming any realization of AFAT's full modalities or universal fracture theorem. |
| **Sterling–Harper, Guarded Computational Type Theory**, [LICS 2018 version](https://arxiv.org/abs/1804.09098v1) | An operational dependent type theory with clocks, later, clock intersection/irrelevance, and predicative universes. It can also act as a metalanguage for recursive semantic objects. | **Adapt with #205, medium/high:** existing stream and FRP models are consumers, but a total host function on streams can anticipate inputs. A bounded explicit clock/guarded interpretation must prove its causal/productive contract. Guarded productivity alone does not yield a terminating eventuality witness. |
| **Angiuli–Harper–Wilson, Computational Higher Type Theory I**, [v2, 2016](https://arxiv.org/abs/1604.08873v2) | Cubical realizability supplies a computational meaning explanation with Kan operations, higher identifications, and a Boolean canonicity theorem. These are constructs of the studied type theory and its semantic validation. | **Defer full theory, high; absorb operational discipline:** local groupoid identity is an explicit model in Lean. For #213 retain path witnesses and composition; for a cubical extension separately specify dimensions, coercions, and composition. Neither ordinary equality nor the existence of a groupoid supplies Kan filling or univalence. |
| **Sterling, First Steps in Synthetic Tait Computability**, [2021 thesis, chapters 4–7](https://www.csd.cs.cmu.edu/sites/default/files/phd-thesis/CMU-CS-21-142.pdf), supervised by Harper | Uses gluing and internal type-theoretic reasoning to organize canonicity and normalization, including open cubical terms. The synthetic metalanguage's topos/universe assumptions are supplied by a model; they are not new axioms of the object calculus. Normalization and its computability are separate steps. | **Adapt when #214 has a consumer, high for generality:** select an existing bounded source, then evaluation/reification and its equality contract. Existing compilation soundness is not normalization. Start with a direct semantic proof; a generic internal gluing metatheory must earn its cost through reuse across type constructors or languages. |

### Newer work and artifact evidence

The two July papers remain **preprints** on
[Harper's author-maintained page](https://www.cs.cmu.edu/~rwh/index.html) as
checked on the assessment date. Their results guide experiments but have not
been independently reproduced here.

- [Potential Functions as Types (PFAT), v2, 2026-07-10](https://arxiv.org/abs/2607.08547v2)
  combines abstraction maps and potentials, credit/debit operators, and Giralf,
  a graded substructural language interpreted in Calf. Its inference result is
  for a restricted program class. **Adapt the modular potential contract;
  defer Giralf and inference** until #211 identifies a repeated manual burden.
  The local counterpart is `run_potential`; the missing property is hiding a
  private potential while composing client bounds, not the summation argument.
- [Directed proof-relevant logical relations in simplicial HoTT, v1,
  2026-07-09](https://arxiv.org/abs/2607.08154v1) uses directed quotient syntax,
  contravariant computability families, and a flat modality in the dependent
  extension. It distinguishes reduction from relational comparison and proves
  directed Boolean canonicity. **Defer its simplicial metalanguage, high cost**;
  first use explicit reduction witnesses and a simulation relation for one
  local calculus. Groupoid arrows are invertible and cannot stand in for a
  directed reduction merely because both compose.
- [Li–Yao–Harper's CPP 2026 mechanization](https://www.cs.cmu.edu/~runmingl/calf.html)
  is a separate implementation of synthetic Tait computability in Istari.
  Its [repository](https://github.com/runmingl/istari-stc/tree/2ff49a7d73f3ad9b3dbeb2b61d7b7f4e1fbb3c8a)
  presents canonicity cases for dependent products/Booleans and Calf.
  It is evidence of mechanized source development, not a Lean port. Istari's
  equality reflection makes the proof-writing experience different from Lean's.

| Inspected artifact | Toolchain, license, and assumptions observed | Reuse decision and evidence limit |
|---|---|---|
| [agda-calf at `10f1ba616e1ade017e4048324ae894281379ce08`](https://github.com/calfproject/agda-calf/tree/10f1ba616e1ade017e4048324ae894281379ce08) | [README](https://github.com/calfproject/agda-calf/blob/10f1ba616e1ade017e4048324ae894281379ce08/README.md) reports Agda 2.6.3 and stdlib 2.0 experimental; [INSTALL](https://github.com/calfproject/agda-calf/blob/10f1ba616e1ade017e4048324ae894281379ce08/INSTALL.md) says stdlib 2.0. [LICENSE](https://github.com/calfproject/agda-calf/blob/10f1ba616e1ade017e4048324ae894281379ce08/LICENSE) is Apache-2.0. [CBPV](https://github.com/calfproject/agda-calf/blob/10f1ba616e1ade017e4048324ae894281379ce08/src/Calf/CBPV.agda) postulates type universes, operations and equations, registering rewrite rules; [Phase.Core](https://github.com/calfproject/agda-calf/blob/10f1ba616e1ade017e4048324ae894281379ce08/src/Calf/Phase/Core.agda) postulates the phase proposition. | Use definitions and examples as implementation references with attribution; no source copied here. Resolve the stdlib wording to a concrete dependency revision before any reproduction. Importing the postulates into Lean would violate the audit; reconstruct or interpret a selected theory instead. Source inspected, **not built**. |
| [PFAT HTML guide](https://www.cs.cmu.edu/~runmingl/pfat/README.html) and [computation module](https://www.cs.cmu.edu/~runmingl/pfat/Calf.Computation.html) | Guide reports Agda 2.8.0, stdlib 2.3, cubical 0.9. It links fracture/gluing, potential, queue and Giralf modules. The computation module uses cubical foundations and univalence and defines cost actions/homomorphisms. These dependencies differ from the preceding Agda embedding. | Useful mathematical reference for explicit cost-action squares. No immutable source revision or software license established from the inspected HTML guide/modules, so **no recommendation to copy or vendor this artifact**. Publication licensing is not substituted for source licensing. No build performed. |
| [istari-stc at `2ff49a7d73f3ad9b3dbeb2b61d7b7f4e1fbb3c8a`](https://github.com/runmingl/istari-stc/tree/2ff49a7d73f3ad9b3dbeb2b61d7b7f4e1fbb3c8a) | README specifies Istari and links its installation guide, without a pinned toolchain/dependency manifest. Inspected repository tree has no LICENSE file; GitHub license metadata is empty. It explicitly relies on an extensional theory with equality reflection. | Read the separation of demo statements and semantic proofs. Establish license and reproducible toolchain before source reuse. Translate the mathematical method with explicit equality transports, not Istari's judgmental rules. Source/README inspected, **not built**. |

No Twelf, historical TIL compiler, or cubical proof-assistant build was performed.
Their papers support conceptual adaptation; this assessment does not recommend
vendoring their implementations. The artifact checks above cover the candidates
most directly relevant to #210/#211. A future port needs its own pinned source,
dependency/license review, and executable reproduction record.

## What the current library already supplies

These are source-inspection findings at the recorded base, not a fresh build of
the existing library. References identify the declarations to reuse and the
scope beyond which they supply no guarantee.

| Local interface and declarations | Reusable result | Missing claim that would justify new work |
|---|---|---|
| [Compiler](../../Compiler.lean): `Term`, `Target`, `Sound`; [STLCNaturality](../../SquareKit/STLCNaturality.lean): `Model`, `Preserves`, `naturality`, `preserves_comp`, `naturality_comp` | Target-dependent interpretation and composition of structure-preservation evidence for existing typed syntax. | No general module sealing, closure-layout transformation, or proof of contextual equivalence follows from this denotational contract. |
| [STLCRelations](../../SquareKit/STLCRelations.lean): `Encoding.arrow`, `Primitives`, `compile_preserves`, `compile_apply_preserves` | The fundamental relation theorem already handles every current STLC constructor and all related function arguments. | Its `Rel` is `Prop`-valued. LRAT-style proof-relevant parametricity, generativity, and phases need additional data/rules. Repeating this induction without a new boundary is not a contribution. |
| [Relations](../../SquareKit/Relations.lean): `RelRep`, `RelSquare`, `compose`, `witnessSquare` | Representation relations need not be functions; preservation composes. Total witnesses retain represented values and relational evidence. | Putting a `Prop` proof inside a witness does not create multiple distinguishable proofs of that proposition. Semantic witness data and proof relevance are different. |
| [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean): `Route`, `transport`, `transport_concat`, `reindex`, `substitution_transport`, `comp_assoc`; [GroupoidIdentity](../../SquareKit/Internal/PathTransport/GroupoidIdentity.lean): `family`, `compose_natural` | Functorial routes retain explicit morphisms and natural transport; identity families are `Type`-valued. | These are bounded higher-identity models, not a univalent universe or directed simplicial model. |
| [Measured](../../Applications/Resources/Measured.lean): `bind_erases`, `reweight_bind`, `reweight_bound`, `erasureSquare`; [Workload](../../Applications/Resources/Workload.lean): `run_append`, `run_value_fusion`, `reweight_run` | Behavior erasure, workload composition, and justified changes of resource observation. | Unrestricted functions can inspect the measured pair. Noninterference needs a restricted client interface or an explicit invariance theorem. |
| [Potential](../../Applications/Resources/Potential.lean): `run_potential`, `run_cost_le`, `run_constant_charge`, `initial_potential_matters` | Local inequalities telescope with initial and final potential retained. | Public bounds that hide private potential; accounting for branching persistent use rather than one trajectory. |
| [Symmetric observations](../../Applications/Sequences/Symmetric/Observation.lean): `representation`, `snocSquare`, `tailSquare`, `headSquare`, `editHead_correct`; [SymmetricCosts](../../Applications/Resources/SymmetricCosts.lean): `execute_abstraction`, `execute_work_potential`, `run_work_empty`; [SymmetricWorkload](../../Applications/Resources/SymmetricWorkload.lean): `workloadSquare`, `observedWorkload`, `measuredRun_bounds` | An existing two-list sequence representation, composed endpoint client, actual measured transitions, and separate charge/work bounds. | A client theorem parameterized by an abstract operation package, instantiated across representations, with a public cost contract independent of the private potential formula. |

The [Sierpiński classifier](../../SquareKit/Internal/SierpinskiEquivalence.lean)
also supplies categorical infrastructure worth inspecting for a future phase
model. A classifier equivalence alone does not establish ModTT/Calf interpretation,
their universes, or noninterference. #202 should record the missing interpretation
obligations before proposing that larger construction.

## Foundational boundary and viable Lean reconstructions

Lean's native `Prop` is definitionally proof-irrelevant, erased at runtime,
and restricted in elimination into data. Its equality proofs therefore cannot
serve as arbitrary proof-relevant paths. [Lean reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).
The repository [audit](../../README.md#proof-and-execution-boundary) permits
`propext`, `Classical.choice`, and `Quot.sound`; it does not authorize extra
phase, univalence, or equality-reflection axioms.

| Source requirement | Bounded reconstruction to investigate | Obligation that remains visible |
|---|---|---|
| Judgments and proof relevance | Explicit syntax/derivations and relation witnesses in `Type`; separate validity in `Prop`. | Adequacy, substitution, and equations; a program witness cannot be extracted from arbitrary erased existence evidence. |
| Static/dynamic or abstract/concrete phases | An explicit category of abstraction maps and commuting squares, plus clients constrained to preserve the representation relation. | Prove the client theorem. Do not label an arbitrary Lean function “phase-respecting” merely because its input is a structure. |
| Cost noninterference | A measured interpretation of a cost-oblivious client, with erasure commuting with every operation. | Return value invariant under allowed cost changes; bounds remain ordered observations. Exposing the cost projection invalidates the client restriction. |
| Cubical/univalent structure | Use existing groupoid routes where first-identity evidence suffices; otherwise model a specified object fragment. | Explicit Kan/universe/coherence obligations for any stronger claim. Equivalence of carriers is not a host equality rule. |
| Directed/simplicial structure | Start with explicit reduction and its simulation, or an ordered cost model. | Reduction need not be invertible; a preorder discards distinct witnesses and is insufficient if higher directed evidence is claimed. |
| Universes and extensional metalanguage | Keep object universes as explicit codes/models and use Lean universe levels for their carriers. Prove propositional equalities and transports. | No `Type : Type`, automatic resizing, or conversion of propositional equality into judgmental equality. A model of a fragment is not a self-model of all Lean. |
| Clock quantification and guarded recursion | An indexed object language/model with named clock and observation contract. | Check productivity and causality against FRP observations; finite arrival and fairness require their own premises. |

For #210/#211, ordinary types, relations, additive ordered costs, and proved
preservation are sufficient candidates. The cost of adopting AFAT's entire
univalent internal theory is therefore unjustified for this initial experiment,
even though its abstraction-map and sealing discipline is directly useful.
“Hidden” below means absent from the client parameters and theorem assumptions,
with a proved representation-invariance property. It is not a security claim
about arbitrary Lean metaprograms or a new kernel access-control mechanism.

## Proposed #210 experiment: one client, two sequence representations

Use ordinary lists and the existing symmetric lists, restricted initially to a
FIFO interface: empty, append-at-right, remove-at-left, and observe-first.
This avoids implementing another batched queue merely to match a paper example.
The concrete operations and invariants are already in
[Symmetric.Core](../../Applications/Sequences/Symmetric/Core.lean).

1. **Public contract.** Parameterize the program by a carrier `Q` and operations
   `empty : Q`, `snoc : α → Q → Q`, `tail : Q → Q`, and
   `head : Q → Option α`. State the independent list specification. Keep
   decoding/invariant evidence in the implementation's correctness package,
   outside the executable client. Empty deletion stays total and returns empty;
   observing empty returns `none`, matching current semantics.
2. **Implementations.** Use `Q = List α` with identity relation, and
   `Q = SymList α` with `Inv q ∧ fromSL q = xs`. Package empty and operation
   preservation once, reusing the three existing operation squares. Allow the
   generic relation interface to remain nonfunctional even though this example
   has a decoder. Compare results at the common `Option α` observation.
3. **Client and theorem.** Write a single generic client that executes a finite
   word of enqueue/delete commands and then observes the head. Prove its list
   specification once from the public operation contracts, for all words and
   related starting states. Instantiate the same theorem twice. Split a word
   into two parts and derive the composed client contract without repeating
   the proof. Reuse `run_value_fusion` where its invariant/transition shape fits.
4. **Internal use.** Express a bounded state-transforming word using existing
   STLC primitives and composition, then attach `headSquare` as an observation.
   Use `compile_preserves`/naturality, rather than recreating a relation theorem.
   This can keep the compiler's single base type as the queue carrier; the
   endpoint observation need not force heterogeneous data into a new universal
   AST. Keep the direct Lean client available.
5. **Nontrivial and negative cases.** Exercise enqueue twice, delete, enqueue,
   observe, including the empty and rebalance cases. Exhibit valid symmetric
   states `([a], [c,b])` and `([a,b], [c])`, both decoding to `[a,b,c]`, with
   different front lengths. A client allowed to inspect front length breaks
   representation independence. Such a client is outside the operation-only
   theorem; a second theorem about all Lean functions is not asserted.
6. **Novelty gate.** `editHead_correct` and `observedWorkload_value` already prove
   concrete composed consumers. #210 succeeds only when one authored client
   theorem serves both implementations through the public interface, and the
   example shows which representation-specific obligations disappear. Record
   primitive obligations, client proof obligations, and any remaining internal
   syntax bookkeeping. A renamed composition theorem is insufficient.

This first instance needs only truth-valued representation preservation.
Do not require proof-relevant relations solely to resemble LRAT. If an extension
uses multiple computational simulation witnesses, preserve those in `Type` and
state their composition laws separately. No general parametricity theorem for
Lean, ModTT, or arbitrary effects is part of #210.

## Proposed #211 experiment: public bounds, private potential

Extend the same operation-only client with measured transitions. Keep behavior
clients independent of cost machinery. The following are proposed specifications;
new instrumentation and interface theorems require checked implementation.

For implementation `i`, let `dᵢ` be its abstraction map on valid states,
`stepᵢ op q = (q', c)`, and `bᵢ op xs` its **public** charge profile depending
only on the abstract state. The implementation privately supplies `Φᵢ` and proves

```text
c + Φᵢ(q') ≤ Φᵢ(q) + bᵢ(op, dᵢ(q)).
```

Use a valid-state subtype or the existing invariant discipline to discharge the
universal premises of `run_potential`. Define `Bᵢ ops xs` as the sum of public
charges along the independent list trajectory. Prove that the concrete budget
equals that abstract budget using behavior preservation. Then derive the shared
client theorem

```text
cost(runᵢ ops q) ≤ p₀ + Bᵢ ops xs
```

from a public initialization certificate for related `q,xs` whose private
potential is bounded by `p₀`. The certificate interface must hide the formula
for `Φᵢ` from the client theorem. Empty construction can expose `p₀ = 0`.
Arbitrary imported states need a public initial credit; do not silently assume
zero potential. The existing `initial_potential_matters` is a reusable negative
case. Keep the stronger inequality with final potential inside the package for
composition, even when the public endpoint theorem drops that nonnegative term.

Concrete evidence to require:

- **Symmetric implementation:** reuse `execute`, `workStep`,
  `execute_work_potential`, and `run_work_empty`. Its existing structural-work
  model supports private potential `2 * potential q` and public per-operation
  charge `8`. Expose this profile without exposing the two-list imbalance.
- **List implementation:** instrument actual append recursion and constant
  head/tail operations, with erasure proofs. A proposed source-visit convention
  charges `xs.length + 1` for append and `1` for head/tail; prove it from the
  instrumented definitions before using it. It uses zero potential. These are
  modeled source visits, not Lean allocation or elapsed runtime.
- **Shared theorem, distinct bounds:** parameterize the client theorem by the
  public profile. The symmetric and list instances then get different budgets
  from the same theorem. If a common coarse profile is useful, `xs.length + 8`
  bounds both proposed profiles, but report that it loses the symmetric
  implementation's constant amortized per-operation advantage.
- **Observation accounting:** the existing `observedWorkload` retains prior
  resources when observing the final head; it does not charge for that extra
  observation. Either state that convention or include an explicit measured
  `.head` step. Do not claim a paid observation while only reusing the former.
- **Composition and changes of measure:** prove budget concatenation along the
  abstract trajectory and reuse `run_append`, `budget_append`, and the retained
  final potential internally. Clients composing two parts must not pay or spend
  the initial potential twice. Reuse `reweight_run` for additive resource maps
  and `reweight_bound` only with the required monotonicity premise.
- **Noninterference:** for this client class, changing charges while retaining
  transition values preserves observed behavior by erasure/fusion. Prove that
  bounded claim; a function that returns a Boolean derived from the cost
  projection is an explicit counterexample outside the class. This reconstructs
  a restricted consequence inspired by calf, not its complete modal theorem.
- **Persistent-use boundary:** duplicating an immutable state does not duplicate
  its accounting credit for free. Reuse or construct a branching counterexample
  where each branch spends the same stored potential. The first theorem is for
  one state-threaded trajectory; persistent clients need a separate credit
  splitting/sharing discipline before receiving an amortized guarantee.

The new contribution is a public, compositional bound whose proof clients reuse
without knowing private potential. Existing generic telescoping and symmetric
queue bounds remain implementation lemmas. Introducing Giralf, a general cost
language, or an augmented-simplicial model is not necessary to meet this contract.

## Integration decisions and remaining scope

The ranked recommendation is:

1. **Absorb now:** PFPL's judgment discipline, LF's adequacy obligation, and
   the distinction between static capabilities, dynamic data, and observations.
   Apply these in #203 and in the fragment contracts being studied by #202.
2. **Adapt next:** the LRAT/AFAT shared-client experiment (#210), followed by
   the calf/PFAT-inspired private-potential contract (#211). Reuse current
   squares, naturality, measured transitions, and resource laws. Neither task
   should require replacing ordinary Lean APIs.
3. **Adapt when a consumer selects a fragment:** guarded computation for
   #205/#206; typed closure conversion and intensional representations for
   #128; synthetic normalization for #214. Each needs its own operational
   and observation contract, not just a type-preserving map.
4. **Defer wholesale adoption:** full ModTT/ParamTT, AFAT's univalent internal
   theory, a general Decalf simplicial model, cubical metatheory, directed
   quotient syntax, and Giralf inference. Revisit when a bounded construction
   exposes a concrete limitation that these mechanisms solve.

For [#202](https://github.com/VladimirMarko/conaled/issues/202), the common
abstraction suggested by this assessment is an operation-preserving semantic
comparison plus an explicit class of admissible clients and observations.
Behavior comparisons, cost inequalities, path witnesses, and reduction
simulations require different extra structure. Share their composition laws
where demonstrated; do not erase that extra structure into one unqualified
“correctness” field. The #210/#211 pair is a test of whether one client and
proof can survive a change of representation and a change of quantitative
interpretation with less author bookkeeping.

This assessment leaves source-code ports and full-model metatheorems unverified.
Research completion does not close #208 or implement #210/#211. The formal
follow-ups need statement review, checked positive/negative applications, the
applicable fresh build and proof audit, and independent Standards/Spec review.
Their acceptance should compare against the existing concrete consumers above,
so a new abstraction is justified by an additional reuse or hiding theorem.

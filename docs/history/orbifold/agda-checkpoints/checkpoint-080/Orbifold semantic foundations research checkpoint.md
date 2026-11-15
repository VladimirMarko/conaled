# Status and objectives

Research checkpoint dated 8 November 2026. The current verified code archive is checkpoint 080; three further sheaf modules are undergoing native compilation for checkpoint 081.

The user has authorized two further goals: attempt to settle whether the complete original Myers foundation has a model, and mechanize the external orbifold theorem from its semantic foundations. Existing Agda work and the user's Lean project [conaled](https://github.com/VladimirMarko/conaled) are to be investigated before building independent replacements.

Recovery and proof update, 2026-11-08: execution and direct Git access work. Checkpoint 079 was restored and all 2,262 manifest payloads verified. The pinned Agda compiler and all six smoke checks passed. Nine new ordinary Agda modules have now been promoted after review and native checks; a fresh aggregate accepted all 54 ordinary modules in 71.076 seconds, with complete literal Checking coverage. The 539 unchanged Cubical sources remain bound to their retained accepted receipt; the optional cold replay was interrupted and is not counted as a new successful aggregate. Checkpoint 080 contains 593 distinct modules and 2,294 verified manifest payloads. The constructed presheaf transfer and the externally proved smooth-site transfer are explicitly distinguished from the still-unconstructed full semantic model.

The full original foundation remains unresolved. The full external theorem remains unmechanized. A failure of one proposed model, or of one interpretation of properness, does not prove that all models or all classical extensions are impossible.

## Last verified code baseline

The current verified archive is [myers-orbifolds-agda-checkpoint-080.tar.gz](https://chatgpt.com/library?file_id=libfile_fde3_f-b9a594c60844819189b3d08a00b74082_bcb09d6951dc8191bbb29f2ba3c27d9d&account_id=personal). Its 3,331,049 bytes and all 2,294 manifest payloads were independently verified. Its SHA256 is:

`4a2e2178578a9cfcae3877bbe4157cb69ea622fc7b07ff10a273b2276eecf264`

The supplied checkpoint 079 and its COMPLETION-079.md record the earlier completion boundary. They were re-read after restoration; the original archive hash and all 2,262 manifest payloads were verified. Checkpoint 080 adds actual presheaf constructions and transfer proofs, with its own CHECKPOINT-080.md and bound acceptance evidence.

That baseline includes an ordinary Agda proof of the reduced finite-branch atlas theorem; native algebraic constructions for square-zero extensions and tensor/pullback comparisons; and conditional point-set and smooth geometric results. The higher Cahiers interpretation, its comparison with smooth stacks, and the transfer of the source proof were external mathematical arguments rather than a single compiled semantic construction. Those are now active formalization targets.

# Existing work worth reusing

These findings come from primary papers, author-hosted sources, and official repositories inspected through web access. Upstream statements about compilation are not fresh build results from this session. No dependency has yet been selected or vendored.

| Development | Evidence inspected and useful contribution | Boundary that matters here |
| --- | --- | --- |
| [conaled, inspected commit](https://github.com/VladimirMarko/conaled/tree/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff) | Constructed split sheaf substitution and dependent products; bounded source interpretation; concrete cubical fillers and a nontrivial higher witness; actual smooth algebras/site/KL, manifold full faithfulness, and torsor/action-quotient descent. | Read-only source audit, without a new Lean build. These components do not yet establish one model of the complete Myers foundation or interpretation of unchanged Agda source; internal universes, Glue/univalence, HITs, cohesion, and the exact properness comparison remain separate obligations. |
| [HoTTLean](https://github.com/sinhp/HoTTLean) | Deep MLTT syntax, natural-model semantics, a soundness theorem, and SynthLean. The README reports a sorry-free groupoid construction for Π, Σ, and Id. | The README says higher inductive types are unsupported and the broader model construction is incomplete. |
| [SynthLean paper](https://voidma.in/assets/papers/2026nawrocki_certifying_proof_assistant_synthetic_mathematics_lean.pdf) | Theorem 3.1 gives interpretation soundness; Lemma 3.2 handles semantic substitution. | The CPP 2026 version postulates injectivity of type formers for its certifying typechecker. The paper explicitly separates this dependency from semantic soundness. Audit any chosen current revision independently. |
| [Brunerie and de Boer initiality](https://guillaumebrunerie.github.io/pdf/initialityHoTTEST.pdf) | The 2020 presentation describes an Agda proof of MLTT initiality, including universes, identity types, and substitution, and identifies release v2.0. | Its metatheory uses Prop, function and propositional extensionality, and postulated quotients with computation. It cannot be imported unchanged into our ordinary safe fragment. |
| [Xu's sheaf semantics](https://cj-xu.github.io/ContinuityType/) | Actual contexts, dependent families, terms, comprehension, and gluing for a uniform-continuity site; [comprehension source](https://cj-xu.github.io/ContinuityType/CwF.Sheaf.ContextComprehension.html) was inspected. | The index advertises Agda 2.4.2. This is a specific ordinary sheaf construction, not a completed higher Cahiers model. Its sheaf section should not be credited with every type former listed in the separate set-model section. |
| [BiSikkel](https://github.com/JorisCeulemans/bisikkel) | Presheaf semantics, intrinsically typed multimode simple syntax, substitution, interpretation, and proof soundness. | Its program language is multimode simple type theory. It does not supply the required dependent higher smooth model by itself. |
| [Orton and Pitts](https://lmcs.episciences.org/5028/pdf) | Internal constructions of cubical-model operations, with an [archived Agda artifact](https://www.repository.cam.ac.uk/items/17c0e797-0972-4d20-8cbd-aaa881c3333f). | The formal development assumes topos/interval axioms and uses impredicative propositions and rewriting. It is a model-construction component whose ambient assumptions still need an instance. |
| [Licata, Orton, Pitts, and Spitters](https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.22/LIPIcs.FSCD.2018.22.pdf) | Theorem 5.2 constructs a classifying universe from a tiny interval in crisp type theory; the authors provide Agda-flat code. | Section 6 explicitly leaves parts of the complete fibrancy/univalence development unfinished. Agda-flat's exact relationship to the stated crisp calculus is also identified as needing further work. |
| [Coquand, Höfer, and Sattler 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.31) | A recent mathematical construction of higher presheaf/sheaf models, with applications to synthetic algebraic geometry and other synthetic theories. The [paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol380-lics2026/LIPIcs.LICS.2026.31/LIPIcs.LICS.2026.31.pdf) uses cubical models, descent, and explicit universe assumptions. | No Agda implementation was identified in the inspected paper and publisher record. Its applications do not establish Myers's joint axioms. Identifying the presented higher objects with the intended classical setting remains a separate obligation. |
| [Coquand, Ruch, and Sattler](https://arxiv.org/abs/1912.10407) | Earlier constructive sheaf-model construction using descent and left-exact localization. | A mathematical route to formalize; not evidence that our smooth instance is already machine checked. |
| [DCHoTT-Agda](https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda) | Relevant synthetic differential geometry. The inspected source explicitly postulates the infinitesimal modality and associated laws. | Useful synthetic proofs, but those postulates do not construct an external model. |
| [agda-categories](https://github.com/agda/agda-categories) | Generic category-theory infrastructure designed around safe, without-K, setoid-enriched mathematics. The README identifies v0.3.0 with Agda 2.8.0 and stdlib 2.3. | Compatibility and required semantic structures need a pinned source/build audit; a category library alone is not a model of dependent type theory. |

## Consequence for implementation

The most promising reuse is layered: generic category and sheaf infrastructure; a construction of model operations and universes; and a separately verified interpretation of syntax.

Lean has relevant existing [smooth-manifold definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html) and [sheafification infrastructure](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Sheafification.html). The latter distinguishes an assumed HasSheafify interface from the [actual instances in LeftExact](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/LeftExact.html). The coefficient category and universe hypotheses must be checked in any application.

The end-to-end semantic formalization remains in Agda. Conaled and other Lean developments supply reference constructions and proof strategies to reconstruct and check in Agda. The completed [comparative report](https://chatgpt.com/space/page_f437e988f088819191f404393d920aad) assesses geometry, model construction, exact source interpretation, and constructive dependencies, with concrete suggestions for conaled's development.

# The original foundation question

The positive target is an explicit nondegenerate model of the entire chosen signature, with every original axiom validated together and with universe and crisp-context restrictions preserved.

The negative target is a contradiction derived from the original signature, or a precise theorem ruling out a stated class of interpretations. Additional compatibility hypotheses must remain visible.

Myers's [Axiom 2 and Definition 3.1.1](https://arxiv.org/pdf/2205.15887) apply to crisp types and identify discreteness with the canonical constant-map comparison being an equivalence. In the indicated stack interpretation, discreteness uses the counit from the constant object on global sections. This exact comparison, rather than an unspecified equivalence of objects, is what the following lemma tests.

# A conditional obstruction that transfers between models

## Statement

Let E and C be topoi, or infinity-topoi, and suppose there is an adjunction

```math
L:\mathcal E\rightleftarrows\mathcal C:U,
\qquad L\dashv U,
```

where L is left exact and U is fully faithful. Let R_E and R_C be chosen line objects, with a specified equivalence L(R_E) ≃ R_C.

Write Γ for global sections and Δ_E for the constant-object functor of E. Suppose C contains an object F satisfying all three conditions:

```math
c_F:F\longrightarrow F^{R_{\mathcal C}}\text{ is an equivalence},
\qquad \Gamma_{\mathcal C}F\simeq 1,
\qquad F\not\simeq 1_{\mathcal C}.
```

Here c_F is the transpose of the projection F × R_C → F.

Assume U(F) is represented by a crisp type in a universe to which the candidate's RealFlat axiom applies, and that its flat modality is interpreted by Δ_E Γ_E.

Then that candidate cannot satisfy the implication in RealFlat which makes every R_E-null crisp type flat-discrete.

## Proof

For every object T of E, exponential adjunction, L ⊣ U, and product preservation give natural equivalences:

```math
\begin{aligned}
\operatorname{Map}_{\mathcal E}(T,(UF)^{R_{\mathcal E}})
&\simeq \operatorname{Map}_{\mathcal E}(T\times R_{\mathcal E},UF)\\
&\simeq \operatorname{Map}_{\mathcal C}(L(T\times R_{\mathcal E}),F)\\
&\simeq \operatorname{Map}_{\mathcal C}(LT\times R_{\mathcal C},F).
\end{aligned}
```

Under these equivalences, postcomposition with c_UF corresponds to precomposition with the projection LT × R_C → LT. The latter is an equivalence on mapping spaces because c_F is an equivalence:

```math
\operatorname{Map}_{\mathcal C}(LT,F)
\xrightarrow{\ \pi^*\ }
\operatorname{Map}_{\mathcal C}(LT\times R_{\mathcal C},F).
```

Adjunction identifies the source with Map_E(T,UF). Thus Map_E(T,c_UF) is an equivalence for every T. By Yoneda, the canonical map c_UF is an equivalence. In particular, this argument proves nullness of the specified constant map, not merely the existence of some abstract equivalence between UF and its exponential.

Since L preserves the terminal object,

```math
\Gamma_{\mathcal E}(UF)
=\operatorname{Map}_{\mathcal E}(1,UF)
\simeq\operatorname{Map}_{\mathcal C}(L1,F)
\simeq\Gamma_{\mathcal C}F
\simeq1.
```

RealFlat, applied with the stated crispness and universe admissibility, now makes the counit Δ_E Γ_E(UF) → UF an equivalence. The constant-object functor preserves the terminal object, so UF ≃ 1_E.

Full faithfulness of U makes the adjunction counit LUF → F an equivalence. Applying L to UF ≃ 1_E consequently gives

```math
F\simeq LUF\simeq L1_{\mathcal E}\simeq1_{\mathcal C},
```

contradicting the third hypothesis. This proves the conditional obstruction.

The proof only uses preservation of the terminal object and the displayed products with R; full left exactness is a convenient sufficient hypothesis. In an ordinary topos, Map can be read as a hom-set. In an infinity-topos, it means the mapping space.

## What must be proved before applying it

The existing Cahiers de Rham counterexample is a proposed input F for this theorem. Its construction, line-invariance, trivial global sections, and nontriviality must all be included in the new semantic formalization. The finite polynomial certificate alone establishes neither the sheaf construction nor its line-invariance.

For a larger candidate setting, construct the actual functors L and U, prove the adjunction and full faithfulness, prove the comparison of line objects, and verify the admissibility of U(F) in the required universe. Merely including the same infinitesimal probes in a larger site does not establish these properties.

This lemma can exclude a class of candidate interpretations if those hypotheses are verified. It does not rule out every model of the original axioms. To obtain a universal nonexistence theorem, one would have to derive an appropriate counterobject or equivalent contradiction from the original axioms themselves. That step is open.

Status of this lemma: new written mathematical proof, not machine checked.

# Concrete completion criteria for the semantic formalization

The following are construction requirements. Records exposing their interfaces are useful during development, but completion requires actual inhabitants constructed from the declared external foundations.

| Component | Concrete output required | Completion test |
| --- | --- | --- |
| Existing work and reproducibility | Inspect conaled; pin dependency revisions, compiler versions, and imported theorem closures. | Reproduce the relevant builds and report actual transitive axioms and parameters. |
| Smooth algebra | Actual real numbers, smooth functions, C-infinity operations, finite Weil algebras, and the necessary tensor/localization comparisons. | Evaluation and Taylor lemmas about the actual structures, including parameter dependence. A generic ring record is insufficient. |
| Formal site | Objects, all required morphisms, composition, identities, coverage, and a proved Grothendieck topology. | Include maps mixing smooth coordinates and nilpotent coefficients; prove subcanonicity or use a proved replacement. |
| Sheaves and higher objects | Actual sheafification/descent or a justified equivalent presentation of higher sheaves, with chosen size bounds. | Construct the localization and demonstrate its universal property and preservation properties in the needed coefficient category. |
| Dependent type semantics | Contexts, substitutions, families, comprehension, identity, Π and Σ operations, relevant truncations/quotients, and universes. | Prove substitution stability, computation laws, and closure at the declared levels. Validate univalence and additional operations when the source signature requires them. |
| Smooth geometry instance | Embed the actual manifolds and smooth maps; construct infinitesimal prolongations and local lifting. | Prove comparisons for the smooth line and charts from calculus, rather than assuming an abstract smoothness package. |
| Quotient and descent | Construct the quotient stack of the actual groupoid, an effective atlas, and compatibility with refinement. | Recover the Čech groupoid and retain isotropy; prove Morita invariance and the required mapping comparisons. |
| Exact proof interpretation | A checked proof term in the supported source calculus and its interpretation. | Prove the type and term substitution equations and instantiate semantic soundness on that exact term. |
| External theorem | A theorem about an actual proper étale Lie groupoid and its resulting formal object. | Recover its classical smooth quotient stack and the intended finite-local/infinitesimal properties, with all preceding constructions instantiated. |
| Original Myers foundation | Validate the complete original signature in one model, or derive a contradiction with explicit hypotheses. | Keep this result distinct from the reduced theory and from a changed meaning of a modality or properness. |

## The source-language boundary

First freeze the ordinary fragment actually used by the reduced atlas theorem: its identity elimination, Π and Σ constructions, universe levels, bounded truncation, and the explicit geometric parameters. Record the difference between that fragment and the full Cubical Agda language.

A suitable interpretation must satisfy the following equations for well-typed substitutions:

```math
\llbracket A[\sigma]\rrbracket
=\llbracket A\rrbracket[\llbracket\sigma\rrbracket],
\qquad
\llbracket t[\sigma]\rrbracket
=\llbracket t\rrbracket[\llbracket\sigma\rrbracket].
```

The chosen strict model must implement these equalities, or a separately proved coherence construction must justify its strict presentation. Abstract equivalences between the underlying objects do not suffice to silently replace the source's computation rules.

SynthLean is a reference for exact source interpretation and substitution proofs. Its generic semantic theorem does not certify this Agda source. The Agda development must construct an interpretation or initiality theorem for its own specified source fragment and state the metatheoretic assumptions explicitly.

## The geometric boundary

For the reduced theory, the intended end-to-end statement has the following form: given an actual proper étale Lie groupoid G, construct its formal semantic object Q(G), prove the reduced orbifold predicate of Q(G), and prove that restriction to ordinary smooth probes recovers the classical quotient stack [G]. Refinement and mapping statements must be proved at the stack level.

The properness hypothesis is the actual classical properness of the anchor map (s,t). Any implication involving the paper's internal Dubuc–Penon predicate is a separate theorem to prove or refute under its exact interpretation.

A fully faithful extension of smooth stacks need not preserve all pullbacks. Its actual preservation properties must be checked before using it to interpret dependent types. The prior comparison argument's non-left-exact extension is not an automatic interpretation functor.

# First nontrivial test of the complete interpretation

Use the action of the two-element group on the ordinary real plane by v ↦ −v. The target example is the quotient stack of this action, not merely its orbit space.

The action groupoid has object manifold R² and arrow manifold {+1,−1} × R². Its source is s(ε,v)=v and its target is t(ε,v)=εv. Composition multiplies the signs.

There is a short external verification of its basic geometry. On each sign component the source is the identity and the target is either the identity or negation, hence a diffeomorphism. Therefore both maps are local diffeomorphisms. For a compact subset K of R² × R², its intersection with either graph {(v,εv)} is compact because each graph is closed. The graph parametrization is a homeomorphism, so the inverse image of K on each sign component is compact. There are only two components, proving properness of the anchor.

At v=0 both signs stabilize v. At v≠0 only +1 does, since −v=v would imply 2v=0 and hence v=0. Thus the example detects whether the construction retains a nontrivial isotropy group.

The first complete formal test should establish:

1. The actual smooth groupoid and its properness and étaleness.

2. Its formal quotient and the effective atlas, constructed from the chosen site and model.

3. The reduced internal theorem obtained by interpreting the checked source proof.

4. Recovery of the ordinary quotient stack and its stabilizers.

5. Agreement after a nontrivial open-cover refinement of the atlas.

6. The first-order infinitesimal comparison at the singular point and away from it.

This is an intermediate test of the general construction. Its success would not settle the full original Myers foundation or complete the theorem for arbitrary groupoids. It is deliberately strong enough to expose loss of isotropy, missing descent, or a transfer that only works for discrete examples.

# Next executable work and current blockers

The conaled source audit now uses the clean, shallow checkout at commit 5867d02ecfc290b7a3b7505cc94acbb98f4f49ff, including its source modules, README, dependency pins, current language-direction document, and relevant architecture and proof-status notes. The inspected Lean source contains substantial constructed semantics and geometry. No Lean rebuild or independent whole-repository axiom audit has been run in this recovered environment.

Execution is available again. The initial disk check found 59.67 GiB available out of 62.94 GiB and ample free inodes; current disk exhaustion is not the blocker. The earlier checkout was absent from the initial mounted workspace, but that observation does not establish the cause of the earlier outage. Identical direct Git queries succeeded for both HoTTLean and conaled. The web retrieval route still returned DisabledError for conaled while retrieving HoTTLean; this is a route-specific retrieval failure, not evidence of different GitHub permissions. The supplied checkpoint 079 archive is 3,271,309 bytes, with SHA-256 8a4e15f8b52b7d43688d7f9da94c4261577b4a2adc9a3a2dc9d90baa3600185f. It has been extracted, all 2,262 manifest entries rehashed successfully, and the pinned Agda compiler installed and verified. Fresh proof checking is in progress.

The current native work constructs actual small sites and sheaves, terminal objects and binary products, and right-Kan preservation of sheaves by local gluing under an explicit cover-lifting condition. Three candidates have passed independent mathematical review and are undergoing native compilation. The next mathematical obligation is an actual restriction-preserves-sheaves proof and sheaf adjunction; the smooth instances, dependent universes and exact source interpretation remain further work. No interface that assumes a missing conclusion counts as constructing it.

Future verified code checkpoints should retain source hashes, compiler and dependency pins, completed native-check receipts, and an explicit separation between constructed definitions, proved theorems, supplied parameters, and remaining semantic obligations. This research checkpoint must not be substituted for such a code archive.

## Reuse audit after recovery

The checked-out source materially improves the starting point. The following are source-inspected constructions, not new build claims.

| Required component | Concrete conaled evidence | Scope retained |
| --- | --- | --- |
| Dependent sheaf families and substitution | [SplitSheaf.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SplitSheaf.lean) constructs reindexing through actual sheaf pullbacks and proves identity/composition laws. | Ordinary Type-valued sheaves. |
| Dependent products | [SplitFunctionSheaf.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SplitFunctionSheaf.lean) constructs the function-family sheaf through an element-site equalizer; SplitSheafPi proves beta, eta, and substitution comparisons. | This constructs closure rather than assuming it as a model field; it does not supply a higher universe. |
| Source interpretation | [DependentFunctionSheafSoundness.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/Internal/DependentFunctionSheafSoundness.lean) proves soundness for the admitted dependent-function syntax. Guarded dependent judgments also have interpretation and substitution theorems. | These are specified fragments, not an importer for arbitrary Agda derivations. |
| Higher identity evidence | [CocycleHigherNonzero.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/Internal/Cubical/CocycleHigherNonzero.lean) proves that a selected second identity cannot be erased even by a third identity. Its model has a constructed lawful cocycle filler. | The [advertised cubical fragment](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/docs/research/cubical-model-construction.md) excludes internal universes, Glue/univalence, HITs, and cohesive geometry. |
| Actual smooth site and calculus | [SmoothAlgebra.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothAlgebra.lean) uses Mathlib real smooth functions; the principal-cover topology and its subcanonicity are proved. [SmoothOpenKL.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothOpenKL.lean) instantiates the constructed first-order KL equivalence. | Finite smooth presentations and the specified topology; the KL theorem permits arbitrary sheaf parameters but is first order. |
| Classical manifold comparison | [SmoothManifoldFullFaithfulness.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothManifoldFullFaithfulness.lean) reconstructs actual Mathlib smooth maps from sheaf arrows and proves both inverse laws. | Finite-dimensional real boundaryless manifold models at the stated universe; global sheaf-arrow equality includes non-real stages. |
| Quotients and descent | [SheafTorsorDescent.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafTorsorDescent.lean) and [SheafActionQuotientDescent.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafActionQuotientDescent.lean) construct descended objects, compatible arrows, and recovery. | Torsors and action-quotient objects with their arrows, not only orbit sets. |
| Nontrivial geometric examples | [SmoothQuarterTurnQuotient.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothQuarterTurnQuotient.lean) contains the quarter-turn disk quotient with four origin automorphisms and trivial nonzero stabilizers, plus a separate ineffective scalar action with distinct arrows. The classical derivative comparison for coherent transport is the C4 disk action at the origin. [SmoothTorsors.lean](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/SmoothTorsors.lean) constructs a nontrivial clutching torsor and proves effective descent. | These existing C4 examples should be reused before recreating a weaker sign-action example. |

The next semantic bridge must combine the necessary capabilities in the selected smooth setting and interpret the exact admitted source judgments. Separate constructed sheaf and cubical models do not automatically provide their combination. The historical #103 experiment gate must be read with the current #323 successor decision and the discharged bounded higher-consumer gate; it is not a blanket prohibition on further semantic work. The original full Myers model-existence question and an unrestricted no-model theorem remain open.

## Interim durability checkpoint

The earlier [interim recovery bundle](https://chatgpt.com/library?file_id=libfile_fde3_f-09524913e038819181942fcfdd487e8a_bcb09d6951dc8191bbb29f2ba3c27d9d&account_id=personal) remains a historical unaccepted snapshot. Its SHA256 is `3be42bc850c0efcebb5da2ef3eca728de6d145250c08b2b44aed02633d706e16`, binding 38 outer payloads and the original 2,262-payload checkpoint 079. The accepted checkpoint 080 above supersedes that snapshot for continuation.

The accepted categorical theorem derives transported real-line nullity, singleton global points, and nonterminality; it constructs invertibility of the actual exponential constant map and refutes invertibility of the actual Delta-Gamma counit. The category interface separates object and hom universes and takes constants only of small sets. The specified smooth-site transfer has passed external mathematical review. Neither result constructs the full original Myers model or interprets unchanged Agda source.

## External site transfer and concrete presheaf progress

The reviewed external argument constructs a full inclusion of finite-Weil open probes into two specified larger sites: finitely presented smooth algebras with principal-open covers, and finitely generated germ-determined smooth algebras with the reflected localization topology. It verifies pullback/refinement of generated covers, proves that restriction preserves sheaves, and constructs a fully faithful right Kan extension. Terminal objects, canonical products, and the represented real line then give the precise conditional transfer of the de Rham obstruction. The larger-site witness is the constructed right extension; it is not identified with a directly defined de Rham sheaf on every larger-site algebra. Literal Cartesian probes require an open/ball-basis comparison. References: [Bunge–Dubuc, 1986](https://www.numdam.org/article/CTGDC_1986__27_3_3_0.pdf), [Kock, Synthetic Differential Geometry](https://users-math.au.dk/kock/sdg99.pdf), [Stacks 7.20](https://stacks.math.columbia.edu/tag/00XI), and [Stacks 7.21.7](https://stacks.math.columbia.edu/tag/00XT).

The seven accepted presheaf modules construct small set-valued presheaves, restriction and canonical terminal/product comparisons, the right Kan extension and its adjunction, full faithfulness, constants/global sections with the actual evaluation counit, represented-line restriction, exponentials with the actual constant map, and the assembled conditional obstruction instance. Together with the two categorical transfer modules, they passed the fresh 54-module ordinary aggregate. Their logical parameter is FunExt at the small value universe; presheaf objects lie in the next universe, without resizing. The base categories, fully faithful inclusion, line and null singleton-global nonterminal witness remain inputs. Actual smooth sites, sheafification, that de Rham witness, crisp rules, universes and source interpretation are not constructed by these nine files.

The prescribed Nix environment for conaled was attempted through a workspace-local official nix-portable release. It could not start: Nix needed unavailable `/proc/self/exe`; the fallback also encountered unavailable procfs data and `ptrace(TRACEME): Operation not permitted`. No Lean build ran and no alternative build bypass was used. The conaled findings therefore remain a pinned source audit. Agda execution is working. The user has since clarified that conaled is a reference for the Agda-only end-to-end goal, so this Lean build limitation is an inspection limit and does not block the intended Agda continuation.
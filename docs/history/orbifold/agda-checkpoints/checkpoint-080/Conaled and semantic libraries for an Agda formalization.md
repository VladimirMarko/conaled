The complete repository report, source notes, and cited Agda files are included in [checkpoint 080](https://chatgpt.com/library?file_id=libfile_fde3_f-b9a594c60844819189b3d08a00b74082_bcb09d6951dc8191bbb29f2ba3c27d9d&account_id=personal). Public-source links below remain direct links to the papers and pinned repositories.

Assessment date: 2026-11-08. Conaled revision:
`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`.

## 1. What the comparison establishes

The intended deliverable is an end-to-end Agda proof, including the semantic
constructions needed to reach an external geometric theorem. Conaled is a
reference for mathematics and proof architecture; a Lean theorem will not be
inserted as an unchecked step in that proof. Among the components inspected,
conaled provides the strongest collection of actual smooth geometry,
manifold realization and quotient descent. Other libraries provide stronger
examples of particular source-language interpretations, presheaf or sheaf
semantics, and universe constructions. Their strengths are complementary.

This evidence supports attempting a constructive development. It does not
establish that the exact conaled site, its analytic foundations, or the whole
original Myers foundation has a constructive Agda model. A constructed
ordinary sheaf model and a constructed higher model must still be joined by
proved compatibility before they constitute a higher smooth model.

This is a source review, not a new build of the compared libraries or an
exhaustive survey of the field. The conaled audit inspected the pinned source
and recorded its file identities in CONALED-REUSE-080.json (`CONALED-REUSE-080.json`, in checkpoint 080).
The required Nix environment could not run in this workspace; no new Lean
build or complete kernel-axiom audit is claimed. The detailed constructions
and their limits are recorded in CONALED-REUSE-080.md (`CONALED-REUSE-080.md`, in checkpoint 080).
Current Agda validation is recorded separately in the checkpoint receipts.

| Source | Useful constructed component | Boundary for this project |
| --- | --- | --- |
| [Conaled](https://github.com/VladimirMarko/conaled/tree/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff) | Ordinary split sheaves, dependent products, smooth presentation site, first-order KL, manifold full faithfulness, torsor and action-quotient descent | Smooth sheaves and the higher cocycle model remain separate; exact Agda interpretation and the constructive port are additional work |
| [HoTTLean / SynthLean](https://github.com/sinhp/HoTTLean) | Deep MLTT syntax, certifying frontend, natural-model soundness, and a groupoid model | The inspected model does not supply smooth cohesion; current syntax excludes higher inductive types |
| [Brunerie–de Boer](https://github.com/guillaumebrunerie/initiality/tree/v2.0) | Agda initiality, including interpretation commuting with substitution | Uses a declared quotient/extensionality metatheory and interprets into a supplied structured model |
| [BiSikkel](https://github.com/JorisCeulemans/bisikkel) | Dependent presheaf model, modal simple-type interpretation, substitution and sound proof checking | The implemented program language is not full dependent MTT; its current equality representation obstructs natural semantic universes |
| [Xu’s ContinuityType](https://cj-xu.github.io/ContinuityType/) | Actual sheaf CwF, dependent reindexing and context comprehension | The continuity site differs from the smooth site; the inspected sheaf chapters do not establish our entire universe/type-former package |
| [Orton–Pitts](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2016.24) and [Licata–Orton–Pitts–Spitters](https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.22/LIPIcs.FSCD.2018.22.pdf) | Internal cubical-model components and a fibration-classifying universe using a tiny interval and crisp contexts | Additional interval/cofibration hypotheses and a precise source-theory boundary remain; these do not supply the smooth instance |

## 2. What to learn from the semantic libraries

HoTTLean names an explicit soundness theorem, `ofType_ofTerm_sound`, connecting
its source syntax to natural-model semantics. Its groupoid construction
supports Pi, Sigma and identity types; its HoTT0 example supplies univalence
for h-sets. The [SynthLean paper](https://voidma.in/assets/papers/2026nawrocki_certifying_proof_assistant_synthetic_mathematics_lean.pdf)
also distinguishes a semantic hierarchy from actual object-language universe
codes. Its chosen comprehension pullbacks are supplied explicitly instead
of obtained through choice. These are useful standards for an exact
interpretation, without implying that every dependency is constructive.
Sound interpretation is enough to transfer a source theorem; full initiality,
including uniqueness of all interpretation morphisms, is a stronger target.

The [Brunerie–de Boer author presentation](https://www.math.uwo.ca/faculty/kapulkin/seminars/hottestfiles/Brunerie-2020-09-10-HoTTEST.pdf)
makes the substitution obligation especially concrete: it identifies
`interpretationsubstitution.agda` separately from initiality existence and
uniqueness. Its declared MLTT includes Pi, Sigma, identities, naturals, sums
and Tarski universes. The same presentation specifies strict `Prop`, function
and propositional extensionality, and postulated quotients with a computation
rule. We should reuse the architectural lesson while accounting for those
assumptions; this is not an unchanged import into our safe Agda closure.

The [BiSikkel paper, Sections 6.1–6.3](https://anuyts.github.io/files/2025/bisikkel-popl.pdf)
provides another useful distinction. Its underlying presheaf model is
dependent, while programs inhabit modal simple type theory and dependent
propositions inhabit a separate logical framework. Function extensionality
is an explicit metatheoretic assumption; a guarded-stream extraction example
adds bisimilarity-as-equality. The current mixture of isomorphism-based
presheaf equality and pointwise term equality limits semantic universes.
That is a warning about an implementation choice, not an impossibility result
for presheaf universes generally. Adopting its modular design is more justified
than assuming its entire representation suits our intended universe.

Xu’s actual [sheaf types and terms](https://cj-xu.github.io/ContinuityType/CwF.Sheaf.TypesAndTerms.html)
and [context comprehension](https://cj-xu.github.io/ContinuityType/CwF.Sheaf.ContextComprehension.html)
are direct guides for the next Agda layer: reindex dependent families, prove
their gluing, and construct extension from the total Sigma carrier. These are
constructions, not a declaration that every family is a sheaf. Assumptions
vary across the project’s extensionality/setoid variants. Type-former chapters
for its set model must not be silently credited to every sheaf chapter.

The crisp-universe work is valuable precisely because it constructs a
classifier rather than renaming an external universe level. However,
[Licata–Orton–Pitts–Spitters, Remark 4.2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.22/LIPIcs.FSCD.2018.22.pdf)
warns that the Agda-flat implementation supports more than the crisp theory
presented, with their precise relationship requiring further work. Tinyness
of its cubical interval is also a different hypothesis from tinyness of
Myers’s double-negation infinitesimal neighborhood.

The newer [Coquand–Höfer–Sattler paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol380-lics2026/LIPIcs.LICS.2026.31/LIPIcs.LICS.2026.31.pdf)
offers a constructive, predicative route through cubical presheaves and sheaf
models. Its introduction nevertheless explicitly conjectures that these
models present the intended higher categories of sheaves. This review has
not established a reusable Agda implementation or our exact smooth instance.
[agda-categories](https://github.com/agda/agda-categories) is useful safe,
setoid-enriched categorical infrastructure, requiring an adapter to our
identity-equality interfaces. [DCHoTT-Agda](https://github.com/felixwellen/DCHoTT-Agda)
provides synthetic formal-disk mathematics with an axiomatized coreduction
modality. Neither fact alone supplies the missing external interpretation.

## 3. Conaled contains substantive geometry worth reconstructing

[SplitSheaf](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SplitSheaf.lean)
proves substitution closure by comparing the reindexed total presheaf with
an actual sheaf pullback. [SplitFunctionSheaf](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SplitFunctionSheaf.lean)
constructs dependent functions through a compatible-function sheaf and an
equalizer condition; sheafhood of `piType` is a conclusion. These proofs offer
concrete models for our Agda implementation. Their imported pullback,
exponential and element-site machinery also needs Agda constructions.

[SmoothAlgebra](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothAlgebra.lean)
uses actual real smooth functions, constructs the free smooth algebra, and
proves its universal property. The finite-presentation site and scalar
descent support [SmoothOpenKL](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothOpenKL.lean).
The underlying [geometric KL proof](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothGeometricKL.lean)
evaluates at the universal dual element, extracts coefficients, and proves
both inverse laws for the actual affine map, for arbitrary sheaf parameters.
This establishes first-order KL, not all Weil comparisons or RealFlat.

[SmoothManifoldFullFaithfulness](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothManifoldFullFaithfulness.lean)
reconstructs smooth maps from full sheaf arrows and proves both inverse laws
under its stated manifold hypotheses. [SheafTorsorDescent](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafTorsorDescent.lean)
constructs descended torsors from compatible local sections. The
[action-quotient descent](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafActionQuotientDescent.lean)
retains equivariant maps and arrows. Effectiveness is proved, not an input
field asserting the desired conclusion. This retained arrow structure is
essential for isotropy.

Conaled already proves bounded source soundness as well:
[DependentFunctionSheafSoundness](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/Internal/DependentFunctionSheafSoundness.lean)
provides `beta_sound`, `eta_sound`, `dep_sound` and `func_sound` for its declared
fragment. This is real interpretation work. The additional obligation is to
cover the exact source language and semantic operations required here.

Conaled also constructs a separate higher cocycle model with a non-erased
second identity. Its [higher witness](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/Internal/Cubical/CocycleHigherNonzero.lean)
does not yet belong to a simultaneous smooth sheaf model. Likewise,
[LocalUniverses](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/LocalUniverses.lean)
constructs local presentations and reindexing for split families, rather than
an object-language universe classifying every admitted family. Both are
useful achievements with additional compatibility obligations.

## 4. Constructive feasibility: four distinctions that matter

**A host language does not decide a theorem’s logical dependencies.** A Lean
`noncomputable section` permits certain definitions; it is not an axiom
certificate. A `classical` command can be irrelevant to the final proof, while
imported constructions can introduce classical dependencies without either
spelling nearby. The constructive assessment therefore needs per-declaration
dependency evidence and mathematical alternatives, not keyword counts.

**Arbitrary selection differs from unique gluing.** In
[SmoothQuotient](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothQuotient.lean),
a representative is selected for every quotient element, then independence
is proved. Finite-arity quotient elimination offers a plausible replacement
for that selector. In [SmoothOpenDescent](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothOpenDescent.lean),
representatives are selected over an arbitrary cover, which needs a more
substantial reorganization. Refining by all witnesses may help, but does not
itself prove gluing.

By contrast, [SheafTorsorLocal](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafTorsorLocal.lean)
selects local group elements whose complete solution is unique. In a
constructive type theory with suitable truncation, mere existence can be
eliminated into a solution type proved to be a proposition. This does not
require arbitrary choice. The uniqueness proof and its size must actually
be supplied; Lean’s use of a choice wrapper does not perform that Agda proof.

**Negative nonzero is not positive apartness.** The cover predicate in
[SmoothOpenCover](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothOpenCover.lean)
requires every real point to make some covering function nonzero. Its
`ambient_cover` proof splits on whether a defining relation is nonzero.
[SmoothInverseGraph](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothInverseGraph.lean)
also uses a classical complement argument. Constructively, `not (x = 0)`
does not generally supply positive separation from zero and the corresponding
inverse data. An apartness-based cozero basis is a possible replacement, but
its localization, cover and classical-comparison theorems must be proved.
Changing the predicate silently would change the model under review.

Analytic existence remains substantial: conaled uses a globally smooth
function defining an arbitrary open set and smooth partitions of unity for
[arbitrary ideal gluing](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothIdealArbitraryGluing.lean).
A basis carrying explicit functions or partitions could isolate a
constructive core. Equivalence with the intended arbitrary-open site would
then be an additional theorem. Eliminating representative choices does not
supply these analytic results.

**Proof irrelevance differs from excluded middle.** Lean’s irrelevance of
proofs in `Prop` simplifies certificate and transport equalities; it does not
by itself decide every proposition. A set-valued Agda port can prove the
relevant law types are propositions, using its stated extensionality where
needed. It must also reproduce coherence: [SplitSheafPi](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SplitSheafPi.lean)
uses proof irrelevance in substitution transport. Higher identities require
their own semantic types. Interpreting them as ordinary Lean equality would
erase the isotropy the quotient theory needs.

## 5. The next external comparison is precise and bounded

At the inspected revision,
[SmoothConstantOrdinary.ordinaryLocallyConstant](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SmoothConstantOrdinary.lean)
maps a group-sheaf section on an ordinary open to a locally constant function.
The missing bounded step is an inverse on ordinary opens, with both inverse
laws and restriction compatibility. A proposed construction covers the open
by locally constant label fibers, refines by principal opens, glues constant
labels, and uses separatedness for uniqueness. This is a proof plan, not an
accepted new equivalence or a whole-repository absence claim.

Combined with manifold full faithfulness and
[chartArrowEquiv](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/SquareKit/SheafActionQuotient.lean),
that equivalence should first identify chart arrows over ordinary open
domains with locally constant group labels satisfying the action equation.
Identity, composition and restriction must agree for the actual maps; the
current label convention `m = a.onMap g n` uses inverse labels relative to
conventional forward action arrows. Extending the comparison to arbitrary
manifold bases requires atlas gluing. Descent can then compare compatible
Cech data and torsor objects. This neither trivializes every torsor nor
identifies an orbifold with its coarse orbit set.

The explicit [quarter-turn application](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Applications/Orbifolds/QuarterTurn.lean)
offers a suitable first geometric target. Conaled currently defines `C4`
using roots of unity. Our proposed Agda reconstruction can instead use an
explicit four-element group and the rotation `(x,y) ↦ (−y,x)`, avoiding a
choice of roots or orbit representatives. Its action groupoid still needs
actual etaleness and compact-preimage properness proofs in Agda. The finite
closed-graph argument is a promising route, provided the chosen compactness
and separation lemmas are established. Finite stabilizers alone are not
properness. The word “classical” can describe external geometric objects
without prescribing unrestricted choice, but constructive equivalence with
all standard orbifold presentations remains a separate question.

A direct theorem about this external groupoid is an intermediate result with
its own value. It does not replace the requested interpretation of the
internal theorem. That further step must preserve the relevant quotient,
identity, test-family and descent operations. Conversely, the
specified-site RealFlat obstruction (`REAL-FLAT-DE-RHAM-078.md`, in checkpoint 080) and its
site-transfer analysis (`SITE-TRANSFER-080.md`, in checkpoint 080) concern particular proposed
semantic identifications. They do not prove that every model or every
external orbifold extension is impossible. A revised theory may retain the
geometric constructions while changing incompatible source assumptions, but
that revision and its exact theorem must be stated explicitly.

## 6. Source axioms and priorities for the next development

The original source is not wholly free of excluded middle. Myers’s
[Axiom 1, Section 3.1, page 24 of arXiv:2205.15887v1](https://arxiv.org/pdf/2205.15887v1)
([HTML text](https://arxiv.org/html/2205.15887v1#S3.SS1)) requires excluded
middle for crisp propositions. Our native
Crisp.agda (`../../src/Orbifolds/Crisp.agda`, in checkpoint 080) defines
`CrispExcludedMiddle = (@♭ P : hProp ℓ) → Dec (P .fst)` as a hypothesis type,
not a globally installed postulate. An interpretation of the unchanged source
must justify this operation on the intended crisp propositions. A constructive
replacement must identify the retained fragment; removing classical selectors
from geometry does not discharge the original crisp axiom.

The revised seven-file `DerivedAtlasOrbifold` theorem has no EM, DNE or choice
assumption. Its displayed inputs include bounded truncation, weak function
extensionality and actual atlas/test data; their interpretation still needs
proof. The dependency audit (`DEPENDENCY-BOUNDARIES-077.md`, in checkpoint 080) separates this
closure from point-set applications with explicit classical and selected-data
inputs. The new nine-module categorical/presheaf branch (`../../src/Orbifolds/Intensional/PresheafObstructionInstance.agda`, in checkpoint 080)
has weak `FunExt` as its explicit logical parameter. It constructs ordinary set-valued presheaf
operations, not infinity-category semantics; its base categories and the
counterexample object with nullity, singleton global sections and
nonterminality remain mathematical inputs. Its conditional RealFlat result
requires the actual semantic identification before application to native
crisp syntax. These distinctions leave the full original-model question open.

The most useful priorities for future conaled development and our Agda
reconstruction are:

1. **Expose the explicit-data core.** Separate quotient operations, chart
   maps and compatible-section constructions from selector wrappers. Export
   unique-output and independence proofs so another metatheory can construct
   the output without adopting arbitrary choice.

2. **Complete the ordinary arrow comparison.** Prove the locally constant
   inverse above, then the actual chart-arrow and descent comparisons. This
   gives a substantial external theorem with a concrete geometric meaning.

3. **Specify the constructive site.** State real-number apartness, principal
   cover, analytic gluing and compactness conventions before claiming the
   exact classical specialization. Keep unresolved existence lemmas visible.

4. **Join higher structure to smooth geometry.** Construct one model containing
   the required identities, bounded universes, type operations and smooth
   objects. The existing separate higher witness and local presentations are
   starting points, not a substitute for this joint construction.

5. **Prove the exact language transfer.** Fix the admitted syntax and build
   interpretation, substitution and the actual geometric comparisons in
   Agda. Use a pinned per-theorem axiom audit to guide reuse of Lean proofs;
   use the other libraries’ soundness and universe constructions as concrete
   standards for what still needs to be built.

These priorities preserve the external applicability goal while making each
remaining mathematical and logical obligation independently reviewable.

# Alternatives after the checkpoint-080 consumer report

Assessment date: 2026-11-08. Conaled baseline:
`700786fa2f691d6db196f388d69c2f12bc5d1afb`. This independent assessment for
[#362](https://github.com/VladimirMarko/conaled/issues/362) reads the incoming
reports, their archived semantic research and source notes, and the prior
[synthesis](synthesis.md). It does not read the other new assessments. Evidence
is source inspection and published mathematics. No compared library was built,
no axiom closure was extracted, and no proposed experiment below was run.

The consumer changes the priority: compare the construction of an admissible
dependent model and interpretation of a fixed source fragment before extending
the arithmetic certificate interface. Retain conaled's smooth geometry and
descent as regression requirements. Keep a cubical/sheaf foundation and a
natural-model interpretation architecture eligible to replace parts of the
current core. Neither the consumer nor the inspected alternatives establishes
an already available replacement for the whole library.

The supplied [semantic-foundations report](<../../history/orbifold/agda-checkpoints/checkpoint-080/Orbifold semantic foundations research checkpoint.md>)
and [library comparison](<../../history/orbifold/agda-checkpoints/checkpoint-080/Conaled and semantic libraries for an Agda formalization.md>)
target an Agda-only external proof. The archive's `formalization/research/semantics/`
contains `LIBRARY-COMPARISON-080.md`, `LIBRARY-SOURCE-NOTES-080.txt`,
`DEPENDENCY-BOUNDARIES-077.md` and `README.md`, inspected here after extraction.
Paths into that archive below refer to its `formalization/` directory. Its
reported accepted proofs, external arguments, and work proposed for checkpoint
081 remain distinct. This note neither adopts the archive's instructions nor
treats that consumer's implementation language as a host decision for conaled.

## What the primary sources justify

**SynthLean supplies a different interpretation architecture.** The CPP 2026
paper, DOI `10.1145/3779031.3779087`, defines natural-model semantics and proves
soundness given a well-formed base interpretation (Theorem 3.1), with semantic
substitution in Lemma 3.2. Chosen comprehension pullbacks are explicit data.
Section 2.2 postulates type-former injectivity; semantic soundness is independent
of that axiom, but certificates produced by the paper's typechecker use it.
Thus a soundness theorem and a frontend certificate have different dependency
questions. The model must still supply the admitted constructors and universe
structure. This is a candidate architecture for interpreting a fixed derivation,
not a theorem interpreting arbitrary Agda programs.
[Primary paper](https://voidma.in/assets/papers/2026nawrocki_certifying_proof_assistant_synthetic_mathematics_lean.pdf).

The [HoTTLean README at `31133dd5b25226ea897f8aa5e2e43b61392459eb`](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/README.md),
resolved and read through GitHub's API/raw endpoint, reports a sorry-free
groupoid model for Π, Σ and Id, and h-set univalence in its HoTT0 example.
It explicitly excludes current support for higher inductive types and describes
the model construction as incomplete. I did not audit whether the paper's
injectivity assumption survives in that revision's certifier. It cannot be
accepted into conaled's proof boundary on the strength of the README alone.

**Initiality is stronger than the transfer needed here.** Brunerie–de Boer's
[`v2.0`, resolved to `eaa6812153c94c0e009e1bce16bf66d255588bcf`](https://github.com/guillaumebrunerie/initiality/blob/eaa6812153c94c0e009e1bce16bf66d255588bcf/README.md)
declares annotated syntax, structured contextual categories, an infinite
universe hierarchy, and separate substitution, totality, existence and
uniqueness proofs. The metatheory includes strict `Prop`, dependent function
extensionality, propositional extensionality and postulated quotients with a
definitional computation rule implemented by rewriting. The
[2020 author presentation](https://guillaumebrunerie.github.io/pdf/initialityHoTTEST.pdf)
agrees with that boundary. This source is a concrete reference for replacing
per-fragment interpretation proofs by a reusable language theorem. A supplied
structured model remains necessary. For the consumer, sound interpretation of
the chosen proof is sufficient; uniqueness of every interpretation is a
possible later strengthening. Unchanged import into its safe ordinary fragment
would not preserve the declared metatheory.

**BiSikkel separates three useful layers without solving this universe problem.**
The POPL 2025 paper, DOI `10.1145/3704844`, constructs dependent presheaf
semantics, modal simple program syntax, and a dependent logical framework with
sound proof checking. Section 6.1 proposes interpretation into arbitrary models
via an additional algebraic syntax layer as future work. Section 6.3 identifies
its mixture of isomorphism equality for presheaves and pointwise term equality
as an obstacle to semantic universes. Function extensionality is an explicit
metatheoretic assumption; the guarded-stream extraction example adds another
equality principle. These boundaries prevent crediting it with full dependent
MTT source interpretation or a ready smooth universe. Its modular semantics,
syntax and proof organization is relevant even if its equality representation
is rejected. [Primary paper](https://anuyts.github.io/files/2025/bisikkel-popl.pdf).
The consumer identifies source release DOI `10.5281/zenodo.14888955`; that
endpoint returned HTTP 429 here, so this assessment relies on the published
paper rather than claiming independent inspection of that release.

**Xu supplies actual sheaf constructions.** The published
[types and terms](https://cj-xu.github.io/ContinuityType/CwF.Sheaf.TypesAndTerms.html)
define dependent families and reindexing. The
[comprehension source](https://cj-xu.github.io/ContinuityType/CwF.Sheaf.ContextComprehension.html)
constructs a total Sigma carrier and its gluing from the component data. The
site concerns uniform continuity, not smooth finite-Weil probes. These generated
2014 source pages were inspected on 2026-11-08; no immutable repository revision
was recovered. They substantiate the particular constructions, not claims about
all type formers, universes, or a modern successful build. They provide an
alternative proof organization for an ordinary layer already present in conaled.

**Cubical classifiers require specific ambient structure.** Orton–Pitts,
LMCS 14(4:23), 2018, works in a topos with a universe, a connected interval with
distinct endpoints and connections, and cofibrant propositions satisfying
specified closure and strictness axioms. Different constructions use different
subsets of these assumptions. The Agda artifact uses impredicative propositions,
postulates for those axioms, and rewriting. Section 7 does not supply an internal
univalent-universe construction in that ordinary internal language.
[Primary paper, Figure 1 and sections 2–8](https://lmcs.episciences.org/5028/pdf).

Licata–Orton–Pitts–Spitters, FSCD 2018 article 22, Theorem 5.2, constructs a
classifying fibration from axioms (1)–(4) and a tiny interval in crisp type
theory. Codes and decoding satisfy the specified classification laws for crisp
families; this is more than naming an external universe level. Section 6 leaves
completion of the Agda-flat fibrancy/univalence development open. Remark 4.2
warns that Agda-flat implements more than the presented crisp calculus. The
interval's tinyness must be instantiated; it is not Myers's separate tinyness
hypothesis for an infinitesimal neighborhood.
[Primary paper, Theorem 5.2, Remark 4.2 and section 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol108-fscd2018/LIPIcs.FSCD.2018.22/LIPIcs.FSCD.2018.22.pdf).

**Constructive higher sheaves offer model derivation machinery.**
Coquand–Ruch–Sattler's [arXiv:1912.10407v4](https://arxiv.org/pdf/1912.10407v4)
develops descent-data operations and lex localization for constructive sheaf
models. This supplies a mathematical construction to investigate, not a
machine-checked smooth instance in this repository.

Coquand–Höfer–Sattler, LICS 2026 article 31, uses constructive set theory or
extensional type theory with a universe hierarchy. Its assumptions include a
cubical setup with connections and locally representable interval, a small
internal category, and, for the subsequent lifting, a suitable lex operation
lifting to fibrant types, fibrancy of the hom family, and descent-data structure.
The cobar construction refines naive presheaves; later results lift properties
from a base model. These are conditional model-construction theorems. The
introduction explicitly conjectures identification with the intended higher
categories of sheaves. Its applications validate particular synthetic theories,
not the whole Myers signature. No reusable implementation or exact smooth
instance was established by this inspection.
[Primary paper, sections 2–5 and Assumptions 1–5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol380-lics2026/LIPIcs.LICS.2026.31/LIPIcs.LICS.2026.31.pdf).

Publication versions and arXiv suffixes above identify the mathematical sources;
author-hosted PDF and generated-page links alone do not pin immutable bytes.
Repository SHAs identify the two independently retrieved README revisions.
This is sufficient for the bounded architectural comparison, but dependency
selection would require pinned source closures and actual validation.

## Changes to the foundation question

The consumer needs reusable *construction of admissible models*, followed by
interpretation of an identified proof and comparison with external geometry.
Repeated wrappers around model records cannot discharge those tasks. Three
changes remain live possibilities:

- Use a natural model or contextual-category core to derive source interpretation
  once for an admitted language. Charge each setting for its model operations,
  constants and laws, rather than making every client reconstruct soundness.
- Use weak semantic structure plus a coherence theorem, or internal cubical
  model constructions plus descent, to derive stability and closure. The
  alternative may change the model representation and equality discipline.
  It need not first inhabit all incumbent strict fields by hand.
- Separate a constructive explicit-data geometry core from classical existence
  wrappers, with different realizations proving their own assumptions. This
  could alter site presentations and public interfaces. It needs comparison
  theorems, not removal of occurrences of `Classical.choose`.

These are design inferences. The papers do not prove that conaled will gain
agent productivity from any of them. Local universes for coherence and an
object-language universe classifying families solve different problems.
Conaled's [LocalUniverses source](../../../SquareKit/LocalUniverses.lean)
explicitly implements parameterized split-family presentations and excludes
both the general coherence theorem and higher identity. Neither this module
nor a host `Type u` annotation is evidence of the needed classifier.

The strongest retention evidence is the consumer's intended reuse of actual
smooth algebra, first-order KL, manifold reconstruction and quotient descent,
combined with existing dependent sheaf construction. Direct inspection of
[SplitSheaf](../../../SquareKit/SplitSheaf.lean) and
[SplitFunctionSheaf](../../../SquareKit/SplitFunctionSheaf.lean) finds
constructed substitution and `piType`, including sheafhood proofs.
[SheafActionQuotient](../../../SquareKit/SheafActionQuotient.lean)
retains arrows and supplies `chartArrowEquiv`. This evidence favors retaining
mathematics and usable specializations through a redesign; it does not require
retaining the current authoring core.

The strongest change evidence is that the external proof needs all of these
operations in one admissible setting, with universes and exact substitution.
The incoming archive's `src/Orbifolds/Intensional/DerivedAtlasOrbifold.agda`
exposes a bounded theorem with `BoundedTruncation`, weak `FunExt`, actual
pushout tests, atlas comparisons and vertex lifts. Its locality and lifting
conclusions are derived. The supplied dependency review distinguishes this
ordinary fragment from point-set proofs with classical inputs and from the
larger Cubical development. This gives a concrete consumer beyond selected
arithmetic packets while keeping full original-foundation validation separate.

The source reports also impose a falsification condition: the reported RealFlat
obstruction concerns a specified canonical constant-map/counit interpretation,
with crispness, size and transfer hypotheses. It does not prove inconsistency
of every possible foundation. A model comparison must expose incompatible
assumptions rather than change the modality silently to obtain a passing model.
Likewise, original crisp excluded middle and the reduced theorem's constructive
signature are distinct requirements. Keywords, host language and imported file
names cannot replace per-declaration logical dependency evidence.

## A matched comparison independent of either architecture

The following is a proposed experiment, not completed formalization. Freeze a
bounded subargument from `DerivedAtlasOrbifold`: the actual mapping comparison
for a pointed pushout test, its restriction/gap computation, and cancellation
yielding locality. Preserve its quantified targets, identity data, levels and
substitution behavior. Freeze the exact admitted source rules before either
implementation starts. Any reduction of that signature must be explicit and
the same for both routes.

Compare the incumbent source/semantic interfaces against a natural-model or
contextual-category interpretation, allowing a weak presentation plus coherence
where its hypotheses hold. Require the same proof to interpret after two
composable context substitutions. Count model construction, required primitives,
coherence proofs and semantic comparisons separately from authoring the source
argument. A claimed universe must provide codes, decoding and the closure the
argument uses. A record whose field is the missing desired conclusion fails
the construction requirement on either route.

Use an independently specified geometric control: ordinary open-domain arrows
for the existing quarter-turn action must correspond to locally constant group
labels satisfying the action equation. Prove the actual inverse maps,
composition and restriction compatibility, then test an open-cover refinement.
[SmoothConstantOrdinary](../../../SquareKit/SmoothConstantOrdinary.lean)
currently supplies `ordinaryLocallyConstant`; the inspected file does not
provide the inverse required for this comparison. Check the arrow convention
`m = a.onMap g n`, including inversion relative to forward-action labels.
This control should reuse C4 geometry rather than recreate a weaker C2 example.
The full source-to-geometric-model theorem remains a further milestone.

Negative controls must reject replacing arrows by orbit equality, replacing
the selected comparison map by an unrelated equivalence, or erasing distinct
ineffective stabilizer arrows because their actions agree. A separately
constructed higher witness cannot satisfy the smooth-model requirement until
the operations coexist and their compatibility is proved. Finite stabilizers
alone cannot discharge properness of an actual Lie groupoid anchor.

The incumbent loses this comparison if recurring substitution or model-admission
work is derived once by the competitor under the same assumptions, with the
same observed geometry, and the incumbent must rebuild it per client. The
competitor loses if it assumes the required model, strengthens the metatheory
without accounting for it, or cannot recover the existing concrete guarantees.
Neither victory follows from line counts. Record setup, maintenance after a
model/constructor change, failed attempts, assistance, checking cost and agent
resources. Preserve a direct/native route as the control.

## Research ordering for #358–#361

The prior comparison was reasonably broad but its recent arithmetic evidence
underweights model construction and exact source transfer. The incoming work
makes those costs observable. Extension interactions and relational hiding
remain useful independent tests; they should no longer precede every geometry
test by default. The existing joint-extension work also prevents treating a
tiny incompatible-extension example as a newly discovered capability gap.

| Work | Recommended research disposition |
| --- | --- |
| #359, selected higher shared meaning | First semantic priority alongside the ordinary arrow control. Fix the required witnesses and joint-model boundary; compare foundation choices before expanding the current representation. |
| #358, authoring and scaling | Design the matched source/model experiment now, but run the productivity comparison only after its semantic contract is fixed. Count model and interpretation setup, not only additional syntax. |
| #361, selected partial solutions | Next, compare selected witnesses, unique gluing and mere existence against the consumer's descent/atlas requirements. Keep relational hiding as a separate observation contract. |
| #360, resource modes | Retain as an independent operational research question. This report supplies no resource semantics or evidence that modal geometry validates resource modes; it should not dictate the semantic foundation first. |

This ordering is a recommendation for revising the pending research, not an
implementation authorization or a dependency theorem between all four issues.
The natural-model and cubical/sheaf alternatives deserve bounded investigation
before further interface commitment. Adoption requires recovery of the current
specializations under stated assumptions and the repository's existing audit
policy; no ADR or host migration is proposed here.

# Internal languages and proved models in Lean

Research for [issue #35](https://github.com/VladimirMarko/conaled/issues/35),
inspected on 2026-10-18. This note distinguishes a proved mathematical model,
an interpretation theorem, and a proof interface for users. None implies the
other two. No external package was built or added as a dependency for this
survey; the compatibility judgments below are source inspections, not porting
results. Commit dates record observed maintenance activity, not a maintenance
guarantee.

## Objective and ownership

The objective is to let an author prove a theorem in an internal language,
interpret it in a constructed mathematical model, and use a proved comparison
to obtain a result about ordinary Lean/Mathlib objects or an existing
realization. For example, an internal synthetic differentiation theorem should
eventually yield an external theorem about the derivative of a smooth map.
The proof interface, model soundness and comparison theorem are all required;
pleasant notation alone does not connect that reasoning to the library.

This is shared infrastructure for the repository's Felix-style development.
A caller should be able to use an internal language wherever its required
structure has been supplied. Different fragments require different structures:
a cartesian model need not support quantifiers, dependent types or cohesion.
Existing category maps and squares connect interpretations and realizations;
the proposed logical interfaces add the meaning of predicates and proof rules.
Internal-language use must be optional. Ordinary Lean definitions, proofs,
notation and direct library calls must remain usable without additional model
parameters, interpretation wrappers, conversions or proof obligations. Keep
internal-language syntax and imports opt-in; importing the ordinary library
must not change the meaning of standard Lean notation or require a custom
proof mode. Implementation complexity belongs in reusable adapters, not at
ordinary call sites.

Acceptance must include representative unchanged ordinary-Lean clients beside
the internal-language examples, including a file using both styles. Check
that they need no additional setup or obligations, and that the ordinary path
acquires no unnecessary runtime representation or elaboration overhead. The
new capability must not make standard Lean use of the library harder.

[#35](https://github.com/VladimirMarko/conaled/issues/35) owns this research
and design assessment. The long-term implementation is now tracked by
[#36](https://github.com/VladimirMarko/conaled/issues/36): shared internal
reasoning, a proved differential cohesive model, and Mathlib and classical
presentation comparisons. The smaller experiment below tests the shared
proof-to-model-to-consumer path before attempting the geometric model.

The [graph experiment](#first-experiment-internal-graphs-external-squares)
is **the same work as Stage A** in the [work breakdown](#stages-and-follow-up-tasks).
Its modest theorem is chosen to expose substitution, existential reasoning,
model preservation and integration with existing squares. It establishes none
of the infinitesimal or cohesive assumptions. The later work packages name
those additional obligations; they are not a claim that all six stages form a
settled implementation plan.

The source survey supports selective reuse: Foundation supplies compatible
intuitionistic proof/semantics machinery, SynthLean supplies a richer dependent
language design to investigate, and the SDG development supplies calculus
proofs under assumptions whose model still has to be constructed.

## Capability and compatibility evidence

| Candidate | Source revision, toolchain, license and activity | Language/model and proved interface | Dependency/reuse boundary |
|---|---|---|---|
| SynthLean / HoTTLean | `31133dd5b25226ea897f8aa5e2e43b61392459eb`, committed 2026-02-06; Lean 4.25.0-rc2; Apache-2.0; upstream describes work in progress. | Explicit dependent syntax, Π/Σ/Id, interpretations and groupoid semantics, with a Lean-like frontend. Current checker has extra injectivity axioms; the illustrative external Unit bridge is incomplete. | Adapt selected semantic components and frontend design after a declaration-level audit and port; no wholesale adoption. |
| FormalizedFormalLogic/Foundation | `c3eb37ae896dc8f1d239ba1511e74d9f25e9d158`, committed 2026-10-13; Lean 4.35.0 and exactly the local Mathlib pin; Apache-2.0. | Propositional Heyting algebra semantics with soundness/completeness; relational first-order intuitionistic Kripke semantics with soundness. | Adopt selected modules if dependency audit passes, or adapt the minimal valuation/soundness interface. |
| `lean-catLogic/formalization` | `bf4eda918a90ed04b8867bfcc587cc0dda1c4347`, committed 2023-03-29; Lean 3.48.0; no license located. | Positive propositional natural deduction and derivation/syntactic-category bridges, including a cartesian closed category. | Architectural reference; no direct import or assumed permission to copy. |
| Pinned Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; Lean/Mathlib 4.35.0, already adopted locally; Apache-2.0. | Proved sheaf/presheaf classifier and cartesian closed constructions under explicit hypotheses. | Adopt model components; implement syntax interpretation and preservation interfaces where absent from this inspected slice. |

The detailed entries supply pinned sources, proof assumptions and examples for
these rows. Compatibility of a declared toolchain does not prove compatibility
of all dependencies or admission policies.

### SynthLean / HoTTLean

**Adapt, with a dedicated compatibility and trust audit; do not adopt wholesale yet.** It combines an MLTT DSL using Lean syntax/tactics, deep syntax, interpretation theorems and groupoid semantics. The checker has the additional assumptions detailed below. Current default-branch checkout is `31133dd5b25226ea897f8aa5e2e43b61392459eb` (commit dated 2026-02-06); GitHub API reports last push 2026-06-12, which is not evidence master has newer content. Apache-2.0. Lean `v4.25.0-rc2`, Mathlib `32bd6c7c8ca4a4be1c71bc04df0c9cf929d04818`, Poly `aedee22f07d681d845bcbe4a1fb9aa10f95c9977`: an older standard Lean toolchain, not a custom kernel, and not currently the project's dependency set. [README](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/README.md), [manifest](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/lake-manifest.json), [toolchain](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/lean-toolchain).

The source has Π, Σ, intensional Id and finite universe levels plus named constants; explicit typing and definitional equality judgments. `ofType_ofTerm_sound` proves interpretation of well-formed contexts/types/terms and equalities. `interpCtx`, `interpTy`, `interpTm`, `interpTy_eq`, `interpTm_eq`, `interpTm_tp` turn these into usable objects, maps and equalities. An interpretation of constants must satisfy `Interpretation.Wf`; this separates naming an internal axiom from proving it valid in a model. Current main entrypoint imports `Model.Unstructured.Interpretation`; the older natural-model interpretation remains a separate Lake target. [natural interpretation](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Model/Natural/Interpretation.lean), [current interpretation](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Model/Unstructured/Interpretation.lean), [entrypoint](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean.lean).

**Material trust qualifications:** `Syntax/Injectivity.lean` declares three conjectured external Lean axioms `EqTp.inv_pi`, `EqTp.inv_sigma`, `EqTp.inv_Id`. These are imported by `Typechecker/Value.lean` and used in `Typechecker/Evaluate.lean` and `Equate.lean`. Thus the current checker path cannot be casually described as satisfying conaled's axiom whitelist. `ForPoly.lean` also has three `sorry`s (lines 595,605,612), imported by the separate Natural target. These do not establish that every semantic soundness theorem or groupoid theorem depends on those holes; an actual dependency audit is required. The README separately describes the groupoid Π/Σ/Id construction as sorry-free. [injectivity axioms](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Syntax/Injectivity.lean), [checker usage](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Typechecker/Evaluate.lean), [ForPoly](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/ForPoly.lean).

User-facing example `test/unitt.lean` declares Unit, its inhabitant, uniqueness, and function extensionality, then proves `uniq_fn` internally with `apply funext; intro; exact ...`. This is convenient internal proof syntax. But the external example interprets only the Unit *type* constant, supplies a hand-written semantic map plus well-formedness proof, and contains `instance : uHomSeq.IdSeq := sorry`; its old imports point at removed/relocated model modules. It is evidence of interface design, **not** an end-to-end verified interpretation of `uniq_fn` at this revision. Exporting the theorem would require interpretations of all its constants, a complete model instance and proof dependencies checked. `test/hott0.lean` declares set-univalence internally; that declaration alone is not a constructed univalent model. No higher inductive types are supported according to README. [unit example](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/test/unitt.lean), [HoTT0 example](https://github.com/sinhp/HoTTLean/blob/31133dd5b25226ea897f8aa5e2e43b61392459eb/test/hott0.lean).

[CPP 2026 paper](https://voidma.in/assets/papers/2026nawrocki_certifying_proof_assistant_synthetic_mathematics_lean.pdf) explains the certifying architecture; [archived paper artifact](https://zenodo.org/records/17798253) is a separate snapshot (`cpp2026`), not interchangeable with the inspected master revision. Prefer source findings where README/paper and master diverge. Reuse the separation of explicit derivations, semantic interpretation and user elaboration; do not require a full natural model just to support a regular-logic fragment.

### FormalizedFormalLogic/Foundation

**Adopt selectively or adapt small interfaces.** Revision `c3eb37ae896dc8f1d239ba1511e74d9f25e9d158`, commit 2026-10-13; API last push 2026-10-17. Apache-2.0. Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, exactly matching conaled. Additional Forgive/doc-gen dependencies mean compatibility is not itself a completed integration test. [manifest](https://github.com/FormalizedFormalLogic/Foundation/blob/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158/lake-manifest.json), [toolchain](https://github.com/FormalizedFormalLogic/Foundation/blob/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158/lean-toolchain).

`FFL.Propositional.Formula.hVal` interprets atom/false/and/or/implication in any Mathlib Heyting algebra. `Heyting.Model.sound`, `lindenbaum_complete_iff`, `complete` and Sound/Complete instances prove the Hilbert proof-system semantics (completeness assumes `Entailment.Int H`; Lindenbaum model additionally assumes consistency). `Heyting.Model` bundles an algebra, valuation, Heyting structure and nontriviality; low-level `Formula.hVal` avoids the latter bundled restriction. Caller effort: choose a Heyting algebra and atomic valuation, provide a Hilbert derivation and validity of theory axioms, then invoke soundness. This is existing syntax+semantics+proof system, not merely a category/model construction; it does not provide quantified categorical internal logic. An immediate example shape is soundness of `p ∧ q → p`, interpreted as `(v p ⊓ v q) ⇨ v p = ⊤`. [complete inspected file](https://github.com/FormalizedFormalLogic/Foundation/blob/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158/Foundation/Propositional/Heyting/Semantics.lean).

For first-order intuitionistic logic, `Kripke.Model` requires a **relational** language, preorder of worlds, nonempty domains as subsets of one ambient carrier, domain persistence and predicate persistence (their accessibility convention is `v ≤ w`). `Forces` interprets implication and universal quantification across accessible worlds, existential quantification in the current domain. `Forces.sound` proves LJ derivations sound, and `Kripke.Mod.sound_empty` exports a closed proof to validity. Callers provide all those model fields and explicit syntactic derivations; there is no found equivalence here to arbitrary categorical sheaf semantics. Equality is not built into the `Forces` cases: predicates are `.rel R`; don't promise the first-order module directly solves internal equality of arbitrary objects. The inspected files contain no `sorry` or new `axiom` declarations, but this is not a transitive proof audit. [model](https://github.com/FormalizedFormalLogic/Foundation/blob/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158/Foundation/FirstOrder/Kripke/Basic.lean), [forcing and soundness](https://github.com/FormalizedFormalLogic/Foundation/blob/c3eb37ae896dc8f1d239ba1511e74d9f25e9d158/Foundation/FirstOrder/Kripke/Intuitionistic.lean).

Classical Lean metatheory is safe here because internal implication is Heyting implication or forcing at all extensions, not external implication at one world. External excluded middle about `w ⊩ φ` does not prove `w ⊩ φ ∨ ¬φ`. Completeness itself uses `classical`, without changing the syntactic rules or semantic validity relation.

### lean-catLogic/formalization (legacy)

**Reference/adapt ideas only; no direct dependency.** `bf4eda918a90ed04b8867bfcc587cc0dda1c4347`, last commit/push 2023-03-29. Lean 3.48.0, old Mathlib `4698e35ca56a0d4fa53aa5639c3364e0a77f4eba`. No LICENSE in checkout and GitHub license metadata null: do not assume permission to copy. Positive propositional calculus has top, atoms, conjunction, implication and inductive natural deduction. Abstract deduction structures yield a thin syntactic category, cartesian closed structures, and modal/monadic variants. `syn_hom`, `syn_hom_inv`, `derives_of_hom` connect derivations and syntactic-category arrows. `LiftT` lifts derivation rules to quotient/category constructions; `Lower` reverses the bridge. This is valuable caller-interface precedent, but not a completed current Lean sheaf model/proof frontend. Inspected source search found no `sorry`/new axiom declarations; it was not built. [toolchain](https://github.com/lean-catLogic/formalization/blob/bf4eda918a90ed04b8867bfcc587cc0dda1c4347/leanpkg.toml), [syntax](https://github.com/lean-catLogic/formalization/blob/bf4eda918a90ed04b8867bfcc587cc0dda1c4347/src/deduction/PPC_natDeduct.lean), [bridge and tactics](https://github.com/lean-catLogic/formalization/blob/bf4eda918a90ed04b8867bfcc587cc0dda1c4347/src/semantics/syntacticCat.lean), [lifted CCC](https://github.com/lean-catLogic/formalization/blob/bf4eda918a90ed04b8867bfcc587cc0dda1c4347/src/semantics/syntacticCat_cartesian.lean).

### Pinned Mathlib model constructions

At conaled's pin, `CategoryTheory/Topos/Sheaf.lean` constructs presheaf and sheaf subobject classifiers, including characteristic maps and pullback/uniqueness proofs (`Presheaf.χ`, `Presheaf.isPullback_χ_truth`, `Sheaf.χ`, `Sheaf.isPullback_χ_truth`, classifier instances for essentially small sites). `Sites/CartesianClosed.lean` builds cartesian closed sheaves under `HasSheafify` and closed presheaf hypotheses. These are proved categorical model components, not a user proof mode or a full internal-language soundness theorem. Callers still handle sites, universes, sheaf conditions and semantic bridges. Adopt existing structures; implement missing interpretation/preservation interfaces instead of recreating classifiers. [classifier source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Topos/Sheaf.lean), [closed sheaves](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/CartesianClosed.lean).


## Synthetic differential geometry

The lead in the [imported orbifold discussion](../history/orbifold/orbifold-simulator-chat.md)
resolves to Brasca and Clemente's [SDG repository][sdg] and
[*Synthetic Differential Geometry in Lean*, version 2][sdg-paper]. It contains
proved synthetic calculus conditional on Kock–Lawvere assumptions. It does
not supply a constructed smooth topos or an interpretation of those assumptions
in one. The paper explicitly identifies formalizing well-adapted models as
future work. This is a useful calculus reference, but does not itself connect
synthetic differentiation to Mathlib's analytic differentiation.

| Candidate | Revision and compatibility | Actual capability | Reuse decision |
|---|---|---|---|
| Brasca–Clemente SDG | [`e4cd622492aba9be421ec0abcf152f58a0ee98df`][sdg], committed 2026-10-15; Apache-2.0; custom `riccardobrasca/lean4:v4.35.0-less-choice`; forked Mathlib `c2934be473385c5b1e3a639cad5c00547d65e354`, with dependencies fixed in its manifest. | A shallow scalar calculus with first/higher-order infinitesimals, derivative rules and multivariable Taylor; KL is a typeclass hypothesis and unique choice is a declared axiom. No model existence or external analytic comparison theorem was located in the inspected source. | Adapt algebraic proofs and the categorical formulation after internalization. Do not adopt the fork or import its KL classes as realizable ordinary Lean types. Upstream choice-free lemmas when independently useful. |
| Ground Zero | [`2cbca29485c2e6f420c120365e00fe3b70db3acf`][ground], committed 2026-02-17; Apache-2.0; standard Lean `4.28.0`, plus a custom command-level HoTT checker. | HoTT notation, synthetic proofs and HIT interfaces; guarded extra axioms, not a proved groupoid/sheaf interpretation. | Study notation and proof ergonomics. Do not import its axioms or use its checker as a substitute for a model soundness proof. |
| `jthulhu/2ltt` | [`6077427bdc4d7e0c521c18f811a54d2dcf85c0a0`][2ltt], committed 2026-06-04; AGPL-3.0; `leanprover/lean4:v4.10.0-rc1`; README explicitly says unmaintained. | Object-language types and notation, a HoTT development including function extensionality; univalence is axiomatized and parts of the Reedy development contain `sorry`. | Design evidence for separating object and metatheory. No direct dependency; permission/license review and a proved semantic reconstruction would precede code reuse. |
| Lean 2 HoTT library | [`8072fdf9a0b31abb9d43ab894d7a858639e20ed7`][lean2], last commit 2018-10-01; Apache-2.0; Lean 0.2 with a separate HoTT kernel mode. | Synthetic homotopy theory, higher inductives and category theory in a foundation without Lean 4's proof-irrelevant `Prop`; univalence is initialized as an axiom. | Mathematical reference and possible theorem-port source. No binary/source compatibility with this repository's Lean 4/Mathlib model boundary. |

The SDG [toolchain][sdg-toolchain], [manifest][sdg-manifest],
[license][sdg-license] and [build workflow][sdg-ci] substantiate its dependency
and activity entries. The workflow builds the forked library and checks source
coverage. This inspection did not reproduce that build or its transitive axiom
reports. Its linter warns about `Classical.choice` and `sorryAx`; that policy is
different from this repository's exhaustive build-failing axiom audit.

### What SDG users can prove

In [Basic/Defs.lean][sdg-defs], `D R` is the subtype of a commutative ring whose
elements square to zero. `IsKockLawvere_one R` extends `Nontrivial R` and
requires every function `D R → R` to have a unique affine coefficient.
`IsKockLawvere R` requires the corresponding unique finite polynomial expansion
at every order. These are supplied proof fields, not constructed witnesses of
consistent scalar models. The derivative selects those coefficients using
[`axiom_unique_choice`][sdg-choice].

The user-facing [derivative API][sdg-deriv] provides `taylor_one`, `deriv_mul`,
`chain_rule`, `deriv_X_pow`, and a bundled `Derivation`. For example,
`chain_rule f g x` states that the derivative of a composite is the product
of the outer derivative at `g x` and the inner derivative at `x`. Callers supply
a commutative ring and its KL instance; they do not manipulate sheaf arrows.
[`taylor_multi`][sdg-taylor] adds a rational algebra structure and the full KL
class, and relates a function on a finite product of infinitesimal neighborhoods
to its mixed partial derivatives. This is convenient shallow mathematics, but
its convenience depends on changing which ambient principles may be used.

The repository proves [`false_of_isKockLawvere_one`][sdg-em]. Its proof uses
classical case analysis to construct a function on `D R`, applies
KL, and derives `1 = 0`. Consequently, transplanting the KL class into ordinary
classical Lean and assuming an instance cannot establish useful model
existence. Nor does forbidding the `classical` keyword suffice: dependencies
can use choice transitively. This is why the upstream project changes library
proofs and checks dependency axioms.

[`Basic/Alpha.lean`][sdg-alpha] offers a better adaptation boundary: it proves
that unique affine expansion is equivalent to bijectivity of
`alpha : R × R → (D R → R)`. In an internal model the analogous statement is
that the categorical map `R × R ⟶ R ^ D` is an isomorphism, with the exponential
and ring operations interpreted in that category. A finite-limit/cartesian
closed interpretation can express this without claiming that all external
set-functions on global elements are smooth. Building the ring object,
infinitesimal subobject and this isomorphism remains a model obligation.
The theorem in SDG is an ordinary function-space statement; the categorical
version proposed here is work to implement, not a theorem already supplied by
that file.

### Higher types and cohesive structure

Ground Zero supplies a useful warning against conflating a familiar proof mode
with a proved model. Its [identity type][ground-id] is explicitly `Type`-valued
and rebinds equality notation. Its [checker][ground-checker] excludes certain
large eliminators and classical declarations, and introduces a `GroundZero`
parameter for guarded axioms. The [univalence development][ground-ua] proves
results from `uaweak` and `uaweakβ` axioms. Its [circle development][ground-circle]
illustrates ordinary-looking synthetic path proofs. The [truncation interface][ground-trunc]
also has primitive axioms. No semantic construction discharging these axioms
was located. The standard Lean executable alone does not make these assumptions
acceptable to this repository's audit.

The [2ltt object-language implementation][2ltt-obj] wraps external types in
private structures and defines object Π-types, application and notation.
Its [HoTT development][2ltt-hott] has external/internal Π and Σ comparisons,
which are instructive interface examples, and an explicit `univalence` axiom.
The inspected [Reedy presheaf file][2ltt-reedy] contains admissions. Privacy of
constructors is an interface discipline; it is not a theorem that a nontrivial
homotopical model validates every added principle.

The historical [Lean 2 HoTT specification][lean2-hott] describes a different
kernel configuration, with primitive truncation/quotients and univalence. Its
[coverage table][lean2-book] identifies substantial completed synthetic
mathematics and unfinished areas. That work is relevant evidence that Lean has
hosted synthetic mathematics, but does not discharge a Lean 4 interpretation
into ordinary mathematical structures.

For the orbifold workstream, a groupoid model would preserve nontrivial
isotropy as arrows and distinguish those arrows from external equality
proofs. A set-valued sheaf model supplies intuitionistic logic and local
variation, but does not by itself supply all higher identities. A groupoid
model by itself supplies neither smooth infinitesimals nor cohesive modalities.
The [Myers assessment](myers-orbifold-assessment.md) identifies the additional
obligations: coherent higher identities/universes, the specified cohesive and
differential modalities and their laws, microlinearity, and comparison with
classical presentations. Any later combination must prove compatibility
between those structures, not merely put each into a record.

Searches for Lean internal languages, Kripke–Joyal semantics, cohesive models,
well-adapted SDG models and HoTT implementations found the candidates recorded
here and in the standard-model survey. We did not locate a checked Lean
construction connecting a differential cohesive higher model to Mathlib
manifolds, or a completed KL smooth-topos model in the inspected SDG repository.
This is a bounded negative result about inspected implementations and primary
source searches, not a proof that no other Lean project has such a result.
Non-Lean constructions and proposals remain mathematical references; they are
not counted as reusable checked implementations.

## Internal reasoning inside classical Lean

An explicit interpretation separates internal propositions from Lean `Prop`.
For instance, at a Kripke world `w`, implication must quantify over accessible
worlds and universal quantification must respect the model's future domains.
At a sheaf stage, existential assertions may require witnesses only after a
cover. An external proof of `P ∨ ¬P` about a satisfaction predicate therefore
does not give an internal derivation of excluded middle. Only the represented
inference rules and proved soundness theorem license that passage.

Internal equality likewise needs its stated interpretation: equality of terms
in a set model, an equalizer/diagonal subobject in an extensional categorical
model, or identity data in a higher model. Lean's proof-irrelevant equality
proofs cannot serve as distinct isotropy arrows. External quantification over
all Lean functions and internal quantification over an exponential object
must not be interchanged without a comparison theorem. These are design
requirements for the proposed interfaces, not new foundational axioms.

In an SDG model the scalar `R` is a ring object. It is not Mathlib's field `ℝ`:
a field has no nonzero square-zero elements. Even if a comparison identifies
global scalar sections with ordinary real numbers, that does not identify
generalized elements at every stage or internal maps with arbitrary external
functions. The `alpha` isomorphism above must hold internally. This permits
classical mathematics to construct and investigate a model with intuitionistic
internal logic without validating the contradictory external KL assumption.

## Repository integration and Felix comparison

This assessment inspected repository revision
`56361015f1fe7bc19bf91e4bce31cf5fb88f3d27`. The following are existing
implementations, not proposed capabilities.

| Existing module | Reusable capability | Missing internal-language capability |
|---|---|---|
| [`Dependent.lean`](../../Dependent.lean) | `Ty Γ := Γ → Type`, sections, substitution, context comprehension, Π/Σ β/η and substitution laws; `SubCert`, `TermCert`, dependent logical relations and graph/square conversion | No abstract category-with-families interface, syntax interpretation theorem, internal predicate calculus, identity-type model, universe, or cohesive modality |
| [`CategoryMap`](../../SquareKit/CategoryMap.lean), [`CartesianMap`](../../SquareKit/CartesianMap.lean) | Object/hom maps, separate preservation laws, composition, induced semantic equivalence and law reflection, non-strict product comparisons | Predicate reindexing, quantifier preservation, comprehension and dependent substitution coherence |
| [`FirstOrderNaturality`](../../SquareKit/FirstOrderNaturality.lean), [`STLCNaturality`](../../SquareKit/STLCNaturality.lean) | Interpret explicit term syntax and compose preservation proofs without another syntax induction | A derivation calculus for propositions and its model-parametric soundness; STLC preservation alone does not establish validity of an internal logic |
| [`Relations`](../../SquareKit/Relations.lean), [`RelationalCategory`](../../SquareKit/RelationalCategory.lean) | Relation-preserving squares, graph embedding, witness presentation and product comparisons | Model-independent relational predicates and existential composition; existing `compose` composes **squares**, not arbitrary binary relations |
| [`Comma`](../../SquareKit/Comma.lean), [`CommaLawful`](../../SquareKit/CommaLawful.lean) | Comparisons between two interpretations into a common target, with Mathlib comma adapters | A comparison to a synthetic geometric model must still be constructed and proved |

`Dependent.lean` is a useful concrete model and regression example, not a
failed attempt at a general foundation. Its `pi_subst` and `sigma_subst` are
`rfl` because reindexing is ordinary function composition. That convenience
cannot be assumed for a sheaf or groupoid model. `reindexRep` explicitly
transports along the context square; `piRel` relates represented functions
without requiring a decoder for every function. The `tighten` example has a
result fiber depending on the argument value and ignores a redundant Boolean
tag. Preserve these distinctions when generalizing. Lean's proof-valued
relations here do not encode higher identity spaces.

The pinned Felix comparison is
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, as required by
[`docs/SOURCES.md`](../SOURCES.md). Inspected
[`Homomorphism.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
separates `CategoryH`, product comparison arrows (`ProductsH`), their inverse
laws (`StrongProductsH`), and cartesian preservation (`CartesianH`). Reuse
this division: a predicate interpretation map should extend an existing
category map with exactly the logical operations it preserves. Do not require
exponentials or dependent products for an existential fragment.

Felix's
[`MakeLawful.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
proves `LawfulCategoryᶠ` and `LawfulCartesianᶠ` under equivalence induced by the
interpretation. The pinned upstream file does not supply closed-law proofs.
The local [#37 implementation](felix-parity-implementation.md#closed-law-transport-37)
provides `ClosedMap.transportCongr` and `ClosedMap.transportLaws` in
[`ClosedMap.lean`](../../SquareKit/ClosedMap.lean). They derive source currying
congruence, beta, eta and currying naturality. Full law transport requires target
congruence and laws, category/product/closed preservation, inverse laws for the
chosen product and exponential comparisons, and reflection of the chosen source
relation. Currying congruence needs only map congruence, reflection, target
composition/currying congruence and currying preservation.
Comparisons may be non-strict; the source relation may be induced by the
interpretation. Source closed laws are conclusions, not premises.
The implementation record includes composed interpretations and the existing
`CodeCategory` consumer. Similarly, predicate
preservation can transport a theorem forward, but cannot reflect validity
without a separate hypothesis. Equality in one selected model is not a proof
of a syntactic equation valid in every model.

Felix's
[`Construct/Comma/Type.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda)
stores a comparison arrow at each object and two arrows satisfying a square
modulo semantic equivalence. This supplies the shape of an external comparison,
not its geometric proof. Use the existing Lean comma implementation for such
comparisons. Keep an internal derivation, validity in a model, and a comparison
to ordinary mathematics as three separately named results.

### Proposed shared interfaces

These interfaces serve the first experiment's reusable proof interface. They
let a theorem author use equality, conjunction and existential witnesses while
a model implementer proves once what those operations mean. A model comparison
then transports the interpreted result to an existing consumer. They are an
initial design for that fragment, not the interface for the entire differential
cohesive theory.

Start with a small predicate interface over a lawful context category with
chosen finite products (terminal object and binary products). The experiment
must establish whether this design saves caller work; no new declarations or
final interface decisions are introduced here.

- A preorder fiber `Pred Γ` with entailment, top and binary meet; a reindexing map
  `σ* : Pred Γ → Pred Δ` for each substitution `σ : Δ → Γ`, preserving those
  operations and identity/composition.
- A distinguished equality predicate `δ_A` in `Pred (A × A)`, realized by
  the diagonal subobject in categorical models. Equality of terms is its
  reindexing along their pair. Prove reflexivity and substitutivity, together
  with substitution stability; do not identify every internal equality with
  Lean's `Eq` on global elements.
- For existential reasoning, left adjoints to the relevant projection
  reindexings, with Beck–Chevalley and Frobenius laws. Package operations and
  their laws separately. Do not assume a topos, universes, or Π-types.
- A map between predicate models over an existing `RawMap`/Mathlib functor,
  with naturality under substitution and preservation of only the selected
  connectives. Use explicit context comparisons when products differ.
  Prove identity/composition once and interpretation naturality once.
- Add implication and universal quantification only in a separate extension
  with right adjoints and their substitution laws. A regular or geometric
  interpretation map need not preserve these operations.

For categorical models, use Mathlib `Subobject Γ` instead of introducing a
second subobject implementation. At the repository pin,
[`Subobject.Basic`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Subobject/Basic.lean)
already provides `existsPullbackAdj` under images and pullbacks.
[`RegularCategory.Basic`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/RegularCategory/Basic.lean)
proves `Regular.exists_inf_pullback_eq_exists_inf`, the Frobenius equation.
Its future-work list still includes interpretation of regular logic. Reuse
these results; the proposed interface and syntax soundness are work remaining.
A law field is a requirement on an adapter, not evidence that any adapter
exists.

A shallow interface gives short proofs using named introduction/elimination
lemmas, with validity represented by entailment in `Pred Γ`. It can support
ordinary Lean notation without changing Lean's kernel. Explicit syntax adds a
separate derivation object and a soundness theorem, allowing the same proof to
be interpreted in several models and inspected for which rules it used.
Prototype both frontends over the same semantics. Prefer the shallow frontend
for mathematical use unless the explicit frontend demonstrates useful proof
reuse; retain a small explicit calculus as a check on rule admissibility.
Neither frontend should expose chosen pullback cones to each application.

## First experiment: internal graphs, external squares

This is the proposed Stage A of #36, specified here in detail. It is the first
test of shared internal reasoning connected to existing external mathematics:
one internal proof, interpretations in two constructed models, and a proved
comparison reaching the repository's square interface. Regular logic uses only
equality, conjunction and existential witnesses for this example, so the test
can run before a smooth or higher model exists.

The intended result is evidence that the proof and comparison interfaces are
reusable and convenient. It is not evidence for Kock–Lawvere, higher identities
or cohesion. Those require their own constructions. This experiment has not
yet been implemented or checked.

For arbitrary objects `A`, `B`, `C`, arrows `f : A → B`, `g : B → C`, and
context variables `a : A`, `c : C`, prove the internal equivalence

```text
(∃ b : B, b = f(a) ∧ c = g(b))  ⟷  c = g(f(a)).
```

The forward derivation eliminates the existential and substitutes its equality;
the reverse chooses `f(a)`. These are intuitionistic rules. State the result as
two sequents in context `A × C`; the displayed equivalence need not add an
implication connective to the syntax. Derive associativity for arbitrary
relational composition using the same existential rules, to show that the
interface also supports relations that are not function graphs.

**Constructed models.** First interpret contexts as Lean types and predicates
as sets, with equality, intersection and existential image. Then interpret
contexts as presheaves `Jᵒᵖ ⥤ Type` and predicates as subfunctors. Choose a
nontrivial indexing category with a nonidentity restriction map in the checked
example. This forces proofs that predicates and witnesses respect restriction,
rather than testing only another copy of Set.

Mathlib's
[`Subfunctor.Image`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Subfunctor/Image.lean)
constructs range, image and preimage pointwise and proves `image_le_iff` and
`image_comp`. Its
[`Subfunctor.Subobject`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Subfunctor/Subobject.lean)
provides `orderIsoSubobject`. These are concrete inputs for proving the
adapter, not a reason to assume the whole soundness theorem. Prove the
remaining equality, substitution, Frobenius and Beck–Chevalley obligations.
If a generic categorical adapter proves more expensive, first complete the
explicit subfunctor adapter using these pointwise constructions.

**Preservation and comparison.** Evaluation at `j : Jᵒᵖ` sends a presheaf
context to its type of sections at `j`. Prove that it preserves the selected
regular operations and that interpreting the graph theorem then evaluating
agrees with evaluating the arrows then using the Set theorem. Image and
intersection are pointwise in this model. This assertion is intentionally
restricted to presheaves and this fragment: evaluation of arbitrary sheaves
at an object need not preserve existential images, and pointwise evaluation
does not in general preserve presheaf implication or universal quantification.

**Existing consumer.** For exact representations `R → S → T`, specialize
`f` and `g` to the two decoding maps. The theorem identifies existential
composition of their graph predicates with the graph of the composite decoder.
For two compatible pairs of horizontal maps preserving those graphs, prove
that their pair preserves the composite relation by mapping the intermediate
witness. Compare the resulting `RelSquare` with
`Relational.ofSquare` of the vertically pasted exact square, after transporting
both source and target relation representations along the
proved predicate equalities. Include equality symmetry to match
`Relational.graph`'s convention `decode r = s`. Then use `RelSquare.ext` to
retain both implementation and specification maps.
Also recover horizontal composition compatibility via the existing
`RelationalCategory.graphMap_laws`. These are different composition statements;
neither follows just by calling the other one.

A second consumer uses arbitrary relations, with a checked two-valued relation
that has no unique decoder. It must prove the same existential-composition
preservation result and separately construct a presentation with an explicit
intermediate value as data, for example a subtype of `A × B × C`. Prove the forgetful map
to the existential composite relation and preservation of these witnesses.
The existing `Relational.witness` of an existential relation stores only its
endpoints and a proof in `Prop`; it does not retain the intermediate value
as data. This exercises the requirement in ADR 0002 that enclosure and
stability contracts remain relations. No runtime witness-erasure claim follows.

**Caller effort and acceptance.** A model implementer supplies reindexing,
logical operations and their local laws once; a comparison implementer supplies
preservation once. A theorem author uses variables, substitution and logical
rules. Application callers supply their decoding maps or relations and local
preservation hypotheses, with no new syntax induction or pullback diagram.
The experiment passes only if the same internal derivation serves both models,
the comparison theorem reaches existing square declarations, and the
many-valued example requires no decoder. Record actual caller obligations
before and after, rather than counting lines of notation.

Every new formal statement needs the repository's statement review and checked
specializations. Recheck all sources and the transitive proof audit with
`direnv exec . ./check.sh`; no new axioms are permitted. Neither an unchecked
notation example nor an instance with unproved law fields completes this
experiment.

## Stages and follow-up tasks

[#36](https://github.com/VladimirMarko/conaled/issues/36) owns the long-term
work. This table is a proposed decomposition, not an alternative to building
the full model and not a fixed linear schedule. Implementation tasks should
be scoped under #36; #35 remains the research issue.

Stage A is exactly the graph experiment above, not another preliminary step.
Stage B develops its author-facing interface. Stage C groups two strands that
need further decomposition: sheaf logic and dependent contexts. Stages D and E
have different model obligations and can be investigated in parallel; the
full orbifold comparison in F requires their compatible combination. This
ordering aims to deliver usable shared mathematics early, but the small graph
example cannot justify the later architecture by itself.

| Stage / task | Acceptance and preserved results | Changes and explicit exclusions |
|---|---|---|
| A. Graph experiment (specified above) | Implement the small shared interface, Set and nontrivial presheaf adapters, a rule-restricted derivation, soundness, evaluation preservation, and the graph/square comparison above. Preserve existing square and dependent-family public statements. | Add predicates and logical interpretation to `SquareKit`; no SDG, higher equality, sheaf descent or kernel changes. The smallest missing prerequisite is the shared rule/interpretation interface and its concrete adapters, not a new category or sheaf implementation. |
| B. Usable proof frontend | Compare shallow rule lemmas with explicit typed syntax on graph composition, relational associativity and Frobenius. Prove capture-avoiding substitution/soundness for the explicit fragment; hide context bookkeeping in checked notation or elaboration. Demonstrate a second application such as interval relation composition. | Syntax may change; model semantics and preservation statements from A remain. Elaborator output must be kernel checked. No automatic translation of arbitrary Lean proofs. |
| C. Sheaf logic and dependent contexts | Construct the sheaf predicate adapter, prove local existential semantics and the preservation fragment for chosen functors. Adapt a CwF/comprehension interface only after selecting a maintained source; recover `Dependent.lean` as a specialization and prove dependent comparison coherence. | Extend from fixed product contexts to dependent families. Preserve A's regular fragment. General Π preservation requires separate hypotheses; a geometric morphism alone does not supply it. |
| D. An internal SDG fragment in a proved model | Specify a site and scalar object, construct the model, prove the exact KL axiom required, interpret one imported synthetic derivative theorem, and compare an ordinary smooth-map instance to Mathlib differentiation. Audit the entire dependency closure. | Internal scalars, maps and quantifiers replace native `ℝ`, arbitrary Lean functions and native quantification in the synthetic theorem. External analytic theorems remain intact. A dual-number calculation or an assumed KL field is insufficient. |
| E. Higher identities and cohesion | Select a model of higher dependent types with substitution, identity elimination, universes at the required scope and relevant truncation; construct cohesive/crisp operations and verify each required modal law. Reinterpret a chosen earlier fragment via a proved comparison. | Replace set-level identity semantics where necessary. An ordinary sheaf topos and a set quotient do not establish this stage. Any alternate kernel/axiom trust boundary needs a separate explicit decision. |
| F. Orbifold presentation comparison | Interpret the particular Myers hypotheses and prove the chosen proper étale presentation corresponds to the internal construction, including isotropy and tangent transport. State precisely which theorem of Myers is recovered. | Adds descent/completion and geometric comparison. Until then, classical groupoids and simulator data remain useful external realizations, without being advertised as synthetic orbifolds. |

Stage D depends on adequate sheaf/internal-function semantics from C, but need
not wait for E's higher foundation. The combination must prove that the
infinitesimal and cohesive structures are compatible with the higher model;
separate records of their laws are insufficient. Classical orbifold
presentation work can also continue independently. To reach F, the obligations include higher
identity spaces that retain stabilizers; the cohesive adjunctions and crisp
context discipline; the synthetic smooth line, infinitesimals and
microlinearity; and the comparison between proper étale classical groupoids
and their synthetic completion. The exact source obligations are recorded in
[the Myers assessment](myers-orbifold-assessment.md#theorem-correspondence).
Proving only an ordinary category equivalence does not discharge them.

The adoption boundary remains ADR 0001: standard pinned Lean/Mathlib, shared
foundations in `SquareKit`, domain uses in `Applications`, compositions in
`Examples`, and all declarations reachable by the public entrypoint and proof
audit. No dependency pin, foundational axiom or ADR is changed by this note.

[sdg]: https://github.com/riccardobrasca/SDG/tree/e4cd622492aba9be421ec0abcf152f58a0ee98df
[sdg-paper]: https://arxiv.org/html/2603.17457v2
[sdg-toolchain]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/lean-toolchain
[sdg-manifest]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/lake-manifest.json
[sdg-license]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/LICENSE
[sdg-ci]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/.github/workflows/build-project.yml
[sdg-defs]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/Basic/Defs.lean
[sdg-choice]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/Axiom/UniqueChoice.lean
[sdg-deriv]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/IsKockLawvere_one/Deriv.lean
[sdg-taylor]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/IsKockLawvere/TaylorMulti.lean
[sdg-em]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/IsKockLawvere_one/EM.lean
[sdg-alpha]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/Basic/Alpha.lean
[ground]: https://github.com/rzrn/ground_zero/tree/2cbca29485c2e6f420c120365e00fe3b70db3acf
[ground-checker]: https://github.com/rzrn/ground_zero/blob/2cbca29485c2e6f420c120365e00fe3b70db3acf/GroundZero/Meta/HottTheory.lean
[ground-id]: https://github.com/rzrn/ground_zero/blob/2cbca29485c2e6f420c120365e00fe3b70db3acf/GroundZero/Types/Id.lean
[ground-ua]: https://github.com/rzrn/ground_zero/blob/2cbca29485c2e6f420c120365e00fe3b70db3acf/GroundZero/Theorems/Univalence.lean
[ground-circle]: https://github.com/rzrn/ground_zero/blob/2cbca29485c2e6f420c120365e00fe3b70db3acf/GroundZero/HITs/Circle.lean
[ground-trunc]: https://github.com/rzrn/ground_zero/blob/2cbca29485c2e6f420c120365e00fe3b70db3acf/GroundZero/HITs/Trunc.lean
[2ltt]: https://github.com/jthulhu/2ltt/tree/6077427bdc4d7e0c521c18f811a54d2dcf85c0a0
[2ltt-obj]: https://github.com/jthulhu/2ltt/blob/6077427bdc4d7e0c521c18f811a54d2dcf85c0a0/Tltt/ObjLang.lean
[2ltt-hott]: https://github.com/jthulhu/2ltt/blob/6077427bdc4d7e0c521c18f811a54d2dcf85c0a0/Tltt/Hott.lean
[2ltt-reedy]: https://github.com/jthulhu/2ltt/blob/6077427bdc4d7e0c521c18f811a54d2dcf85c0a0/Tltt/Reedy/ReedyPresheaf.lean
[lean2]: https://github.com/leanprover/lean2/tree/8072fdf9a0b31abb9d43ab894d7a858639e20ed7
[lean2-hott]: https://github.com/leanprover/lean2/blob/8072fdf9a0b31abb9d43ab894d7a858639e20ed7/hott/hott.md
[lean2-book]: https://github.com/leanprover/lean2/blob/8072fdf9a0b31abb9d43ab894d7a858639e20ed7/hott/book.md

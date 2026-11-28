# Myers properness: source and model assessment

Assessment against repository `970350f9ce3b85ba81f1af304382f0aee2e7d083`. This is an initial assessment, not completion of #724 or adoption of a new foundational architecture. Start with the independently checked [096-10 obstruction](myers-properness-096-10-verification.md); retain its conclusions and receipts. No new Lean or Agda check was run for this assessment.

## Exact source target

Pin David Jaz Myers, *Orbifolds as Microlinear Types in Synthetic Differential Cohesive Homotopy Type Theory*, arXiv **2205.15887v1**, submitted 31 May 2022. The HTML retrieval identifies v1 but displays a later rendering date; use the version identifier, not that display date, as the publication pin.

[Definition 6.2.1](https://arxiv.org/html/2205.15887v1#S6.SS2.Thmthm1) tests all propositions and predicate families for compactness and all compact subtypes for properness. [Definition 6.3.6 and Theorem 6.3.7](https://arxiv.org/html/2205.15887v1#S6.SS3.Thmthm6) require an ordinary manifold pregroupoid with crystalline-étale source and DP-proper anchor; a crisp such presentation has orbifold Rezk completion. The proof uses microlinearity descent, hom/identity comparison, compact hom fibers, and the discrete compact-subset finiteness lemma. Crispness of the presentation does not restrict the predicates tested by DPProper.

[Theorem 6.4.1](https://arxiv.org/html/2205.15887v1#S6.SS4.Thmthm1) gives an alternative finite-group quotient route. Its identity fibers are subobjects of the finite group, so [Lemma 6.1.5](https://arxiv.org/html/2205.15887v1#S6.SS1.Thmthm5) applies without DP compactness. [Warning 6.2.3](https://arxiv.org/html/2205.15887v1#S6.SS2.Thmthm3) distinguishes subfinite from DP-compact; [Warning 6.2.20](https://arxiv.org/html/2205.15887v1#S6.SS2.Thmthm20) supplies the equality-dependent control.

The original comparison target remains 6.3.7. Select the finite-label identity-family consequence of 6.4.1 as the defensible alternative first comparison contract below, explicitly recording the changed route. This does not silently amend 6.3.7 or discharge its properness premise.

## Source signatures and assumptions

The exact inspected Agda definitions, in the user-supplied checkpoint 521, are:

```
DPCompactAt p (K : Type ℓ) : Type (max ℓ (suc p))
  = (A : hProp p) (B : K → hProp p) →
      ((x : K) → A ∨ B x) → A ∨ ((x : K) → B x)
DPCompact K = DPCompactAt ℓ K
DPProper (f : X → Y), X Y : Type ℓ
  = (U : Y → hProp ℓ) → DPCompact (Σ y, U y) →
      DPCompact (Σ x, U (f x))
```

Here `∨` is truncated disjunction; neither binder is `@♭`. The signatures live in the successor universe and introduce no resizing. `ProperMaps.proper→CompactFibers` requires `isSet Y`; the reverse direction does not. The unrestricted higher-codomain version must not replace this theorem. Primary locations: `myers/src/Orbifolds/Compactness.agda:40–47`, `ProperMaps.agda:35–37,49–50,76–88` in checkpoint 521.

`FullProperEtaleOrbifolds.Context.Presentation.Ordinary.proper-etale-completion-orbifold` is a conditional source theorem. Its signature supplies these inputs rather than constructing a joint model:

- Crisp level, commutative ring, Kock-field evidence, category, and invertibility of arrows; crisp identity induction at the carrier and zero levels and zero-level flat induction/computation.
- Ordinary strict order, ordered-ring compatibility, Principle of Constancy, finite object/arrow dimensions and ordinary manifold structures.
- Real-flat axiom, crisp excluded middle, tininess of the actual `𝔇`, flat/truncation distribution at `ℓ` and `suc ℓ`, and preservation of crisp pullbacks by crystalline reflection.
- Covering Property, DP compactness of the unit interval, positive-line equivalence, **DPProper of the actual source-target projection**, and crystalline étaleness of the actual source projection.

These are read from `myers/src/Orbifolds/FullProperEtaleOrbifolds.agda:34–69`, not inferred from the use of the cohesion compiler flag. The target is the full orbifold predicate of the actual completion. `𝔇` is the full double-negation neighborhood; it is not the first-order square-zero disk `D`. The archive's `math/properness.md` traces the tininess premise to paper Axiom 3, Postulate W, printed page 30, and `𝔇` to Definition 4.2.3, printed page 33. Treat that wider source proof as conditional; this assessment does not revalidate its entire import closure or all its paper dependencies.

The minimal verified diagonal obstruction has much fewer assumptions: a commutative ring, KockField and first-order KL. KockField supplies nontriviality and the finite-tuple inverse condition. First-order KL asserts that the affine map `R × R → R^D`, `(a,b) ↦ (d ↦ a + b*d)`, is an equivalence for `D = {d | d² = 0}`. This must be interpreted as an exponential, never arbitrary functions on a stage's underlying set. The [096-10 statement review](myers-properness-096-10-verification.md) is the fresh checked authority for this dependency claim.

## The separating control

For a set `X`, the checked implication is `DPProper Δ_X ↔ decidable equality on X`. A DP-compact proposition has decidable inhabitation. The diagonal fiber at `(x,y)` is the proposition `x=y`, so unrestricted properness decides this equality for ordinary, varying `x,y`. Under KockField and first-order KL this contradicts the verified smooth-line result. No crispness assumption on the *map* removes those varying test fibers.

On the classical side, [Examples.FiniteActionPresentation.Trivial.diagonal_map](../../Examples/FiniteActionPresentation.lean) proves Mathlib `IsProperMap (fun x : ℝ => (x,x))`; `Trivial.diagonal` identifies the actual trivial-group anchor with it. Thus the prohibited contract is precise: an interpretation preserving the represented smooth-line diagonal and validating Kock/KL cannot send this external proper map to unrestricted internal DPProper. It is not a prohibition of every interpretation or every properness comparison.

The alternative below retains `x=y` as a potentially undecidable proposition. Such a proposition embeds in the singleton finite object. It has decidable equality *between its inhabitants*, since it is a proposition; this does not decide whether it has an inhabitant. This is why subfinite/properly-finite identity types do not imply the forbidden DP-compact fibers.

## Selected alternative contract and actual maps

Fix a finite ordinary group `G` acting smoothly on a finite-dimensional manifold `M`. In the current smooth sheaf category let `G̲` be its locally constant group sheaf, `jM` the constructed manifold realization, and `Q` the constructed torsor quotient stack. For every sheaf parameter `T` and maps `x,y : T → jM`, compare the **actual** chart-arrow family with

```
H(x,y) = { g : T → G̲ | action(g,y) = x }.
```

The desired statement is a natural equivalence, with both inverse laws, between the interpreted source identity family of the two quotient chart points and this family. Its label projection must be a monomorphism into `T × G̲` in the slice over `T`, and agree with the label of the actual classical arrow after realization. Restriction must pull back the whole equation and commute with both maps. `G` is externally fixed finite data; `T,x,y,g` vary ordinarily. No endpoint equality is made decidable and no predicate class is silently restricted to crisp inputs.

This semantic chart equivalence already exists as [SheafActionQuotient.chartArrowEquiv](../../SquareKit/SheafActionQuotient.lean), with relation `action(g,y)=x`, and is connected to ordinary arrows by [SmoothActionGroupoid.arrowIso](../../SquareKit/SmoothActionGroupoid.lean), its endpoint equations, and the completion unit. The outstanding comparison is its identification with an admitted source identity/subfinite derivation in the constructed smooth interpretation. Existing code is the semantic implementation to reuse, not a reason to create another quotient representation.

At ordinary points an action arrow `x → g·x` uses label `g`; quotient chart arrows use the inverse label. [SheafGroupoidCompletion.quotient_label](../../SquareKit/SheafGroupoidCompletion.lean) records that inverse. Preserve this orientation under composition and tangent transport.

Positive example: the proper étale trivial `C4` action on the real line from [groupoid-branches](groupoid-branches.md), with the actual arrow model and independent switched branch charts. Each loop fiber retains all four ineffective labels. Also retain the existing S3 noncommuting composition and quarter-turn fixed/nonfixed controls. Negative control: the trivial-group real-line diagonal is externally proper and satisfies the subfinite-label contract, but its varying equality fibers cannot uniformly be DP compact under the displayed Kock/KL assumptions. The positive example is positive for the **alternative** contract, not a new DPProper assertion.

For arbitrary quotient objects `P,Q` over `T`, regular-chart labels exist only after a common trivializing cover. Their isomorphism sheaf must be locally a subobject of the finite locally constant label object, with transitions derived from actual torsor arrows. A globally chosen label map for every pair would exclude nontrivial torsors. Reuse effective descent and full faithfulness of the completion unit, retaining its comparison isomorphisms. Likewise, finite local branch data for general groupoids give local finite-labelled displays, not automatically one global finite ordinal or the source theorem's properly-finite predicate. That last identification remains to be proved.

A map `T → G̲` can change label across disconnected components. Hence `H(x,y)(T)` need not have cardinality at most `|G|`. For the trivial action on `r` discrete components there are `|G|^r` loop sections. This mathematical control follows directly from locally constant labels; the existing disconnected-stage examples already reject factoring every section through one fixed summand. Keep [SmoothBranchRealization.stageEquiv/fiberEquiv](../../SquareKit/SmoothBranchRealization.lean) and restriction laws intact.

## Properness predicates that remain separate

| Predicate | Inputs and output | Available or missing comparison |
|---|---|---|
| Mathlib `IsProperMap` | Actual topological map, ordinary topology and compactness | Finite-action anchors and the diagonal are checked. [ProperLocalBranches](../../Applications/Orbifolds/ProperLocalBranches.lean) derives finite local branch diagrams from this hypothesis. |
| Internal `DPProper` | Every internal proposition-valued subtype, unrestricted compactness formula above | The diagonal blocks the proposed blanket external-to-internal implication. No current source/model comparison was found in the inspected production interfaces. |
| `Compact.ProperData` | A selected finite-open-subcover operation for every compact subtype, relative to explicit open fragments | In checkpoint 521 this is `Orbifolds.Intensional.CompactSeparation.ProperData`; some imports call that module `Compact`. `CompactData` returns an actual list of cover indices and membership witnesses; it is not proposition-valued. Ordinary classical compactness plus external choice can supply this data at a fixed universe, but such an adapter is not a sound non-Boolean DP interpretation. |
| Finite-labelled hom display | Mono into a finite constant object, locally after charting; actual endpoint equation retained | Semantic action-chart comparison exists. Interpretation of the source finiteness statement and its passage to all quotient identities remain. |

For the third row, primary definitions are checkpoint `CompactSeparation.agda:45–65,204–207`. Its closed-graph and finite-label anchor proofs explicitly use classical propositional excluded middle. They cannot be transported unchanged into a non-Boolean smooth model merely because their chosen topology is geometric.

## Current interpretation facilities and exact gaps

The [#433 construction](smooth-source-interpretation.md) is completed. `SmoothQuotientSource.model a T` interprets the unchanged first-path transport proof over the entire torsor quotient and its deformation family, with arbitrary-parameter and generated-section descent. Its contexts, substitutions, identity and dependent J rules are reusable. It is not necessary to reopen #433 or assert that no smooth interpretation exists.

The inspected `Internal.PathTransport.Typed.TyDeriv` constructors are base, fiber, identity and substitution. Its all-rule smooth instance does not thereby admit a universe of propositions, arbitrary predicate quantification, finite-object membership, truncation, general dependent sums, or crisp/modal judgments. `Internal.Logic.FormulaCore` supplies equality, binary atoms, conjunction and existential formulas, not the unrestricted DP formula. `Internal.DependentFunctions` is a bounded base-indexed function syntax. The modal-access Boolean experiment and the higher group family do not supply Myers's cohesive/crystalline modalities. The finite complementary-predicate classifier is a different classifier theorem; its name is not evidence of a source subfinite universe.

`SmoothGeometricKL.kl` is an actual sheaf-exponential isomorphism, with coefficient recovery at arbitrary parameters. This is a valid first-order KL input. It does not by itself establish the exact Kock-field predicate, ordered axioms, interval compactness, Covering Property, tininess of `𝔇`, or a joint higher/crisp model. Current sheaf groupoid stackification supplies quotient objects and descent, not microlinearity or those modal rules. Reuse [general-groupoid-completion](general-groupoid-completion.md) where no action presentation is available; do not impose a global action presentation on that completed result.

## Precise prerequisite tasks to record

These are scoped prerequisites under #724/#36, coordinated with the completed #428 assessment and #433 infrastructure. Recording them does not schedule implementation. Before adopting source extensions or a new semantic organization, apply the repository design-challenge requirement.

1. **Admit and interpret the finite-subobject proof.** Pin a small constructive derivation using Definitions 6.1.1 and 6.1.3: a subtype of `Fin n` embeds in that finite ordinal, is a surjective image of itself, and has decidable equality, hence is properly finite by Lemma 6.1.5. This requires neither decidable membership nor inhabitedness. Admit only the finite object, proposition family, dependent subtype and truncated witnesses used by that derivation. State source universes and substitution rules. Construct its semantics in slices of the existing smooth sheaf category, using actual finite locally constant objects, and prove soundness/naturality. Controls: an arbitrary proposition as a subtype of `Fin 1`, empty subtype, and disconnected local labels. Reject an inference of DP compactness. Deliver source syntax/derivation plus semantics, not a native Lean theorem relabelled internal. Owner: #36, prerequisite of #724; reuse #433's context/substitution conventions where they fit.

2. **Connect interpreted identities to the existing finite-action label family.** Starting from task 1 and the existing smooth quotient model, admit exactly the chart identity/fiber comparison needed to consume that source derivation. Prove that its semantic map is `chartArrowEquiv` with the inverse-label convention, agrees with `SmoothActionGroupoid.arrowIso` and the completion unit, and commutes with arbitrary parameter restriction. Extend from chart objects by the already constructed common-cover descent, with no global trivialization assumption. Retain four ineffective C4 loops, an S3 composition, nontrivial torsor recovery, and the diagonal. Owner: #724/#36, technical reuse of #433 and #719/#720/#727. This yields the selected finite-identity comparison, not yet full microlinearity or a properness equivalence.

3. **Validate the exact scalar hypotheses needed for the separating control in the selected model.** Against the current smooth presentation site, formalize the Kock finite-tuple clause with internal negation, local existence and all substitutions. Either construct it from the actual site's cover/ring properties and combine it with existing `SmoothGeometricKL.kl`, or exhibit the exact stage/cover obstruction and record a needed model restriction. Do not replace internal negation by a nonzero external section. Interpret the already verified diagonal argument in that same model; no added axiom or assumed comparison is acceptable. Owner: #36, prerequisite for a model-level negative half of #724. The external Cahiers argument in checkpoint 521 is a proof lead, not this Lean model construction.

#724 must retain the further full-theorem obligations: source/model microlinearity and modal/crisp requirements, their compatibility with the higher quotient and completion, and the precisely selected properness comparison. A stronger classical-to-DP bridge remains impossible when it includes the represented Kock/KL diagonal. A restricted bridge on separately justified finite/discrete maps is not ruled out; it needs its own admitted map class and theorem. No current result warrants closing #724 after these initial findings.

## Checkpoint 521 provenance and evidence boundary

Only selected files were read/extracted outside the repository. The archive SHA-256 is `1f6100552e1bc52b96fa50cb8054757aabf5e550b5b41691ecfa96bbe7ec0906`. Selected primary files:

| Member under `myers/` | SHA-256 |
|---|---|
| `src/Orbifolds/Compactness.agda` | `6c0a2a15999d76e55849a8ece282cbdd1a0adcb31f07e31bd20a5e8a86dbc5e2` |
| `src/Orbifolds/ProperMaps.agda` | `26afb9e9501666aebcc9d25c089552b72fc155bd10d3efa91afecbc9ba153b1f` |
| `src/Orbifolds/ProperCompactDecisions.agda` | `e6ec3b66c2c1614b22268d5870f734d130f9e2dd1d4e783a747d649d19184ee6` |
| `src/Orbifolds/ExternalPropernessObstruction.agda` | `4c65d0cb2e388b0ceaf2c89cffd5d22426b85035b02edca0887200bc19857779` |
| `src/Orbifolds/FullProperEtaleOrbifolds.agda` | `47c94ef11b406f8bca66b0c42ab6162fbe7d385c4619fea77a80cf72d0cb3a27` |
| `src/Orbifolds/Intensional/CompactSeparation.agda` | `724df65ba4d4ae4cdc7131c800341b0f07012d8546f2f959ee0fba0df7788ee4` |
| `math/properness.md` | `8bac4f9f8fc8bfd3e9faf75c15312c2e54896aaa27553183146e7a6b86964bc5` |

The three obstruction/full-theorem source hashes match `state.json`, which marks them accepted via inherited `Everything` evidence. The inspected aggregate receipt reports exit code zero and stable sources; its ledger explicitly limits this to inherited evidence, not a fresh combined release. The ledger says `project_complete: false`. This assessment checked source bytes and selected signatures; it did not rerun checkpoint 521 or independently certify its native compiler protocol. The independently replayed 096-10 receipts remain the basis for the verified obstruction. Neither archive acceptance nor the paper proof supplies a constructed joint smooth/cohesive model in Lean.

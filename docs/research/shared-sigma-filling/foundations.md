# Shared Sigma filling: contract and foundations assessment

Assessment of issue #627 at `9aa0520591e7d107b63f9172a496fe7332b24cb8`. This is the initial independent report. I inspected the supplied brief, full issue body, repository guidance, native constructions and their stated clients. I did not inspect the other assessors' reports or coordinate conclusions. The historical synthesis in `docs/research/shared-cubical-constructors.md` was supplied context. No source files were changed, and no Lean experiments or builds were run. The unrelated uncommitted Lawvere work was excluded.

## Recommendation and retaining evidence

Extract a local two-stage construction with separate boundary and substitution theorems. Retain both native algorithms, their signatures, and their primitive box lemmas. Prefer a theorem telescope or small records for one source problem and one target problem over a global category of contexts. Native contexts, caps, faces and families instantiate the local problem; they need not become one shared model.

The strongest evidence is the existing code. `SumFilling.lean:10` and `CartesianDependentFilling.lean:123` perform the same first-fill, dependent-second-box, second-fill, pair sequence. Their uniformity proofs (`SumFilling.lean:30`, `CartesianDependentFilling.lean:143`) use the same equality between first-section subtypes, then the primitive second-box substitution equation, then second-component uniformity. The substantive argument is already separate from reversal, connections, classifier operations and representables. The proposed extraction therefore has a demonstrated mathematical client in each model.

No defect in either current theorem was established. The issue is duplicate proof work and an unimplemented reusable interface.

## Primitive operations and derived guarantees

For one fixed native problem `(p, φ, r, b)`, with the cap absent as an explicit argument in the De Morgan specialization, the following data suffice:

- First box `u = fst b`, first-section type `A`, first-fill operation `F`, and predicate `P a = u.Fills a`.
- Second-section family `B : A → Type`, second-box family `V : A → Type`, and second-box constructor `S : (a : A) → P a → V a`.
- Second-fill operation `G : (a : A) → V a → B a` and its boundary predicate `Q : (a : A) → V a → B a → Prop`.
- Pair operation `J : (a : A) → B a → C`, where `C` is the whole-section type, and whole-box predicate `R : C → Prop`.

The selected operation is exactly `J (F u) (G (F u) (S (F u) hF))`, where `hF : P (F u)`. A shared definition of this expression can recover the native expressions by reduction; keeping the existing native definitions and proving their equality to the expression is also acceptable. Recovery must be checked, not inferred from equal boundary behavior.

The boundary argument needs component filling and the operation-level pairing rule

```text
∀ a (ha : P a) c, Q a (S a ha) c → R (J a c).
```

This rule is legitimate primitive interface evidence: it concerns arbitrary first and second sections satisfying the component boundaries and mentions neither selected filling operation. It is already proved as `OpenBox.sigmaIntro_fills` in `PartialSums.lean:62` and `CartesianDependentFilling.lean:81`. The shared theorem applies it to the two selected component fillers. Requiring `R (selectedSigma b)` instead would assume the target theorem.

The second-box type depends on the first section; its construction additionally consumes its boundary witness. Those are different dependencies. Native code makes them explicit in `PartialSums.lean:48` and `CartesianDependentFilling.lean:67`. Indexing only by an arbitrary first section would lose the cap and tube identifications needed to construct the second box. Indexing every second-section type by a proof as well as the section is unnecessary for these clients and can add transport obligations.

The construction itself needs only first-component boundary evidence. The public native API currently receives the stronger `hF : F.Lawful`; preserving that API is harmless. The generic construction need not demand first-component uniformity until proving uniformity, nor second-component lawfulness until proving its laws.

## Smallest substantive substitution theorem

Use source and target copies of the preceding data, with primes denoting the target. The theorem should expose actual maps of first boxes, first sections, dependent second boxes, dependent second sections and whole sections:

```text
R_U : U → U'
R_A : A → A'
R_V : (a : A) → V a → V' (R_A a)
R_B : (a : A) → B a → B' (R_A a)
R_C : C → C'
```

Here `U` and `U'` are first-box types. The source and target full boxes are fixed parameters, with distinguished projections `u` and `u'`. Supply these equations and witness transport:

```text
u' = R_U u
F' (R_U u) = R_A (F u)
R_P : ∀ a, P a → P' (R_A a)
∀ a ha, S' (R_A a) (R_P a ha) = R_V a (S a ha)
∀ a v, G' (R_A a) (R_V a v) = R_B a (G a v)
∀ a c, J' (R_A a) (R_B a c) = R_C (J a c)
```

This is a mathematical telescope, not checked Lean syntax. It can be packaged into records if doing so reduces adapter repetition. The first-box equation must refer to the actual projection of the reindexed full box. In the native adapters it appears definitionally true, but it should be exposed as a named obligation or checked `rfl` argument, rather than discarded from the contract. `R_P` is native `OpenBox.Fills.reindex`, with the first-box equation accounted for.

Derivation:

1. Combine first-box substitution and first-component uniformity to equate the selected target first section with the transported selected source section.
2. Apply `Subtype.ext` to obtain equality in `{a' // P' a'}`. Proof irrelevance makes no additional equality of boundary proofs necessary.
3. Apply congruence to the target continuation `fun z => J' z.val (G' z.val (S' z.val z.property))`.
4. Rewrite the second-box substitution equation, apply second-component uniformity, then pair substitution.

The result is equality of the complete selected target output with `R_C` of the complete selected source output. No input is a law of the selected Sigma operation. In particular, do not replace the last three equations by an assumption that the entire target continuation commutes with transport: that would move most of the duplicated argument into adapter obligations.

The native proofs already execute steps 1–4, except that first-box and pair substitution are discharged through definitional equality. `PartialSums.lean:78` and `CartesianDependentFilling.lean:97` supply the genuinely dependent second-box equations. The native section pairing definitions are pointwise (`TypeFormers.lean:58`, `CartesianDependentFamilies.lean:46`). This supports expecting small adapters, while Lean elaboration and exact recovery remain untested here.

No identity or composition axioms for an abstract category are needed to prove this one-substitution theorem. A native substitution composite is another instance. To claim a generic composable transport API later would require explicit coherence of all its maps; this bounded theorem need not make that additional claim.

## Concerns and discriminating checks

**Established acceptance gaps in the baseline:** the existing native filling proofs are duplicated. `Examples/SharedCubicalConstructors.lean` checks classifier recovery, but its `sigma_code_comp` concerns codes, not the extracted filling derivation. Its dependent variable-cap theorem quantifies over a supplied box. It does not itself construct a proper-face dependent box and run two particular nonidentity substitutions through the shared proof.

**Circularity risk:** a field asserting final `sigmaFilling_lawful`, final selected-output preservation, or preservation of the entire continuation would make the extraction too weak to meet #627. Primitive pair-boundary and second-box substitution laws are permitted because they quantify over arbitrary component sections and witnesses independently of the selected algorithms.

**Dependency risk:** a proof based only on first values and ordinary congruence of the second filler is ill-typed when the second family varies with the first. Preserve the subtype step in the shared proof. The existing Boolean-tagged `Fin 1`/`Fin 2` family in `Examples/CartesianClassifier.lean:19` is a suitable separating application. Test both tags rather than replacing the family with a constant product.

**Scope risk:** making the common parameter a Boolean endpoint would weaken the Cartesian theorem. Keep the Cartesian arbitrary cap term and arbitrary `Subcontext` in the adapter, including cap substitution. The shared theorem has no reason to constrain these indices. The De Morgan adapter retains fixed false cap and `Cofibration`.

**Proof-irrelevance boundary:** the proposed subtype proof uses Lean equality and Prop-valued boundary predicates, as the current native proofs do. It does not establish reuse in a setting where boundary witnesses carry relevant higher identity data. No extra proof field for coherence of Prop witnesses is justified for the present clients.

**Cost uncertainty:** a large global record could cost more to instantiate than the shared proof removes. First implement the local telescope and inspect the resulting native adapters. Acceptance should show that both native uniformity bodies delegate their subtype/congruence argument, with adapters supplying existing primitive lemmas, rather than repeating that argument twice under new names.

Run these discriminating checks during implementation:

1. Prove exact native operation recovery for arbitrary lawful inputs and complete output sections. Try `rfl` first. Recheck existing native reduction clients if definitional equality is lost.
2. Keep both public `sigmaFilling`, `sigmaFilling_fills`, `sigmaFilling_uniform` and `sigmaFilling_lawful` signatures available. Verify that the shared theorem proves their bodies without using either old final theorem.
3. Construct an inhabited dependent Sigma box with a variable Cartesian cap and a proper face. Retain evidence that the cap differs from the false endpoint and that the face is neither universally true nor empty. Existing variable and endpoint-face definitions provide ingredients, but the report's evidence does not include this combined instance.
4. Use two explicitly nonidentity native substitutions, check each complete filled section and their composite, and compare successive reindexing with composite reindexing. Check the first-section witness and second box at the intermediate stage. Classification-code composition alone does not test this interface.
5. Preserve the endpoint-map rejection from `Examples/SharedCubicalConstructors.no_interval_identification`. Instantiating one abstract proof twice supplies no map between the two intervals or between their chosen fillers.

## Limits and next action

This recommendation rests on inspected declarations and a paper derivation. I did not run elaboration, a build, or an axiom audit, and I did not establish an author-effort measurement. The existing native code is the evidence for feasibility; the proposed telescope remains to be checked.

Implement the local proof first, instantiate both native adapters, and inspect whether complete operation recovery is definitional. The model-specific obligations that should remain are box formation, witness reindexing, dependent second-box substitution, and the component filling laws. The shared module should own the two-stage boundary derivation and dependent uniformity argument. This meets the bounded extraction without adding a classifier interface or claiming a cross-model bridge.

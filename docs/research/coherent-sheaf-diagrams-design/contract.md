# Fixed-context diagrams: contract and foundations

Baseline: `ba7ee812cbcc3024c235e72832d1f4aa840a5139`. Initial independent assessment; no other lens reports read. Relevant repository task-authority, domain, architectural-quality, language-direction, formal-development, EDD and prose guidance was consulted. No tracked files changed.

## Recommendation

Package the equivalence of diagrams over each arbitrary `K : I ⥤ D`, and its restriction to cartesian diagrams, as a bounded derived capability. Existing theorems establish the ingredients but do not currently give a category equivalence usable by ordinary categorical transport. Reuse an existing Mathlib category, preferably a thin abbreviation for based functors or for the fiber of postcomposition. Do not introduce a separate category structure or ask sheaf callers for additional coherence.

The mathematical benefit is an equivalence retaining every vertical natural transformation, including noninvertible ones, and therefore a connection on which categorical constructions can operate. Merely declaring the unrestricted functor-category equivalence adds little: `totalEquivalence.congrRight` already supplies it. The useful work is the restriction and its cartesian consequence.

## Exact category and proposed contract

For `p : C ⥤ D`, define the intended category by either existing presentation:

```lean
Functor.Fiber ((whiskeringRight I C D).obj p) K
```

or

```lean
BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)
```

Objects are diagrams `A : I ⥤ C` with `hA : A ⋙ p = K`. A morphism is an arbitrary natural transformation `η : A ⟶ B` satisfying

```lean
whiskerRight η p = eqToHom (hA.trans hB.symm)
```

The based presentation expresses the same condition componentwise through `IsHomLift p (𝟙 (K.obj i)) (η.app i)`. Both existing categories preserve independent object and hom universes. A fiber abbreviation is lighter if the implementation only needs restriction. Based functors supply composition and whiskering already, and are worth comparing before writing fiber transport helpers.

The category is generally NOT the full subcategory of `I ⥤ C` selected by `A ⋙ p = K`. Objects alone do not force a transformation to project to the identity of `K`. In particular, for `p = 𝟭 Type`, a constant Boolean diagram admits the componentwise constant-false transformation in the ambient functor category, but it is not vertical. The scratch probe checks this rejection for any inhabited index category.

For the current sheaf assumptions, with `pC = forget (codePseudofunctor G J)` and `pS = forget (J.pseudofunctorOver (Type w))`, the proposed result is

```text
DiagramsOver pC K ≌ DiagramsOver pS K
```

The functor and inverse must recover `A ⋙ totalDecode` and `A ⋙ totalCode` on underlying diagrams, and whiskering on transformations. The unit and counit must recover whiskered total recovery and counit, with their actual verticality certificates. This recovers objects, all compatible maps, identities and composition; no diagram transition is required cartesian.

A generic helper can take an ordinary equivalence `e : C ≌ C'` over `D`, strict projection equations for both functors, and verticality of the unit/counit. Its restriction is ordinary categorical transport, independent of sites. Do not replace these hypotheses with only an unrestricted equivalence: an arbitrary chosen inverse can fail to land in a strict fiber even when its image is isomorphic over the base. Here all required equations and verticality are already proved.

## Cartesian restriction and derivability

For a fixed-context diagram `A`, define the object property

```text
∀ i j (f : i ⟶ j), p.IsCartesian (K.map f) (A.map f).
```

The equality `A ⋙ p = K` supplies the endpoint and hom-lift transports. A formulation using `p.map (A.map f)` is equivalent and can reduce transport bookkeeping.

Take the FULL subcategory of `DiagramsOver p K` on this property. Fullness is correct here: all vertical natural transformations between cartesian diagrams remain, without requiring their components to be cartesian or invertible. In particular, a cartesian-section category need not be a groupoid. Requiring cartesian components of its maps would discard the intended noninvertible vertical maps.

The existing `totalDecode_cartesian` and `totalCode_cartesian` prove preservation for every diagram arrow. They impose no new sheaf assumptions. Restrict the chosen functor and inverse, then lift the unit/counit through the full-subcategory inclusion; the triangle equation follows from the original one. This route needs preservation in both directions and no separate public reflection axiom.

Alternatively, `Equivalence.congrFullSubcategory` applies after proving an iff of object properties and closure under isomorphisms. Both are derivable: a vertical diagram isomorphism conjugates each transition by vertical component isomorphisms; `IsCartesian.of_iso_comp` and `of_comp_iso` preserve cartesianness. Forward preservation, inverse preservation and the vertical unit then yield reflection. Do not add these derived properties to the caller contract.

These restriction arguments are paper derivations from inspected definitions and theorems, not a checked implementation of the entire equivalence.

## Inspected source evidence

- `Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`: `Fiber`, `fiberCategory`, `fiberInclusion`, and `inducedFunctor` provide exactly the object and morphism restriction. Inclusion is faithful; it is not declared full.
- `Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean`: `BasedFunctor`, `BasedNatTrans`, `homCategory`, `BasedFunctor.comp`, `BasedCategory.whiskerRight`, and `BasedNatIso.mkNatIso` already provide the alternative native presentation. Basic definitions allow independently sized total categories; the final bicategory instance fixes their sizes, so using that instance needlessly could reintroduce universe constraints.
- `Mathlib/CategoryTheory/Equivalence.lean:418`: `Equivalence.congrRight` supplies unrestricted diagram equivalence.
- `Mathlib/CategoryTheory/ObjectProperty/Equivalence.lean:66`: `congrFullSubcategory` restricts an equivalence when its object-property and iso-closure hypotheses are proved.
- `Examples/CoherentSheafFibration.lean:29–143`: recovery, projection, arbitrary-map compatibility and cartesian preservation are already stated for generic diagrams. These should become consequences of the packaged capability or remain connected to it, not acquire duplicate independent proofs.
- `SquareKit/Internal/CoherentSheafFibration.lean:308–412`: total equivalence, both projection equations, original and packaged vertical recovery, and preservation in both directions provide the restriction inputs.
- `SquareKit/CoGrothendieckTransport.lean:130–166`: fixed-base hom lifting/reflection and cartesian reflection already exist at the total comparison level.

## Checked probe and acceptance application

`contract/Probe.lean` passed with:

```sh
direnv exec /home/vlad/Code/conaled lake env lean /tmp/conaled-diagrams-assessment/contract/Probe.lean
```

It checks both category presentations with independent universes; derives the exact displayed equality for a fiber morphism using `IsHomLift.fac'`; rejects the constant-false Boolean transformation from the fixed-context category; and checks that composition with an arbitrary based functor transports diagrams and all their vertical transformations. Only stylistic `haveI` warnings remain. This is bounded evidence for the interface and the consequential non-fullness risk.

An initial sheaf-import probe could not run because the current checkout lacks `Examples/CoherentSheafFibration.olean`. No build was launched, and the final probe uses only existing Mathlib artifacts. No complete categorical equivalence, cartesian restriction, site specialization or integrated audit was checked by this assessment.

For implementation acceptance, use the existing Boolean collapse as a noninvertible vertical transformation between constant diagrams. Such diagrams are cartesian since their transitions are identities, while their maps need not be invertible. Apply the proposed cartesian equivalence and recover that transformation through the public unit; establish that its image is still noninvertible. Also retain the current nonidentity-context composite case and add a changing-context cartesian diagram to exercise transitions rather than only identity arrows. This distinguishes the promised all-map category from an accidentally selected groupoid. The current direct diagram theorems and sheaf assumptions must continue to hold unchanged, with unequal and reversed universe checks.

The smallest useful alternative is to expose the existing `BasedFunctor` presentation and package only postcomposition equivalence plus the cartesian full-subcategory restriction. A new sections framework, a universal bicategory of heterogeneous based equivalences, or changes to sheaf classification are unnecessary for this contract.

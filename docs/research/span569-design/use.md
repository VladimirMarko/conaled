# #569 implementation and client assessment

Recommend the existing slice realization over any category C with pullbacks, with the selected-pair acceptance client in C = Type. Both admissible leg classes are all morphisms. They contain identities and are closed under composition and pullback. Freeze sums as `Over.map`, reindexing as `Over.pullback`, and adjunctions as `Over.mapPullbackAdj`. No exponentiability, dependent products, terminal objects, or left exactness assumption is needed for this action.

## Construction and proof route

Reuse Mathlib `Span (⊤) (⊤)` and its apex maps. For S : X <- S.apex -> Y define A(S) = `Over.pullback S.l ⋙ Over.map S.r`, covariant from Over X to Over Y. For e : S ⟶ S', the component at V is the slice map with underlying arrow

`pullback.lift (pullback.fst V.hom S.l) (pullback.snd V.hom S.l ≫ e.hom) (...)`.

The two leg equations on e prove the lift condition and Over Y condition. Its first projection is the unchanged V-value; its second projection is the old apex witness followed by e. This makes an actual functor from the category of spans X→Y into the category of functors Over X→Over Y. Naturality, identity, and composition reduce to `Over.OverMorphism.ext` and `pullback.hom_ext`. Do not restrict apex maps to isomorphisms: a collapsing map between duplicate witnesses is a necessary test.

For S : X→Y and T : Y→Z let P = pullback S.r T.l, p = pullback.fst, q = pullback.snd. The existing checked cell

`DependentBaseChange.leftComparison (IsPullback.of_hasPullback S.r T.l)`

has type `p* ⋙ Σq ≅ Σ(S.r) ⋙ (T.l)*`. Expand A(S;T) using `Over.pullbackComp p S.l` and `Over.mapComp q T.r`, then whisker this cell on the left by S.l* and on the right by Σ(T.r), adding functor associators. This produces A(S;T) ≅ A(S)⋙A(T), exactly the orientation of Mathlib `Pseudofunctor.mapComp`. Its invertibility follows from the pullback universal property in `DependentBaseChange.outer`, not from an unrestricted assertion about mates. `leftComparison` itself is the current actual sum/base-change cell; `pullbackComparison` is its defined mate. If the deliverable calls the chosen sum comparison a mate, explicitly identify it by applying `mateEquiv.symm` to `pullbackComparison`, using the equivalence inverse law.

Define the unit comparison with `Over.pullbackId` and `Over.mapId`. Prove the associator and both unit equations by natural transformation extensionality, slice-map extensionality, and projections. For associativity the observations needed are the original V-value and each of the three span-apex coordinates. Mathlib supplies the source associator projection lemmas `SpanBicat.associator_hom_hom_πₗ`, `..._πᵣ_πₗ`, and `..._πᵣ_πᵣ`, as well as unitor equations. These proofs are new obligations, not supplied fields on a new client-facing record. Prove compatibility with left/right whiskering as well: it is required for the actual pseudofunctor, even though the issue foregrounds associators and units.

A small composition helper is useful as the implementation layer, but cannot by itself fulfill the requested action. The least duplicated architecture is native action/projection helpers using existing Span data, followed by Mathlib Pseudofunctor packaging. Avoid another category of spans, another chosen-adjunction record, or another record asking users for final coherence laws. The direct `IndexedSumFamilies.first` and `twice` interfaces remain usable.

## Selected client and proposed discriminating examples

The existing checked `IndexedSumFamilies` client stores `Selected I P γ := (i : I γ) × P γ i`; `first_value`, `first_base`, `twice_value`, and `twice_base` retain the whole dependent pair and selected context. `IndexedSumBaseChange.encode` bridges independent native fibers to chosen categorical pullbacks. Recovery should identify a specific component of mapComp with `leftComparison`, and then derive these observations. Merely asserting existence of an isomorphic result does not recover this client.

Use three composable correspondences with independent mathematical specifications, for example:

1. N <- (N × Bool) -> N, left (n,b)↦n, right (n,b)↦n+n. This duplicates a selected dependent value and changes its output base; witnesses with false and true stay distinguishable.
2. N <- N -> N, left k↦k+k, right k↦k+1. Composition with the first forces k=n and retains the selected Bool branch while shifting the output. This exercises a genuine intermediate matching equation.
3. N <- (N × Fin 2) -> PUnit, left (k,j)↦k, right constant. This introduces another retained choice and collapses the final context. The full composite retains n, Bool, Fin 2, and the original dependent value.

Take the starting family V over N with fiber `Fin (n+1)` and choose its last element. Both parenthesizations must return the same selected value and the same three apex coordinates under the source associator. Neither the output base alone nor existence distinguishes the branch witnesses. Prove at least one mismatch fails to lift (the second span cannot match an odd intermediate natural) and distinguish the two Bool witnesses. For a noninvertible apex map, add the collapse from the first span to N <- N -> N with legs id and doubling. Its action preserves the selected value but collapses the Bool witness, so it must not be reported as an isomorphism.

These are proposed fixtures, not checked declarations. Existing native `first`/`twice` recovery should additionally use the actual sum span `(id,indexMap I)` followed by reindexing span `(σ,id)` and then `(τ,id)`. Their mapComp components are the canonical comparisons already observed by the native client. This ties the new action to the repository's actual use, while the three correspondences above test more than repeated substitutions.

## Controls and future interpretation maps

Reuse `Examples.MatesBaseChange.noninvertible_inverse_mate`, which references `IndexedWitnessAdjunctions.NonPullback.inverse_mate_not_invertible`. It rejects inferring an invertible original cell from its invertible mate. It is a control outside the pullback hypothesis, not a counterexample to the slice span pseudofunctor. `IndexedSumBaseChange.comparison` supplies the forward map for an arbitrary commuting square. Without cartesianness this has the composite-to-iterated orientation used by an oplax comparison; it does not automatically define an oplax span action on arbitrarily chosen squares, because associativity/unit compatibility still needs proof.

For F : C⥤D preserving pullbacks, components `Over.post F` should intertwine A_C(S) with A_D(FS). Use `MixedBaseChange.iso F S.l` and the post/map compatibility. Preserve the value and apex projections through `MixedBaseChange.comparison_fst/snd`; prove unit and composition compatibility, including the canonical apex comparison F(S×Y T) ≅ FS×FY FT. `MixedBaseChange.composition` and `context_composition` provide checked local pasting equations but do not already package the whole span-level transformation.

`Examples.MatesBaseChange.forget_comparison_iso` and `forget_not_leftExact` for F=`Over.forget Bool` supply a relevant positive control: pullback preservation suffices even though finite-limit preservation fails. This example should instantiate the interpretation comparison, not be forced into geometric-morphism data. Without pullback preservation the mixed forward comparison still exists; span composition transport has noninvertible apex comparisons and should be described with the actual direction rather than promoted to a pseudonatural equivalence.

## Validation boundary

This report inspected current sources and Mathlib APIs read-only. No proposed definitions or proofs were elaborated and no builds were run. The main implementation uncertainties are proof normalization for Mathlib's adjunction-derived `Over.pullbackComp`, universe parameters of the target Cat, and packaging the native coherence proofs in `Pseudofunctor`. Establish projection lemmas for pullbackComp early; if its opaque construction causes repeated work, prove equality to the explicit universal-pair comparison once. These are Lean proof costs, not missing mathematical hypotheses. A completion claim still requires the ordinary action, all coherence fields, selected native recovery, checked discriminating examples, and applicable full audit/review.

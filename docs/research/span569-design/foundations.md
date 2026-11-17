# Independent foundations and coherence assessment for #569

Recommend the slice realization for an arbitrary category C with pullbacks, with the Type specialization retaining the existing indexed pairs. Use all morphisms as both admissible legs (`⊤` properties), and the actual adjunction `Over.mapPullbackAdj`. No local cartesian closure, right dependent products, terminal-object preservation, or chosen final coherence law is needed. Mathlib's existing `Span` and `SpanBicat` supply the source; avoid creating another span record. Construct the action and its concrete projection lemmas first, then package the proved laws as a `Pseudofunctor` to `Cat`.

This is a proposed proof route based on source inspection, not a checked new implementation. No Lean commands or full builds were run.

## Variance and exact construction

For S = (X ←l S →r Y), define A(S) = `Over.pullback l ⋙ Over.map r`, from Over X to Over Y. Thus the action is covariant on spans, despite being contravariant on each left leg. A span map k:S→S' with k;l'=l and k;r'=r induces A(k):A(S)→A(S'), also covariantly. At U→X its underlying arrow is the pullback lift from U×X S to U×X S' whose components are the old U projection and old S projection followed by k. This retains both the full selected value and the apex; its Y compatibility follows from the right triangle. Naturality and preservation of identity/vertical composition follow by pullback extensionality. This explicitly allows noninvertible apex maps.

In Type, a selected element is (u,s,h), where h:U.hom u=l s. The map is (u,s,h)↦(u,k s,h'). It is not existential image or quotienting. Fiber over y additionally records r s=y. Thus the selected apex index and payload survive; only deliberately applying `Nonempty` forgets selection.

For composable spans S=(l,r), T=(m,n), put P=S×Y T with p:P→S and q:P→T. Source composition has legs p;l and q;n. Freeze the compositor in the direction required by Mathlib:

    c[S,T]: A(S≫T) ≅ A(S) ⋙ A(T).

Expand the source with `Over.pullbackComp p l` and `Over.mapComp q n`. Its middle expression is p* followed by Σq. Replace precisely that expression using

    DependentBaseChange.leftComparison (IsPullback.of_hasPullback r m)
      : p* ⋙ Σq ≅ Σr ⋙ m*.

Whisker by l* and Σn, with explicit functor associators. This gives c in the correct direction without reversing 1- or 2-morphisms. Invertibility here follows from the pullback universal property (`outer`, `isoPullback` in DependentBaseChange), not from a blanket rule about mates. `IndexedSumBaseChange.comparison_eq` identifies its forward arrow with the elementary commuting-square lift; `DependentBaseChange.pullbackComparison` is explicitly the mate of that same leftComparison under the sum/pullback adjunctions. Recovering the leftComparison via inverse mate equivalence can document the precise BC origin if needed.

At U→X, c sends (u,(s,t)) to ((u,s),t). Its two outer projections must be established as actual arrow equations; the first projection itself is characterized by its U and S projections. Retaining only U and the final base Y/Z does NOT characterize this map when apex indices are nonunique. Prove the complete U,S,T component equations before relying on extensionality.

## Deriving coherence rather than assuming it

The native helper can define c directly through universal lifts and prove it equals the above BC composite. This keeps proof reduction manageable while preserving the specified BC comparison. It must not silently substitute an arbitrary equivalence with unproved agreement.

For three spans S,T,R and an object U, both paths in compositor associativity land in the iterated pullback representing (((u,s),t),r). Expand their natural-transformation components, apply `Over.OverMorphism.ext`, then nested `pullback.hom_ext`. The resulting equations are equality of the U,S,T,R projections. Source reassociation is exactly Mathlib's span associator, with its already proved `associator_hom_hom_πₗ`, `associator_hom_hom_πᵣ_πₗ`, and `associator_hom_hom_πᵣ_πᵣ` equations. Target associators are functor associators. This is a concrete proposed proof of the required `map₂_associator` field, not an assumption that the span bicategory's pentagon alone establishes it.

Define the unit comparison using `Over.pullbackId` and `Over.mapId`. On U its arrow forgets the identity-pullback base and returns u. Mathlib's `leftUnitor_hom_hom` and `rightUnitor_hom_hom`, together with the compositor projection equations, reduce both action-unit compatibilities to U and apex projections. The repository already proves `DependentBaseChangeIdentity.pullbackId_hom_left`, which gives the precise normalization arrow. This avoids pretending chosen pullbacks of identities are definitionally identities.

Whiskering compatibility remains an explicit proof obligation. Prove compositor naturality under maps in each span variable using the same U,S,T projection equations; translate to Mathlib's `map₂_whisker_left/right` fields. An oplax-first implementation with `Pseudofunctor.mkOfOplax` is also reasonable, but does not eliminate the associator/unit proof obligations. Since c is already an iso, direct packaging has fewer layers unless oplax clients actually materialize.

## Boundaries and discriminating clients

Three correspondences should involve genuinely nontrivial apices and both legs, not three reindexing graphs. A useful Type fixture uses finite base sets and apices carrying extra Bool labels, with legs ignoring at least one label. Choose a payload type with distinguishable values and two witnesses having the same final base but distinct labels. Test the associativity map on all retained labels and payload. Include an apex map that folds a Bool label, proving its induced transformation is noninvertible while preserving the payload and right base. This distinguishes the action from existential truth and catches proofs observing too few projections.

Recover `IndexedSumFamilies.first` by the composable spans (Sigma I ←id Sigma I →indexMap Γ) and (Γ ←σ Δ →id Δ), whose composite apex is `index₁`. Compare action/compositor with the exact native chosenIndex/chosenValue encoding using both projections and `IndexedSumBaseChange.selected`. The identity leg normalizations matter. Recover `twice` by appending the analogous τ span and invoke the proved associator law. Keep the original declarations directly usable. Tagged sums require the existing adjoint-uniqueness conjugations, not definitional equality of realizations.

For a commuting square not known cartesian, `IndexedSumBaseChange.comparison` only gives the forward map p*Σq→Σr m*. In the above orientation that is oplax-shaped (A(composite)→A(S)A(T)); its inverse lax-shaped comparison is unavailable. This observation alone does not create an oplax action on any arbitrary proposed noncartesian composition system: that source would still need an associative composition and coherent square choices. Within ordinary spans with chosen pullbacks, BC is invertible. Preserve the Empty/Unit mate control separately; it refutes the unjustified general mate-invertibility inference, not this pullback-specific construction.

For a future ambient functor F:C→D, `Over.post F` supplies objectwise interpretation. `MixedBaseChange.comparison` gives the actual comparison for pullback portions; pushforward/postcomposition compatibility follows from F.map_comp. Pullback preservation makes these invertible and supplies comparison between F(P) and the chosen composite apex in D. The two projection laws and `MixedBaseChange.composition/context_composition` are existing evidence for the required compatibility. Full pseudonatural transport coherence still needs proof. The #556 pullback-preserving but non-left-exact example fits because this construction requires pullbacks, not terminal objects or all finite limits.

## Adoption criterion and remaining gaps

Direct native pairs are suitable for a single calculation but do not express action on arbitrary span maps or reusable associator compatibility. A small composition helper can centralize the actual BC arrow and projections, but completing #569 requires proving its unit and associator laws anyway. Mathlib packaging then gives an established interface for those new capabilities and avoids a custom law record. The sensible dependency direction is concrete action/projections → coherence proofs → Pseudofunctor wrapper → Type/native recovery, with projection lemmas available without clients opening bicategorical notation.

The implementation risks are elaboration and universe plumbing for `Cat`, normalization through the adjunction-defined `Over.pullbackComp`, and enough projection lemmas to keep nested extensionality local. None was tested in this assessment. There is no evidence from these files of an existing turnkey span-to-slices pseudofunctor. No new assumption of final coherence, all-mates invertibility, or left exactness is justified.

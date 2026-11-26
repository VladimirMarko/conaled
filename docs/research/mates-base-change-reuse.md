# Mates and base-change reuse with retained witnesses

Assessment for [#556](https://github.com/VladimirMarko/conaled/issues/556),
2026-11-15. The starting repository revision is
`c214fb0720ffc998951255a7e4b5f2e80a299186`; the inspected Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This is a bounded ordinary-category
implementation and framework assessment within [#555](https://github.com/VladimirMarko/conaled/issues/555).
It supports both interpreting an argument in different settings and transporting
its supplied maps between settings. It does not implement the higher six operations.

## Result and decision

Adopt two small extensions of existing interfaces:

* [`MixedBaseChange`](../../SquareKit/MixedBaseChange.lean) constructs the mixed
  slice comparison for any functor between categories with pullbacks. Its
  identity, ambient composition and context composition laws require no adjoint
  or preservation assumption. Pullback preservation supplies the isomorphism.
* [`AdjointSquareTransport`](../../SquareKit/AdjointSquareTransport.lean) transports
  curried and uncurried arrows through two pasted adjoint squares. It uses
  Mathlib's `TwoSquare` and `mateEquiv`, without introducing another square record.
  Equality of the whole pasted mate is supplied by Mathlib's pasting theorem.

Retain the geometric interface as the convenient native specialization. Its
universal-property proof is already appropriate; mates do not manufacture the
projection-preserving input square. Investigate a span pseudofunctor and maps
between such interpretations for additional capabilities described below.
Reject automatic invertibility of arbitrary mates. Defer a higher correspondence
implementation to #555's foundation study, rather than interpreting this ordinary
experiment as an expressive ceiling.

## Inspected contracts

| Source | Actual data and assumptions | What it does not supply |
|---|---|---|
| [`GeometricMorphism`](../../SquareKit/Internal/GeometricMorphism.lean) | Inverse/direct image functors, a specified adjunction, finite-limit preservation; transformations are all transformations of inverse images. | Tensor, exceptional operations, or higher categorical structure. |
| [`GeometricSlice`](../../SquareKit/Internal/GeometricSlice.lean) | `onSlices` constructs a slice adjunction; `along` needs `Closed (Over.mk s)` and pullbacks. | Exponentiability of every map in every base category. |
| [`GeometricMixedChange`](../../SquareKit/Internal/GeometricMixedChange.lean) | `pullbackPost` uses the preserved pullback and retains both projections; identity and both composition directions are proved. `mixedGeometricIso` also requires closure of both relevant slice objects. | A reason that arbitrary mates are invertible. The comparison itself does not need those closure assumptions. |
| [`Family`](../../SquareKit/Family.lean) | Display maps, sections, universal pairs, actual chosen pullbacks, identity/composition isomorphisms. | Strict equality of iterated and flattened pullback objects. |
| [`DependentBaseChange`](../../SquareKit/DependentBaseChange.lean) | An actual `IsPullback`; left comparison, its pullback mate, and dependent-product mate for supplied right adjoints. `mate_conjugate` obtains invertibility by *iterated* mating into the restricted conjugation correspondence. Evaluation and curry laws retain maps. | A free invertibility rule for a single general mate, or a strict split family presentation. |
| [`AdjointComparison`](../../SquareKit/AdjointComparison.lean) | Curry/uncurry and mate compatibility under canonical replacement of both chosen right adjoints. | A comparison between unrelated settings without functors and comparison cells. |
| [`IndexedWitnessAdjunctions`](../../Examples/IndexedWitnessAdjunctions.lean) | Two nonidentity substitutions retain index 3 and value 8 over context 5; alternative sum adjoints retain the selected pair. Empty/Unit refutes pullback and invertibility claims. | Recovery of a selected dependent pair from existential truth. |

Pinned Mathlib supplies ordinary
[`mateEquiv_vcomp`, `mateEquiv_hcomp`, `mateEquiv_square`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Mates.lean),
with explicit functor associators and unitors. `conjugateIsoEquiv` is the restricted
isomorphism correspondence; it must not be substituted for arbitrary `mateEquiv`.
The [bicategorical mate module](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean)
already has horizontal, vertical and square pasting and conjugation laws. The
[span module](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Span/Basic.lean)
constructs spans with specified left/right morphism properties, identities,
composition and suitable pullback stability. Its 2-morphisms retain apex maps and
both projection equations. These are existing foundations to reuse, not features
this issue has implemented. No general packaged Beck–Chevalley formalism was
identified in the inspected adjunction and slice modules beyond these facilities.

## First client: exact geometric recovery

`MixedBaseChange.comparison F σ` has component the actual
`pullbackComparison F Z.hom σ` in the slice. Universal pairing proves naturality
and the two projections. `iso` adds only
`PreservesLimitsOfShape WalkingCospan F`. No direct-image functor is requested.

`geometric_recovery` equates the whole natural transformation with
`(h.pullbackPost σ).hom`; `geometric_iso_recovery` equates the entire natural
isomorphism. `geometric_context_recovery` identifies the actual pasted map.
[`Examples.MatesBaseChange`](../../Examples/MatesBaseChange.lean) then proves the
original first projection, second projection, identity, ambient composition and
context-composition statements through the general laws. The old declarations
remain unchanged. This is recovery of their maps and equations, rather than a
second comparison with a weaker observation.

The context law has a genuine two-stage input:
`pullback (pullback.snd p σ) τ`. One route maps the original flattening isomorphism
then compares the composite substitution. The other applies the two ambient
comparison maps and pairs their final value/context projections. Their equality
is proved without invertibility assumptions. Ambient composition separately
compares a composite functor with the pasted comparison maps in the original order.

`forget_context_paste` specializes this law to `Over.forget Bool : Over Bool ⥤ Type`.
It changes the setting from displayed types over Bool to their underlying types.
It retains the underlying maps of arbitrary displayed values and substitutions.
`forgetComparisonIso` also constructs its invertible comparison.
`forget_not_preservesFiniteLimits` proves that this functor cannot be the inverse image of a
geometric morphism: the terminal display over Bool forgets to Bool, which is
not terminal in Type. Thus this client is outside the original finite-limit
contract while satisfying the weaker pullback-preserving one. This is not a
claim that all display information can be recovered from the forgotten type.

A mates-only replacement of the first client would require adjunctions on the
edges being transposed. The original `pullbackPost` does not require
`Closed (Over.mk σ)`. Insisting that pullback along σ be a left adjoint would
add exponentiability, an unjustified stronger client hypothesis. Using its
existing right-adjoint role still starts from a comparison cell whose projections
must be proved. Consequently the pullback universal property remains the better
construction here. This finding concerns this client, not the suitability of
bicategorical machinery for other operations.

## Second client: actual dependent-product transport and pasting

For adjunctions `L ⊣ R`, `L' ⊣ R'`, a square
`s : G ⋙ L' ⟶ L ⋙ H`, and an arrow `k : L X ⟶ Y`, the shared theorem proves

```
G.map (curry k) ≫ (mate s).app Y = curry (s.app X ≫ H.map k).
```

This needs a comparison, not its inverse. Two such squares produce
`curry_paste` and `uncurry_paste`; `mate_paste` equates their entire pasted
transformation with the mate of the input paste. Thus interpretation uses the
same universally quantified proof in each setting, while transport uses the
specified connecting functors and square. Separate interpretation alone would
not provide that connecting equation.

`DependentBaseChange.curry_recovery` recovers the original single-square curry
contract through the generic theorem. `DependentBaseChange.curry_paste` specializes the generic theorem to two actual
pullback squares with three specified product adjunctions. It retains the exact
canonical mates of `DependentBaseChange.WithAdjunction`; no replacement product
is chosen. All involved family maps, including their display equations, survive.
The pasted input retains iterated pullbacks. We do not claim strict equality
with a separately chosen flattened outer-square product presentation.

The `FiniteProducts` client supplies these hypotheses constructively:

* The original display is `Nat → PUnit`, with the existing terminal-product
  adjunction. The value family is `n ↦ Fin (n+1)` and the chosen dependent function
  selects `n`, proved by the reused `selected_value` theorem. `different_fibers`
  independently rejects an equivalence between its fibers at zero and one.
* Base change is first along `Nat → PUnit`, then along `n ↦ n+1`. Both squares
  are actual pullbacks; `sigma_not_injective` shows the first change collapses
  distinct parameters, and `tau_not_identity` rejects an identity interpretation of
  the second substitution. The two new right adjoints are constructed by
  `ExponentiablePullback.squareAdjunction`, not postulated.
* `twice` applies the two canonical mates to that chosen function.
  `twice_evaluation` identifies its actual uncurried family map with the original
  body mapped along both changes and composed with the pasted input comparison.
  `pasted_mate` also identifies the full transformations before choosing that value.

The concrete `twice_evaluation` is an inferred specialization of
`uncurry_paste`; its elaborated type is inspected in the validation evidence.
This avoids repeatedly normalizing the constructed adjunctions while preserving
the actual map expression defining `twice`. The conclusion is equality of maps
in the final slice, including the retained
value and context data. It is not just equality of truth values or a separate
proof that some product element exists. The native `selected_value` calculation
establishes which function is transported; the new evaluation equation connects
that very function to the categorical route. It does not provide executable
machine code for the noncomputable categorical limit choices.

## Counterexample and statement review

`noninvertible_inverse_mate` reuses the existing Empty/Unit construction. The
commuting square has two maps `Empty → Unit` and two identities of Unit. The
sum comparison at the identity family has empty domain and inhabited codomain,
so an inverse would produce an element of Empty. The pullback condition is
independently refuted by its universal lifting property. Its forward mate is
invertible because every arrow in `Over Empty` is invertible; the inverse mate
is still the original failed comparison. This directly refutes the proposed
rule, without relying on failed instance search. The positive dependent-product
case proves invertibility using the additional pullback/iterated-conjugation
argument already present in `DependentBaseChange`.

The quantified generic claims range over arbitrary categories, functors and
supplied adjunctions. They have no invertibility premise hidden in `TwoSquare`.
The mixed comparison only requires available pullbacks until `iso` is requested.
All equalities here are ordinary Lean equalities of categorical maps or natural
transformations. They do not retain proof-relevant higher homotopies; ordinary
projection equations are propositions. No claim about arbitrary native cubical
paths follows from this study. Existing dependent sums remain selected pairs;
`no_selection_reconstruction` in the reused witness example excludes turning
propositional existence into recovery of those pairs.

## Native and shared author obligations

| Contract | Native route | Shared route and retained work |
|---|---|---|
| Geometric mixed square and projections | Preserved-pullback iso and naturality, both projections. | Same universal pair; exact recovery. Generic users need only F and pullbacks, with preservation for inversion. No reduction in the mathematics of constructing that square. |
| Both mixed composition directions | Projection uniqueness and existing flattening laws. | Same derivations shared across arbitrary F; geometric specializations supply no new laws. |
| Single curried base change | `WithAdjunction.curry_base_change` proves the counit/naturality calculation. | `AdjointSquareTransport.curry` proves the same calculation once for arbitrary squares, not just slices. Users still supply the adjunctions and input cell. |
| Twice-curried transport | Apply the single-square result twice; rewrite composition and associators. | `curry_paste` and `uncurry_paste` discharge that repeated calculation. The concrete client supplies actual squares, right adjoints and its selected input. |
| Whole comparison pasting | Could expand mate units/counits and prove their cancellation. | Direct application of Mathlib `mateEquiv_vcomp`; no new mate engine. |
| Chosen-adjoint replacement | Existing `AdjointComparison.mate` and curry/uncurry laws. | Remains available unchanged; replacement is not assumed definitionally invisible. |

This is checked derivation reuse, not an author-productivity trial. Framework
setup, specialization declarations and the concrete client's representation
adapters remain real costs. The geometric native API is shorter for its existing
users. The benefit is broader hypotheses and repeated-arrow transport, not a
claim that every old proof should be rewritten. #548 owns structural-view author
trials; this issue does not duplicate them.

## Wider frameworks and additional mathematics

Voevodsky's [Cross functors draft, §§0–1](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Unfinished_papers/Motives/2theories/Abstract/2015_td_copy.pdf)
uses adjunction transformations and exchange cells with composition requirements.
Proposition 0.4 asserts independence of adjunction-transformation sequences; its
illustration is not a machine-checked general coherence theorem. The current
experiment checks particular ordinary pasting laws through Mathlib, not that
unrestricted assertion.

Scholze's [Six-Functor Formalisms, Definitions 2.3–2.5 and Lecture IV](https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf)
packages pullback, exceptional pushforward and tensor through a lax symmetric
monoidal functor on correspondences. Right adjoints supply the remaining
operations. The construction theorem requires additional geometric/factorization
and compatibility assumptions. The ordinary slice adjunctions above do not
establish those hypotheses.

The following are design assessments, not delivered theorems:

| Candidate | Additional capability and discriminating construction | Extra assumptions and remaining author/implementation work | Decision and owner |
|---|---|---|---|
| Ordinary bicategorical mates | Interpret the same pasting argument in a bicategory whose 2-cells are not natural transformations of ordinary categories. | Choose the bicategory and adjunctions; connect its observational contract to concrete clients. Mathlib already supplies mate pasting, but the present slice projection recovery is specialized to Cat. | Investigate under #289/#235 when an independent bicategorical client needs it. |
| Span pseudofunctor | Assign to `X ← S → Y` the actual pull–push functor `r₊ l*`. Composing two correspondences then reuses base change to compare the iterated pull–push with their fiber-product span. This adds a compositional language for arbitrary correspondence strings, beyond the selected two squares. | Supply admissible arrow classes, their closure/pullback stability, functorial operations, units/composition comparisons, invertible Beck–Chevalley where required, and associator/unit coherence. Build the action on span maps and prove it respects both projections. Mathlib spans and pseudofunctors provide the shapes, not this action for our clients. | Investigate under #555/#235; a first test should recover the selected-pair sum client and a three-correspondence composite, including its associator. |
| Maps between span interpretations | Transport a whole pull–push argument between coefficient settings, rather than separately reprove it in each. | A family of comparison functors, compatibility with both leg operations, chosen-adjunction mate laws, and compatibility with span composition/2-cells. An invertible source cell cannot be moved across an unproved exchange inverse. Recover both witness projections after transport. | Investigate jointly with #557/#235; freeze the observation contract before an author trial. |
| Higher correspondences with tensor | Support projection-formula, exceptional-adjunction and duality arguments retaining their higher coherence, rather than only equations of ordinary maps. | A chosen higher-categorical representation, tensor and exceptional operations, admissibility, universe control and interpretation/transport contracts retaining specified higher witnesses. Ordinary hom-set equality is insufficient evidence. | Defer implementation, retain mathematical investigation under #555/#557. This is not rejection of the broader framework. |

For the span proposal, the concrete new argument is composition of pull–push
operators. Given spans `(l₁,r₁)` and `(l₂,r₂)`, compare
`r₂₊ l₂* r₁₊ l₁*` with the action of their fiber-product composite using the
Beck–Chevalley cell for the middle square and then leg-composition constraints.
A third span tests the associator; maps of interpretations must preserve that
same comparison, not only objectwise functors. The acceptance control is the
Empty/Unit square: without the required base-change hypothesis the comparison
can still exist, but the pseudofunctor's invertible composition constraint cannot
be asserted. A lax version may remain possible and must state its direction.
This is a specific expansion target with an owned missing contract, rather than
an inventory of unimplemented abstractions.

No textbook theorem was required to discharge these categorical hypotheses.
The new textbook corpus does not by itself supply a correspondence action or
an exceptional-operation realization. Its algorithms remain potential consumers
only when a concrete semantics provides the required adjunctions and comparisons.

## Validation scope

The focused module builds and targeted statement/axiom checks accompany this
candidate in the orchestration evidence. Full integrated build, exhaustive axiom
audit and independent Standards/Spec review are acceptance requirements handled
by the parent implementation loop. Failed development attempts are retained
there; they are not counterexamples or accepted validation. No new kernel axioms,
proof admissions, resource-limit increases or dependency changes are intended.

# #569 alternatives and interface cost

Recommendation: construct the slice pull–push action with small, projection-based helpers, using Mathlib's existing `Span` and `SpanBicat`; package its proved laws as an actual `Pseudofunctor` to `Cat`. Keep the helper API available independently. A new record asking callers for composition or associator laws would move the requested work into assumptions. A helper without those laws is a useful intermediate artifact but does not complete #569.

## Fixed mathematical scope

Take a category C with pullbacks, all maps admissible on both legs (`MorphismProperty` top), and chosen adjunctions `Over.mapPullbackAdj`. The object action is X ↦ Over X. The span X ←l S →r Y acts covariantly by `Over.pullback l ⋙ Over.map r`. In Types, this sends a selected value x over l(s), with the actual s, to the same value at output r(s). Both the value and the apex witness matter.

For an apex map h:S→S' with h;l'=l and h;r'=r, construct the natural transformation using the universal property of the chosen pullback: its underlying map preserves the input-value projection and sends the apex projection s to h(s). This is covariant on apex maps, including noninvertible ones. Identity, vertical composition and naturality follow by pullback extensionality. This part needs no invertibility hypothesis on h.

For S:X→Y and T:Y→Z with apex pullback P=S×Y T, expand the action of the composite using `Over.pullbackComp` and `Over.mapComp`. The central interchange is precisely

`Over.pullback π₁ ⋙ Over.map π₂ ≅ Over.map S.r ⋙ Over.pullback T.l`,

namely `DependentBaseChange.leftComparison (IsPullback.of_hasPullback S.r T.l)`. Whiskering this with the outer pullback and sum functors gives `action (S ≫ T) ≅ action S ⋙ action T`, the orientation expected by Mathlib's `Pseudofunctor.mapComp`. Its invertibility comes from the pullback universal property proved in `DependentBaseChange.outer`, not from a general claim that mates preserve isomorphisms.

## What the alternatives buy

| Route | Reusable result | Author obligations and remaining gap |
|---|---|---|
| Direct native selected families | Small concrete functions with immediate value equations | Repeats nesting, reindexing and association bookkeeping; does not supply an action on arbitrary spans or apex maps |
| Small composition helper | Named action, map on apex maps, BC comparison and projection lemmas | A viable implementation interface; must still derive compatibility with horizontal maps, associator and units |
| Mathlib Span plus Pseudofunctor | Existing source bicategory, standard laws and composition with future pseudofunctors | Initial categorical wrappers and equality normalization; source coherence is already supplied, target action coherence is new work |

Mathlib `Span/Basic.lean` already provides the span, span-map category, composition, associator, unitors and bicategory. With all maps admissible, no new leg-property hierarchy is justified. `Pseudofunctor.lean` exposes exactly the outstanding laws: map₂ identity/composition inherited from `PrelaxFunctor`, whiskering compatibility, associator compatibility, and both unit compatibilities. These are substantive checks, not accidental ceremony. Defining another bespoke span structure would duplicate checked source machinery without improving the selected-value interface.

The best client API need not expose bicategorical syntax. It can offer `action`, `actionMap`, `compositionIso`, and projection theorems on generalized arrows, with the pseudofunctor as a final packaging theorem. The distinction is between backend proof cost and repeated author effort. No measured author trial is available from this read-only review, so shorter future client proofs remain a prediction.

## Existing evidence and actual gaps

`IndexedSumBaseChange.comparison` is already a natural transformation for any commuting square. `comparison_eq` identifies it with the canonical invertible BC comparison on actual pullbacks. `selected`, `transport_value`, `transport_base`, `reindex_value`, and `reindex_base` retain actual arrows and both projections.

`IndexedSumFamilies.first_value`, `first_base`, `twice_value`, and `twice_base` recover the complete dependent pair, but the second reindexing requires explicit `inner`, `secondIndex`, and `secondValue`. This is concrete evidence of bookkeeping the proposed helper could absorb. It is not evidence that a span pseudofunctor has already been constructed.

`IndexedSumChoices.withSumChoices` and `choices_agree` provide comparison under alternative left-adjoint choices. The tagged sum changes carriers while retaining selected data. Reuse this as a specialization/transport check; do not create a fresh global record selecting sums before a second realization requires it.

`AdjointSquareTransport.curry_paste`, `uncurry_paste`, and `mate_paste` transport actual arrows and identify the pasted mate. They do not identify the two bracketings of three span actions or provide compatibility with Mathlib's span associator. That is the mathematical gap. Lean issues involving `Cat` universes, functor associators and chosen pullbacks are additional encoding costs, not reasons to treat coherence as already proved or lower the mathematical scope.

Derive the new laws by equality of generalized arrows using pullback projection extensionality. Establish projection characterizations of the comparison first, including the inverse or sufficient uniqueness facts. Then prove whiskering, associator and units by the same characterization. This avoids a generic Beck–Chevalley structure whose users would have to supply the final laws.

## Discriminating checks

Use three spans in Types with genuinely varying apex witnesses and noninjective legs. A proposed concrete fixture can use finite pairs, with each left leg selecting one coordinate and each right leg selecting another, so pullback composition retains compatible triples. The associator must preserve every chosen apex coordinate and the payload. Checking only the output base or a constant payload could conceal witness collapse.

Include a noninvertible apex map that forgets an extra Boolean coordinate while preserving both legs. Its induced transformation should preserve the payload and perform exactly that witness map. This catches an implementation accidentally restricted to isomorphic spans.

Recover `IndexedSumFamilies`' native dependent pair equations under the action/comparison API, including its map observations. A theorem about `Nonempty` would not satisfy this requirement. Apply both unit comparisons to an actual selected value; test the tagged sum transport using `choices_agree`.

Keep the Empty/Unit noninvertible-mate control as a negative test against overgeneralizing inversion. For arbitrary commuting squares, the existing comparison points from the pull–push route through the square to the other route, and need not be invertible. In a generalized span action with noninvertible BC cells that same composite-to-sequential orientation would be oplax under Mathlib's conventions. The category of ordinary spans still composes by actual pullbacks, so this bounded slice realization is pseudo. General oplax coherence would require separate proofs; it does not follow solely from having individual cells.

The #556 `Over.forget Bool` example in `Examples/MatesBaseChange.lean` is a useful change-of-base control: it preserves pullbacks while failing to preserve the terminal object. Future preservation requirements should demand the pullbacks actually used, not finite limits by default.

## Future change of interpretation

For a pullback-preserving F:C→D, use `Over.post F` on slice categories. The already available mixed pullback comparison and compatibility of postcomposition with `Over.map` are the ingredients comparing each span action with the action of its F-image. Preservation of selected projection equations should be explicit. A coherent map of span interpretations also needs the comparisons to respect apex maps, composition and units, including F's comparison between chosen composite pullbacks. Pointwise natural isomorphisms alone do not establish this. This is an appropriate stated contract for future work, with the concrete #556 example checking that terminal preservation is unnecessary.

This assessment inspected current source definitions and the named Mathlib interfaces. It did not elaborate proposed code, run builds, or establish an implementation cost estimate. The construction and tests above remain proposed proofs. No target files were changed.

# #698 implementation and use assessment

Pinned source: `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`. This is the initial independent implementation/use report. I did not read another #698 report or coordinate conclusions. I previously wrote the #697 use assessment and a read-only #694 audit of discrete comma recovery and ordinary span controls. That exposure suggested locations to inspect; the claims here use the delivered #694 code, rather than the earlier proposal. No Lean probes or builds were executed for this assessment. Proposed constructions below are paper derivations and declaration plans, not checked new Lean results.

## Recommendation and scope

Choose a finite path-family example over `B²(C₂)`, admit its selected nonzero dependent cell through `TwoFamily`, and use the actual total hom-groupoid as the middle correspondence apex. Extend the selected #694 comma shape to accept this apex and its base-cell projection. Construct both bracketings and both representation maps directly, then compare them on the entire selected comma morphism. Recover the original dependent 2-cell from that morphism.

This is a ready finite implementation task. It needs new finite specializations and a selected comma reassociation, but no new higher foundation. It deliberately passes a genuine 2-cell to the morphism level of its existing hom-groupoid. The implementation must prove that connection using the actual `TwoFamily.totalBicategory` and `projectionHigher.mapFunctor`; calling an unrelated group arrow a 2-cell would not satisfy it.

The selected total 2-cell has nonzero **base** component and a forced dependent fiber boundary. Its fiber component is an equality cell because this path fiber is locally discrete. This proposal does not claim a nonzero independent fiber 2-automorphism. If that stronger condition is intended, it must be stated as an additional contract; `fiberLoop 1` alone would meet that stronger observation but would not supply the nontrivial dependent action required here.

## Inspected machinery and what it supplies

- `SquareKit/Internal/PathTransport/TwoFamily.lean` defines `Family` as `StrictPseudofunctor Γ StrictTwoCategory`, `evaluation`, `Total`, `Hom`, `identity`, `compose`, `whiskerLeft`, `whiskerRight`, and exact action boundaries. Its hom category is `TwoGroupoidHom.Total (evaluation F x.fiber) y.fiber`.
- `TwoGroupoidHom.cell α ρ` takes `ρ : u ⟶ E.map α ≫ v`; this is an actual fiber 2-cell, not a host equation in the general API. `fiberCell`, `reindex`, `reindex_comp`, `inverse`, `inverse_comp`, `comp_inverse`, and `totalIsGroupoid` preserve or operate on that complete data.
- `TwoFamilyCoherence.totalBicategory` and `totalStrict` already make these cells actual total 2-cells, with derived whiskering, interchange, triangle, and pentagon. `TwoFamilyHigher.projectionHigher` maps the total cell to its base component; `totalLocallyGroupoid` derives vertical invertibility. These results remove a potential foundational prerequisite.
- `Examples.TwoFamily.pathFamily`, `arrow`, `cell`, `retains_nonzero_action`, `compose_integers`, `right_whisker_retains_base`, and `left_whisker_retains_base` are the existing integer specialization. `Examples.TwoGroupoidHom.pathCellDecode`, its two roundtrips, and `integerAction_evaluation` establish the connection between the concrete forced-boundary model and the general hom construction. A finite specialization should follow this pattern.
- `Examples.TwoGroupoidHom.fiberLoop`, `fiberLoop_detect`, and `fiber_one_ne_zero`, and `Examples.TwoFamilyCoherence.cell`/`nontrivial_fiber`, separately test a nonzero fiber component. They should remain separate retained controls; a product with one of these examples does not by itself prove that a new action depends on the cell.
- `TwoFamilySigmaRegroupHigher.sigmaRegroup` and `sigmaUngroup` are genuine strict higher functors with inverse laws. `sigmaRegroup_projection`, `sigmaUngroup_first`, and `sigmaUngroup_projection` retain the projections. `TwoFamilySigmaRegroupCell_fiber_heq`, `sigmaRegroupCell_comp`, `sigmaRegroupCell_whiskerLeft`, and `sigmaRegroupCell_whiskerRight` retain cell data. `Examples.TwoFamilySigmaRegroup` checks these on independently selected integer components. This proves that general dependent regrouping machinery exists; it does not identify sigma regrouping with a comma correspondence associator.
- The delivered `SquareKit.GroupoidCorrespondence` has `Boundary`, `Left`, `Right`, `reassociate`, selected units, and `changeBoundary`/`changeLeft`/`changeRight`. Here the two comma inputs in `Boundary` are discrete points. `commaIsDiscrete` therefore makes that comma category discrete even though its object has an observable boundary label. The existing normal forms `G × Bool` and their `discreteEquivalence` cannot be applied to the new non-discrete hom apex.
- `Examples.SecondIdentity.Bit`, `Label`, `encode`, and `observation_encode` provide the finite representations and observation. `DoubleDelooping.map_vertical`/`map_horizontal` prove the necessary algebraic preservation, but the inspected `DoubleDelooping.lean` does not package this as the particular strict higher functor needed below.

These are source inspections. No claim that the proposed finite declarations already exist follows from their integer analogues.

## Finite dependent family and exact selected cell

Use `G = Examples.SecondIdentity.Bit` and `H = Examples.SecondIdentity.Label`, both commutative groups in `Type 0`. Write `1` for the group identity, and `ε` for the nonidentity element. In additive labels these are `0` and `1`; in Boolean labels they are `false` and `true`.

Construct `F_G : TwoFamily.Family (DoubleDelooping.Space G)` with constant fiber `LocallyDiscrete (SingleObj G)`. Its unique base 1-arrow acts by the identity strict functor. A base 2-cell `a : G` acts by the strict transformation whose component is the fiber 1-arrow `Discrete.mk a`. Commutativity proves naturality; multiplication proves vertical and horizontal compatibility. This is the finite counterpart of `Examples.TwoFamily.pathFamily`, not a constant family whose 2-cell action is erased.

Let `x_G : TwoFamily.Total F_G` be the unique selected total object. Its total 1-arrows `p_G(m) : x_G ⟶ x_G` have unique base arrow and fiber arrow `Discrete.mk m`. An actual total 2-cell `c : p_G(m) ⟶ p_G(n)` has

```text
c.base : G
c.fiber : Discrete.mk m ⟶ Discrete.mk (n * c.base).
```

The multiplication order is intentional: `SingleObj` composition of `a` then `n` is `n * a`. Decode the fiber component using `LocallyDiscrete.eq_of_hom` to obtain `m = n * c.base`. Conversely construct the actual `TwoGroupoidHom.cell` from `a` and that equation, and prove both encode/decode roundtrips.

The selected cell is

```text
δ_G : p_G(ε) ⟶ p_G(1)
δ_G.base = ε
δ_G.fiber : Discrete.mk ε ⟶ Discrete.mk (1 * ε).
```

It is a genuine 2-cell in `TwoFamily.Total F_G` by `totalBicategory`. Its nonzero action is detected by `(TwoFamily.projectionHigher F_G).map₂ δ_G = ε`. Its dependent boundary prevents replacing the base component with `1` while retaining its two total-arrow endpoints.

Define the **actual hom-groupoid**

```text
K_G := (x_G ⟶ x_G)
π_G : K_G ⥤ SingleObj G :=
  (TwoFamily.projectionHigher F_G).mapFunctor x_G x_G.
```

`K_G`'s objects are total 1-arrows; its morphisms are the same total 2-cells. Its groupoid structure comes from the existing locally groupoid theorem. No separate manually labeled category is substituted. In particular `π_G.map δ_G = ε` is an evaluation of the actual higher projection.

## Correspondences and the two bracketings

Use the exact chain

```text
Point ← Point → SingleObj G
SingleObj G ←π_G K_G → Point
Point ← Discrete Bool → Point.
```

The first right leg is existing `GroupoidCorrespondence.point G`; every unnamed terminal leg uses existing `terminal`.

Define, for this selected shape,

```text
C_G := Comma (point G) π_G
T_G := Comma (terminal K_G) (terminal (Discrete Bool))
L_G := Comma (terminal C_G) (terminal (Discrete Bool))
R_G := Comma (point G) (Comma.fst (terminal K_G) (terminal (Discrete Bool)) ⋙ π_G).
```

The source and target of the selected `C_G` morphism are

```text
c₀ = (point, p_G(ε), boundary 1)
c₁ = (point, p_G(1), boundary ε).
```

Its left component is the point identity and its right component is exactly `δ_G`. Its comma square reads

```text
1 ≫ ε = 1 ≫ π_G.map δ_G,
```

or, after decoding `SingleObj`, `ε = ε * 1`. Thus the dependent 2-cell changes the actual comma boundary. It is not a detached observation appended to a #694 object.

For each Boolean `b`, let `l₀(b),l₁(b) : L_G` be the left-associated objects with `c₀,c₁` and third apex `b`. Construct

```text
χ_G(b) : l₀(b) ⟶ l₁(b)
χ_G(b).left.right = δ_G
χ_G(b).right = 𝟙 (Discrete.mk b).
```

The reassociation functor `A_G : L_G ⥤ R_G` sends

```text
((point,k,g), b, terminalBoundary) ↦ (point,(k,b,terminalBoundary),g)
((identity,δ),identity)             ↦ (identity,(δ,identity)).
```

Its inverse reverses these nesting operations. Prove functor laws, natural unit/counit, all object projections, and complete morphism roundtrips. The apex and terminal boundaries are uniquely determined where they should be, but `δ` is never replaced by a subsingleton witness before its typed endpoints and observation are retained. Reuse `Comma.equivProd` for `L_G` and `T_G` if that reduces definitions; an explicit selected reassociation is likely simpler than a generic theorem about arbitrary comma composition.

This is the precise dimension shift: `χ_G` is a **1-morphism of an ordinary comma groupoid**, and its stored `K_G` component is a **2-cell of the independently constructed total bicategory**. Define recovery functors/projections `recoverL := Comma.fst … ⋙ Comma.snd …` and `recoverR := Comma.snd … ⋙ Comma.fst …`, both landing in `K_G`, and prove

```text
recoverL.map χ_G(b) = δ_G
recoverR.map (A_G.map χ_G(b)) = δ_G.
```

These equations establish that correspondence composition carries the actual dependent 2-cell. They do not make the comma category a bicategory of higher correspondences.

## Representation change and exact route comparison

Use `e := Examples.SecondIdentity.encode : Bit ≃* Label`. Construct `J_e : K_G ⥤ K_H` on the existing total hom-categories by sending `p_G(m)` to `p_H(e m)` and sending an actual cell with component `a` to the actual cell with component `e a`. The fiber boundary follows from

```text
m = n*a  ⇒  e m = e n * e a.
```

Do not stop at a functor on a manually duplicated finite `Cell` record. Either construct a finite strict higher map `U_e : TwoFamily.Total F_G → TwoFamily.Total F_H` and identify `J_e` with its `mapFunctor`, or give checked encode/decode equations showing `J_e.map` acts on the original `TwoGroupoidHom.cell`, including the original fiber witness after endpoint conversion. The former also exercises existing total whiskering coherence; the latter is the minimum connection required for this finite hom-category experiment.

The base comparison is the existing `GroupoidCorrespondence.groupEquivalence e`. Prove the functor square `J_e ⋙ π_H ≅ π_G ⋙ (groupEquivalence e).functor`, with its component and map equations. On the finite selected skeleton the object alignments are canonical identity arrows. Use the actual square, `Comma.post`/`Comma.map`, and point alignment to define independent representation functors `Mᴸ_e : L_G ⥤ L_H` and `Mᴿ_e : R_G ⥤ R_H`. Both map the boundary by `e`, the middle apex by `J_e`, and the Boolean identically.

The two routes are

```text
P := Mᴸ_e ⋙ A_H : L_G ⥤ R_H
Q := A_G ⋙ Mᴿ_e : L_G ⥤ R_H.
```

Prove `η : P ≅ Q` with explicit object components, and its actual naturality equation at `χ_G(b)`:

```text
P.map χ_G(b) ≫ η.hom.app l₁(b)
  = η.hom.app l₀(b) ≫ Q.map χ_G(b).
```

This is equality of entire comma morphisms after their displayed endpoint identifications. On the chosen coordinate constructions `η` can be built from the equality of whole output objects, and both recovered `K_H` morphisms must equal `J_e.map δ_G = δ_H`. Prove the resulting observation is `labelObservation ε = 1` and retain the two changed boundary objects and Boolean apex. Require arrow roundtrip under `e.symm`, not merely object roundtrip.

#694 chooses its right representation by conjugating the left representation through reassociation. That was its stated contract. Here define `Mᴿ_e` independently by mapping its `K_G` and boundary fields. Otherwise the higher route square would mainly restate a conjugate definition and would not test the direct map on the dependent cell. The finite equations make this stronger test practical without claiming comparison of arbitrary independently supplied interpretations.

## Erasure test and what it does not prove

In each representation prove

```text
¬ ∃ c : p_G(ε) ⟶ p_G(1), c.base = 1.
```

Decoding the actual fiber boundary yields `ε = 1*1`, a contradiction. Consequently there is no comma morphism `c₀ ⟶ c₁` having a right component whose base observation is zero. Its comma equation independently fails when the same boundary objects are held fixed. Run this rejection after `A_G`, after `Mᴸ_e`, and after the two routes, by the recovery equations. This is a fixed-boundary rejection, not an assertion that a typed forgetful functor can send this cell to a zero cell with unchanged endpoints.

The selected `K_G` is thin: its boundary determines `a = n⁻¹*m`. Therefore the endpoints themselves determine the cell's observation. Do **not** claim an impossibility theorem saying no observer can reconstruct `a` from those endpoints. That would be false here. #694's loss of independently chosen boundary labels and `SecondIdentity.no_groupoid_observation` remain separate information-loss controls at their stated dimensions.

A replacement that collapses both total-arrow endpoints can send this cell to an identity; that changes the endpoint observation as well. A product with a constant independent fiber loop could exhibit a further loss with fixed endpoints, but would not improve the evidence for nontrivial dependent action. The present experiment targets dependence through the forced boundary.

## Declaration plan, supplied laws, and checked applications

Proposed finite declarations can live in a small reusable finite-family module and a correspondence client module. Names below are proposed, except where qualified as existing.

1. `commutativePathFamily`, `pathArrow`, `pathCell`, `pathCellDecode`, their two roundtrips, and `pathProjection`. Parameterizing by `CommGroup G` is a modest generalization of the existing integer proof, but fixed `Bit`/`Label` implementations are acceptable if universes or elaboration obscure the finite result. Expose `map₂` action and its laws. The finite theorem must instantiate both representations.
2. `selectedCell`, `selectedCell_projection`, `reject_erased_component`. These must be stated in the actual `TwoFamily.Hom` type. Use `TwoFamilyCoherence.totalBicategory`, `TwoFamilyHigher.projectionHigher`, and `TwoGroupoidHom.totalIsGroupoid` rather than new bicategory or groupoid cores.
3. Selected `BoundaryOf`, `LeftOf`, `RightOf` taking `π : K ⥤ SingleObj G`, with the above chain; `reassociateOf` and inverse, object and morphism projection/recovery. This can be kept local to the client until a second use warrants a public general interface. If exported generically, prove its functor and natural equivalence laws for arbitrary `K,π`; no arbitrary-span pentagon follows.
4. `changePathHom`, its inverse and dependent boundary/map preservation; the base representation square; independently defined `changeLeftOf`/`changeRightOf`; `representationReassociateIsoOf` with whole-morphism naturality and explicit selected component recovery.
5. Public applications for both `b=false,true`, the selected nonzero cell, its inverse/vertical cancellation, both bracketings, both representation routes, full inverse recovery, and zero-component rejection. A selected left/right whiskering test in the total bicategory should recover the same nonzero projected action through the existing `whiskerLeft`/`whiskerRight`; it is a useful check that the finite family really implements the existing higher API.
6. Specialize `K=Point`, `π=point G` to recover #694's selected `Boundary`, `Left`, `Right`, object and morphism projections. Use the existing #694 code as the baseline, rather than deleting it. Specialize to discrete cospans via existing `discretePullback` and `discretePullback_encode` for the ordinary bridge.

Supplied data are the commutative group operations/laws, actual finite representation equivalence, the selected elements/Boolean, and the strict family construction's primitive map actions. Derived laws include the family naturality and functoriality, total bicategory and locally groupoid structure, comma groupoid laws, reassociation inverse laws, representation naturality, dependent recovery and erasure rejection. Do not accept the final route comparison, projected observation or erased-component rejection as caller-supplied fields.

There are two explicit restrictions. The fiber `LocallyDiscrete (SingleObj G)` has no nontrivial parallel fiber 2-cells; the dependent total cells are nevertheless present through their base action and have different total-arrow endpoints. The correspondence composition is the selected three-leg comma shape, not a general bicategory of correspondences with arbitrary higher transformations.

At the generic source level `TwoFamily` keeps separate base and fiber object/arrow/cell universes; its total levels use their maxima. The chosen finite group carriers and hom data use level zero. The classifier `StrictTwoCategory` is a universe-level packaging of these fibers, not evidence that every classifier object is finite. The new finite theorem should state its universe parameters explicitly and check that the comma apex is the intended hom-category, avoiding inference of an unintended locally discrete instance.

## Ordinary specialization and retained assumptions

The new selected comma functor is ordinary category theory on an apex that happens to be a total hom-groupoid. It neither replaces nor strengthens the hypotheses of `SpanAction` or `SpanInterpretation`.

Retain the checked #694 public applications `Examples.GroupoidCorrespondence.Ordinary.two_chosen`, `three_chosen`, `compositor_on_comma`, `Native.selected_recovery`, and `Interpreted.output_recovery`. They connect to Mathlib's chosen pullback and `IndexedSumBaseChange.encode`. Ordinary `SpanAction` assumes only pullbacks; `SpanInterpretation` assumes preservation of pullbacks (`WalkingCospan`), and #633's composition modifications and associativity/unit laws remain complete. The existing `Examples.SpanAction.collapse` is noninvertible and must remain admitted. `Examples.MatesBaseChange.forget_not_leftExact` and `Examples.SpanInterpretation.truncation_not_preserving` remain required hypothesis controls.

No finite-limit preservation, exceptional operation, motivic model, or reinterpretation of ordinary equality is needed. The locally discrete specialization of the new **higher** family removes its nonzero-cell test, while the existing **ordinary** API still allows arbitrary apex maps; these are different restrictions and must not be conflated.

## Alternatives and smallest discriminating test

A generic higher comma construction would carry dependent 2-cells as higher morphisms without the hom-category dimension shift. It would require specifying higher comma objects/arrows/cells and their coherent boundaries, an interface not supplied by the inspected #694 code. `sigmaRegroup` offers reusable strict dependent-pair coherence, but a theorem identifying that regrouping with such a comma construction is still missing. Proposing a new higher core before this selected test would add obligations without improving its finite observation.

The smallest discriminator is to implement `F_Bit`, `δ_Bit`, and the non-discrete comma morphism `(identity,δ_Bit) : c₀ ⟶ c₁`, then prove its projected base is the nonidentity bit and its zero-base replacement is uninhabited. If that succeeds, the remaining two nesting maps and representation maps have explicit coordinate definitions. If an encoding problem appears, retain that exact judgment and source in a bounded scratch probe; a resource failure is not evidence against the paper construction.

The principal remaining implementation risk is dependent endpoint transport in a representation functor between the actual `TwoFamily.Hom` types, especially when identifying it with a strict total higher functor. The encode/decode roundtrips provide a smaller proof boundary without weakening the retained cell. The first implementation child can require those actual-type roundtrips and add the strict-total representation packaging when straightforward; it must not silently replace the higher data with an unrelated group label.

I recommend a ready child for this finite hom-apex experiment with those explicit limits, rather than a new foundational prerequisite. Its validation should include the checked public applications and repository build/audit requirements, with independent statement review of the cell dimension, the forced boundary, the two entire route morphisms, and the ordinary controls. Completion establishes this selected connected dependent-cell checkpoint; it does not claim a general higher correspondence interpretation.

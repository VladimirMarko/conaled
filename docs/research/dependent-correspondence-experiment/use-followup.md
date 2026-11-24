# #698 implementation/use follow-up

The mod-two/mod-four proposal in `alternatives.md` is a feasible bounded replacement for my initial thin control, subject to proving the concrete finite admission. It makes a stronger test: two different dependent 2-cells retain the same endpoints and the same nonzero base action. The thin example need not be an implementation prerequisite. Neither construction calls for a general higher correspondence core.

This is the requested cross-exposed follow-up. I read the alternatives report after saving `use.md`; that initial report remains unchanged. My prior exposure includes authoring the #697 use assessment and the #694 discrete bridge audit. I inspected the actual `TwoFamily`, `TwoGroupoidHom`, `StrictTwoTransformation`, `TwoFamilyMap`, `GroupoidCorrespondence`, and `SecondIdentity` declarations at the pinned source `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`. I ran no Lean probe or build. The new construction below is assessed from source and finite arithmetic, not claimed as an elaborated instance.

## Concrete admission fits the existing interface

Take `Q = ZMod 2`, `R = ZMod 4`. Mathlib already supplies `ZMod.castHom`; its additive-hom projection supplies reduction `π : R →+ Q`, using the proof that 2 divides 4. A new generic quotient or crossed-module interface would add no capability needed by this client.

For the proposed one-object fiber K, use 1-arrows `m : Q` and actual 2-cell types

```text
FiberCell m n = { r : R // m = n + π r }.
```

Vertical composition adds labels; left and right whiskering leave the R label unchanged. The latter facts are essential: horizontal composition then adds labels, and interchange is commutativity in R. Identity labels are zero, inverse labels are negatives. The boundary for an inverse follows by moving `π r` across the original equation. These definitions provide the individual hom groupoids and a strict bicategory with 1-arrow composition addition in Q. They also provide the ordinary one-object category required by the bicategory carrier.

The proof interface should expose at least label extensionality, identity/composition/inverse label equations, left/right whiskering label equations, and `label_eqToHom = 0`. These are proposed declarations, not existing repository names. `label_eqToHom` follows by equality elimination and the identity definition. It is the useful normalization lemma for the strict coherence and family-action proofs. One must not assign `Subsingleton (FiberCell m n)`: for example the labels 0 and 2 give different endomorphism 2-cells of each m.

For base `DoubleDelooping.Space (Multiplicative Q)`, the proposed family maps its sole base 1-arrow to the identity strict functor of K. A base 2-cell α acts by `StrictTwoTransformation.Trans` whose component is the fiber 1-arrow `Multiplicative.toAdd α`. The actual structure has three fields:

- `app`, the component 1-arrow;
- `naturality`, equality of the two composites of 1-arrows;
- `naturality₂`, equality of the corresponding transported 2-cells.

The first naturality is commutativity in Q. For a fiber cell with label r, both sides of `naturality₂` have label r: whiskering retains r and each `eqToHom` contributes zero. Label extensionality proves the law. This checks the actual interface obligation that a family storing only an α-component could otherwise overlook. `Trans.ext` can prove identities/composition of the resulting transformations from their components; it does not erase K's parallel 2-cells.

The remaining `StrictPseudofunctor` identity, composition and whiskering laws are finite additive identities and identity-functor equalities. They require proofs in the existing strict interface. No desired dependent recovery or reassociation theorem should appear as an assumed field. I see no contradictory judgment or extra cell level in this admission. Its Lean proof effort is unmeasured.

## Admission must end in actual total cells

`TwoFamily.evaluation` evaluates the action above at the unique fiber object. `TwoGroupoidHom.cell` consequently accepts α together with a genuine fiber cell

```text
ρ : m ⇒ α + n.
```

Its label r satisfies `m = α + n + π r`, equivalently the alternatives report's `m = n + α + π r`. The harmless commutativity conversion must be present in the decoder; the printed normal form should not be mistaken for a definitional equation.

Use `TwoFamily.Hom F x x` itself as H. Prove an equivalence between its objects and Q and, for chosen objects m,n, between its arrows and

```text
D m n = { (α : Q, r : R) // m = n + α + π r }.
```

The bridge must recover complete actual cells in both directions. Equality of proof fields is harmless; equality of the retained α and r coordinates is substantive. `TwoFamily.totalLocallyGroupoid` in `TwoFamilyHigher.lean` supplies the local groupoid once K's hom groupoids are installed. Thus H is the needed groupoid without new total-category machinery.

At m=n=0, `d₁=(1,1)` and `d₃=(1,3)` satisfy the boundary. Their images in H must be distinct. The erasure function to `(m,n,α)` takes equal values on them, while the independent observation `r.val` takes 1 and 3. This proves no decoder from that erased input can recover both complete cells, or even both observations. Replacing either r by zero while retaining α=1 fails its boundary. These are separate, valid tests: a failure of typing and a loss of information.

For the thin path-family model, fixed endpoints determine α. It cannot support this same erasure theorem. My initial recommendation was therefore the smallest nonzero-action test, not a necessary prerequisite or an equally strong substitute for this parallel-witness test.

## Correspondence routes and representation change

The proposed point-selection chain is sufficient. For `p₀ : Point ⥤ H` selecting total arrow 0, use the three spans and actual nested comma types from `alternatives.md`. `GroupoidCorrespondence.commaIsDiscrete` needs discrete source categories, not a discrete target H. It therefore applies to `Comma p₀ p₀`; the other required comma categories are discrete as well. The complete normal form for either bracketing is `D 0 0 × Bool`.

`GroupoidCorrespondence.discreteEquivalence` then lifts complete object equivalences to categorical equivalences. The existing concrete `Boundary`, `Left`, `Right`, and `groupEquivalence` specialize to `SingleObj G`; they do not accept H directly. A bounded chosen-object variant or local finite definitions are appropriate. Generalizing the established chosen-point pattern to `p : Point ⥤ H` is enough. The finite construction fits Type 0 throughout; the existing `commaIsDiscrete` and `discreteEquivalence` already permit separate object and hom universes. No common-universe restriction on the broader ordinary interface follows from this finite client.

Whole recovery means the original H-arrow, hence its α and r, and the Bool branch survive forward and inverse maps. Require both roundtrips on arbitrary complete comma objects, then selected checks for both `(d₁,false)` and `(d₃,false)` through both bracketings. A natural comparison on its own is too weak as an acceptance description unless the component equation is tied to this decoder. Its discreteness proof may use proof irrelevance for actual comma morphisms; it may not use proof irrelevance to identify their distinct object-boundary H-arrows.

The representation change needs slightly more specification than “apply encode.” `SecondIdentity.encode : Bit ≃* Label` has `Label = Multiplicative (ZMod 2)`. An additive Q coordinate is `Multiplicative.toAdd (encode b)`. Keep R fixed; map the m,n,α coordinates by this existing equivalence and preserve r exactly. Define and verify the representation of K's composition, whiskering and transformation action before claiming a map of actual families or total cells.

`TwoFamily.StrongMap.toHigher` is for families over the same base Γ. It does not directly supply the cross-base map between the Bit and Label double deloopings. A route using this API needs the base strict functor, `TwoFamily.reindex`, and compatible family data. A direct finite functor between the actual hom-groupoids, with explicit complete-cell inverse laws and action compatibility, is a smaller sufficient route for this selected comma experiment. Neither route should be described as already supplied by `SecondIdentity.encode` alone.

Prefer defining both left and right representation functors from the coordinate map, with the necessary point alignment, then prove their reassociation comparison. This is a finite calculation because all retained fields are displayed. A right representation functor defined by conjugation is possible, but only proves the deliberately weaker constructed comparison; it does not test independently specified right-hand interpretation. The selected child can choose the stronger direct pair without a new general API.

The proposed whiskering check is useful and connected. Apply actual `TwoFamily.whiskerLeft` or `TwoFamily.whiskerRight` to d₁ and the total 1-arrow with fiber coordinate 1. Both endpoints become 1, and α=1,r=1 remain. Run this resulting cell through the point-selection chain using `p₁`, not `p₀`, and require representation compatibility. This checks action on the actual total cells before using their hom-groupoid as the correspondence target.

## Scope and acceptance

The bounded child can implement K and its family, the complete-cell bridge, the two parallel selected cells, the representation map, and the finite chosen-point comma comparison together. If admission fails, report the exact failed obligation and isolate that finite admission. There is no basis in this audit for making the thin example mandatory, broadening to a general higher comma construction, or classifying an elaboration failure as mathematical impossibility.

Concrete acceptance should require:

1. Actual K strictness/local groupoid instances and actual `TwoFamily.Family` admission, including `naturality₂` without a false fiber-cell subsingleton instance.
2. Both complete-cell bridge roundtrips, d₁/d₃ separation, the fixed-boundary zero-replacement rejection, and the no-reconstruction theorem for the erased `(m,n,α)` coordinates.
3. Both actual threefold comma bracketings with complete arbitrary-object roundtrips and selected d₁/d₃ plus Bool recovery.
4. The Bit/Label cell map preserving r, its inverse laws and family-action compatibility, plus the two representation/reassociation routes under an explicit choice of direct or conjugated right map.
5. The actual whiskering calculation and its recovery through the correctly selected p₁ chain.
6. Ordinary discrete recovery and the existing ordinary consumers under their original assumptions.

For the last item reuse `GroupoidCorrespondence.discretePullback`, `discretePullback_encode`, and `discretePullback_roundtrip`, with #694's `Examples.GroupoidCorrespondence.Ordinary.two_chosen`, `three_chosen`, and `compositor_on_comma`, native `input_recovery`/`selected_recovery`, and interpreted `output_recovery`. Do not require groupoidal ordinary apex maps, preservation of all finite limits, or additional finiteness assumptions. #633's `SpanAction` needs its original pullbacks; `SpanInterpretation` needs its stated pullback-diagram preservation. The new finite higher example does not replace that general ordinary theorem or strengthen its hypotheses.

One source-name correction to my initial report: the existing theorem is `TwoFamily.sigmaRegroupCell_fiber_heq`; the isolated spelling `TwoFamilySigmaRegroupCell_fiber_heq` in that report is not a declaration. The sigma regrouping APIs remain useful evidence that complete dependent cells survive strict maps, but they are not the selected comma associator without a proved bridge.

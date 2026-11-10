import SquareKit.SmoothQuotientGeneratedMatching
import SquareKit.Internal.PathTransport.CechMatchingCanonical
import SquareKit.SheafCoverCech

/-! Independently supplied generated matching data on an arbitrary original
cover, compared with its split-display presentation. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SmoothOpenSite
open SheafActionQuotient (Action)
open Internal.PathTransport GroupoidModel Comparison
open SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (f : Y ⟶ X)

/-- The input diagram uses the actual original cover and its categorical
pullbacks. No global object or split matching datum is supplied. -/
def strictDiagram : CechMatching.StrictDiagram.{1} where
  localCategory := context a hΓ Y
  doubleCategory := context a hΓ (SheafCoverCech.double f)
  tripleCategory := context a hΓ (SheafCoverCech.triple f)
  first := restriction a hΓ (SheafCoverCech.first f)
  second := restriction a hΓ (SheafCoverCech.second f)
  diagonal := restriction a hΓ (SheafCoverCech.diagonal f)
  firstSecond := restriction a hΓ (SheafCoverCech.firstSecond f)
  firstThird := restriction a hΓ (SheafCoverCech.firstThird f)
  secondThird := restriction a hΓ (SheafCoverCech.secondThird f)
  diagonalFirst := by
    rw [restriction_comp, SheafCoverCech.diagonal_first, restriction_id]
  diagonalSecond := by
    rw [restriction_comp, SheafCoverCech.diagonal_second, restriction_id]
  tripleFirst := by
    rw [restriction_comp, restriction_comp, SheafCoverCech.firstThird_first]
  tripleMiddle := by
    rw [restriction_comp, restriction_comp, SheafCoverCech.secondThird_first]
  tripleLast := by
    rw [restriction_comp, restriction_comp, SheafCoverCech.firstThird_second,
      SheafCoverCech.secondThird_second]

abbrev Datum := CechMatching.Datum (strictDiagram a hΓ f).toDiagram

theorem restrictionOverlap_eq :
    restriction a hΓ f ⋙ (strictDiagram a hΓ f).first =
      restriction a hΓ f ⋙ (strictDiagram a hΓ f).second := by
  change restriction a hΓ f ⋙ restriction a hΓ _ = restriction a hΓ f ⋙ restriction a hΓ _
  rw [restriction_comp, restriction_comp]
  exact congrArg (restriction a hΓ) Limits.pullback.condition

/-- The original global-to-local functor uses actual restriction along f. -/
def restrictionFunctor : context a hΓ X ⥤ Datum a hΓ f :=
  (strictDiagram a hΓ f).equalFunctor (restriction a hΓ f) (restrictionOverlap_eq a hΓ f)

/-- Transfer uses restriction along the three actual cover isomorphisms. -/
def toSplitMap : CechMatching.StrictMap (strictDiagram a hΓ f)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f)) where
  localMap := restriction a hΓ (SplitSheaf.displayIso f).hom
  doubleMap := restriction a hΓ (SheafCoverCech.splitDoubleIso f).hom
  tripleMap := restriction a hΓ (SheafCoverCech.splitTripleIso f).hom
  first := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitDouble_first]
  second := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitDouble_second]
  diagonal := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitDouble_diagonal]
  firstSecond := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitTriple_firstSecond]
  firstThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitTriple_firstThird]
  secondThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.splitTriple_secondThird]

private theorem inverse_square {A B A' B' : Sheaf topology Type}
    (e : A ≅ A') (i : B ≅ B') (p : A ⟶ B) (q : A' ⟶ B')
    (h : e.hom ≫ q = p ≫ i.hom) : e.inv ≫ p = q ≫ i.inv := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp, ← Category.assoc,
    h, Category.assoc, i.hom_inv_id, Category.comp_id]

def fromSplitMap : CechMatching.StrictMap
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f))
    (strictDiagram a hΓ f) where
  localMap := restriction a hΓ (SplitSheaf.displayIso f).inv
  doubleMap := restriction a hΓ (SheafCoverCech.splitDoubleIso f).inv
  tripleMap := restriction a hΓ (SheafCoverCech.splitTripleIso f).inv
  first := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SheafCoverCech.splitDoubleIso f) (SplitSheaf.displayIso f) _ _ (SheafCoverCech.splitDouble_first f)).symm
  second := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SheafCoverCech.splitDoubleIso f) (SplitSheaf.displayIso f) _ _ (SheafCoverCech.splitDouble_second f)).symm
  diagonal := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SplitSheaf.displayIso f) (SheafCoverCech.splitDoubleIso f) _ _ (SheafCoverCech.splitDouble_diagonal f).symm).symm
  firstSecond := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SheafCoverCech.splitTripleIso f) (SheafCoverCech.splitDoubleIso f) _ _ (SheafCoverCech.splitTriple_firstSecond f)).symm
  firstThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SheafCoverCech.splitTripleIso f) (SheafCoverCech.splitDoubleIso f) _ _ (SheafCoverCech.splitTriple_firstThird f)).symm
  secondThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ =
      restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp]
    exact congrArg (restriction a hΓ)
      (inverse_square (SheafCoverCech.splitTripleIso f) (SheafCoverCech.splitDoubleIso f) _ _ (SheafCoverCech.splitTriple_secondThird f)).symm

theorem toSplit_fromSplit : (toSplitMap a hΓ f).comp (fromSplitMap a hΓ f) =
    CechMatching.StrictMap.id (strictDiagram a hΓ f) := by
  apply CechMatching.StrictMap.ext
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.inv_hom_id, restriction_id]
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.inv_hom_id, restriction_id]
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.inv_hom_id, restriction_id]

theorem fromSplit_toSplit : (fromSplitMap a hΓ f).comp (toSplitMap a hΓ f) =
    CechMatching.StrictMap.id
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f)) := by
  apply CechMatching.StrictMap.ext
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.hom_inv_id, restriction_id]
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.hom_inv_id, restriction_id]
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = 𝟭 _
    rw [restriction_comp, Iso.hom_inv_id, restriction_id]

/-- Original and split matching data are equivalent on objects, actual overlap
isomorphisms and selected local arrows, for every supported generated context. -/
def matchingEquivalence : Datum a hΓ f ≌
    SmoothQuotientGeneratedMatching.Datum a hΓ (SplitSheaf.ofDisplay f) :=
  CechMatching.StrictMap.equivalence (toSplitMap a hΓ f) (fromSplitMap a hΓ f)
    (toSplit_fromSplit a hΓ f) (fromSplit_toSplit a hΓ f)

/-- The canonical global restriction commutes with the presentation change,
including its overlap and selected local arrows. -/
theorem restriction_toSplit : restrictionFunctor a hΓ f ⋙ (matchingEquivalence a hΓ f).functor =
    SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ (SplitSheaf.ofDisplay f) := by
  have hl : restriction a hΓ f ⋙ (toSplitMap a hΓ f).localMap =
      restriction a hΓ (SplitSheaf.p (SplitSheaf.ofDisplay f)) := by
    change restriction a hΓ f ⋙ restriction a hΓ _ = _
    rw [restriction_comp, SplitSheaf.displayIso_projection]
  have he : (restriction a hΓ f ⋙ (toSplitMap a hΓ f).localMap) ⋙
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f)).first =
    (restriction a hΓ f ⋙ (toSplitMap a hΓ f).localMap) ⋙
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f)).second := by
    rw [hl]
    exact SmoothQuotientGeneratedMatching.restrictionOverlap_eq a hΓ (SplitSheaf.ofDisplay f)
  have h := (toSplitMap a hΓ f).equalFunctor_map (restriction a hΓ f)
    (restrictionOverlap_eq a hΓ f) he
  simpa only [hl, restrictionFunctor, matchingEquivalence,
    CechMatching.StrictMap.equivalence, SmoothQuotientGeneratedMatching.restrictionFunctor] using h

end SquareKit.SmoothQuotientCoverMatching

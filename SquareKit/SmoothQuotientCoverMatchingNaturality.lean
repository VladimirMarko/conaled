import SquareKit.SmoothQuotientCoverMatching
import SquareKit.SheafCoverCechMaps
import SquareKit.SmoothQuotientCoverSections

/-! Original-cover generated matching data is natural under parameter squares,
with identity and composition laws on the complete matching functors. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SmoothOpenSite
open SheafActionQuotient (Action)
open Internal.PathTransport GroupoidModel Comparison
open SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y X' Y' : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable {f : Y ⟶ X} {k : Y' ⟶ X'}
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

def squareMap : CechMatching.StrictMap (strictDiagram a hΓ f) (strictDiagram a hΓ k) where
  localMap := restriction a hΓ v
  doubleMap := restriction a hΓ (SheafCoverCech.mapDouble u v square)
  tripleMap := restriction a hΓ (SheafCoverCech.mapTriple u v square)
  first := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapDouble_first]
  second := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapDouble_second]
  diagonal := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapDouble_diagonal]
  firstSecond := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapTriple_firstSecond]
  firstThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapTriple_firstThird]
  secondThird := by
    change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _ ⋙ restriction a hΓ _
    rw [restriction_comp, restriction_comp, SheafCoverCech.mapTriple_secondThird]

/-- Arbitrary cover squares transfer independently supplied matching data. -/
def squareFunctor : Datum a hΓ f ⥤ Datum a hΓ k := (squareMap a hΓ u v square).functor

theorem squareMap_id : squareMap a hΓ (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) =
    CechMatching.StrictMap.id (strictDiagram a hΓ f) := by
  apply CechMatching.StrictMap.ext
  · exact restriction_id a hΓ Y
  · change restriction a hΓ _ = 𝟭 _
    rw [SheafCoverCech.mapDouble_id, restriction_id]
  · change restriction a hΓ _ = 𝟭 _
    rw [SheafCoverCech.mapTriple_id, restriction_id]

variable {X'' Y'' : Sheaf topology Type} {l : Y'' ⟶ X''}
variable (u' : X'' ⟶ X') (v' : Y'' ⟶ Y') (square' : v' ≫ k = l ≫ u')

theorem squareMap_comp : (squareMap a hΓ u v square).comp (squareMap a hΓ u' v' square') =
    squareMap a hΓ (u' ≫ u) (v' ≫ v) (by
      rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  apply CechMatching.StrictMap.ext
  · exact restriction_comp a hΓ v v'
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _
    rw [restriction_comp, SheafCoverCech.mapDouble_comp]
  · change restriction a hΓ _ ⋙ restriction a hΓ _ = restriction a hΓ _
    rw [restriction_comp, SheafCoverCech.mapTriple_comp]

theorem squareFunctor_id : squareFunctor a hΓ (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) =
    𝟭 (Datum a hΓ f) := by
  unfold squareFunctor
  rw [squareMap_id, CechMatching.StrictMap.functor_id]

theorem squareFunctor_comp : squareFunctor a hΓ u v square ⋙ squareFunctor a hΓ u' v' square' =
    squareFunctor a hΓ (u' ≫ u) (v' ≫ v) (by
      rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  unfold squareFunctor
  rw [← CechMatching.StrictMap.functor_comp, squareMap_comp]

/-- The selected split square is the conjugate of the actual original square
through the checked presentation isomorphisms at all three overlap levels. -/
def splitSquareMap : CechMatching.StrictMap
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay f))
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ (SplitSheaf.ofDisplay k)) :=
  (fromSplitMap a hΓ f).comp ((squareMap a hΓ u v square).comp (toSplitMap a hΓ k))

/-- This is the same local cover map used by parameter-compatible sections. -/
theorem splitSquareMap_local : (splitSquareMap a hΓ u v square).localMap =
    restriction a hΓ (SmoothQuotientDeformations.CoverSectionFamily.splitSquareMap
      (f := f) (k := k) v) := by
  change restriction a hΓ _ ⋙ (restriction a hΓ _ ⋙ restriction a hΓ _) = _
  rw [← Functor.assoc, restriction_comp, restriction_comp]
  rfl

theorem toSplit_square : (toSplitMap a hΓ f).comp (splitSquareMap a hΓ u v square) =
    (squareMap a hΓ u v square).comp (toSplitMap a hΓ k) := by
  change (toSplitMap a hΓ f).comp ((fromSplitMap a hΓ f).comp _) = _
  have h : (toSplitMap a hΓ f).comp
      ((fromSplitMap a hΓ f).comp ((squareMap a hΓ u v square).comp (toSplitMap a hΓ k))) =
    ((toSplitMap a hΓ f).comp (fromSplitMap a hΓ f)).comp
      ((squareMap a hΓ u v square).comp (toSplitMap a hΓ k)) := by
    apply CechMatching.StrictMap.ext <;> rfl
  rw [h, toSplit_fromSplit]
  apply CechMatching.StrictMap.ext <;> rfl

/-- Original-to-split matching equivalences commute with arbitrary parameter
squares as complete functors on objects, overlaps and arrows. -/
theorem matchingEquivalence_natural :
    (matchingEquivalence a hΓ f).functor ⋙ (splitSquareMap a hΓ u v square).functor =
      squareFunctor a hΓ u v square ⋙ (matchingEquivalence a hΓ k).functor := by
  change (toSplitMap a hΓ f).functor ⋙ (splitSquareMap a hΓ u v square).functor =
    (squareMap a hΓ u v square).functor ⋙ (toSplitMap a hΓ k).functor
  rw [← CechMatching.StrictMap.functor_comp, toSplit_square, CechMatching.StrictMap.functor_comp]

/-- Global restriction commutes with every original cover square, retaining
canonical overlap data and all local arrows. -/
theorem restriction_square :
    restrictionFunctor a hΓ f ⋙ squareFunctor a hΓ u v square =
      restriction a hΓ u ⋙ restrictionFunctor a hΓ k := by
  have hl : restriction a hΓ f ⋙ (squareMap a hΓ u v square).localMap =
      restriction a hΓ u ⋙ restriction a hΓ k := by
    change restriction a hΓ f ⋙ restriction a hΓ v = _
    rw [restriction_comp, restriction_comp, square]
  have he : (restriction a hΓ f ⋙ (squareMap a hΓ u v square).localMap) ⋙
      (strictDiagram a hΓ k).first =
      (restriction a hΓ f ⋙ (squareMap a hΓ u v square).localMap) ⋙
        (strictDiagram a hΓ k).second := by
    rw [hl, Functor.assoc, Functor.assoc, restrictionOverlap_eq]
  have hm := (squareMap a hΓ u v square).equalFunctor_map
    (restriction a hΓ f) (restrictionOverlap_eq a hΓ f) he
  change (strictDiagram a hΓ f).equalFunctor _ _ ⋙ (squareMap a hΓ u v square).functor = _
  rw [hm]
  simp only [hl]
  rfl

end SquareKit.SmoothQuotientCoverMatching

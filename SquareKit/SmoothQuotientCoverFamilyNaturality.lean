import SquareKit.SmoothQuotientCoverRelativeMatching
import SquareKit.SmoothQuotientCoverMatchingNaturality
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberMap

/-! Arbitrary cover squares act on independently specified relative matching
families, retaining total arrows and strict identity/composition coherence. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SmoothOpenSite SheafActionQuotient
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y X' Y' : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable {f : Y ⟶ X} {k : Y' ⟶ X'}
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

/-- The total family map is the actual extended-context parameter restriction. -/
def relativeSquareMap : CechMatching.StrictMap
    ((relativeFamilyData a hΓ hB f).total (relativeFamilyCoherence a hΓ hB f))
    ((relativeFamilyData a hΓ hB k).total (relativeFamilyCoherence a hΓ hB k)) :=
  ((relativeToGenerated a hΓ hB f).comp (squareMap a (.ext hΓ hB) u v square)).comp
    (generatedToRelative a hΓ hB k)

theorem relativeSquare_projection :
    (relativeSquareMap a hΓ hB u v square).comp
      ((relativeFamilyData a hΓ hB k).projection (relativeFamilyCoherence a hΓ hB k)) =
    ((relativeFamilyData a hΓ hB f).projection (relativeFamilyCoherence a hΓ hB f)).comp
      (squareMap a hΓ u v square) := by
  apply CechMatching.StrictMap.ext
  · change SmoothQuotientGeneratedMatching.restriction a (.ext hΓ hB) v ⋙
      Grothendieck.forget _ = Grothendieck.forget _ ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ v
    rw [SmoothQuotientGeneratedMatching.restriction_extend]
    rfl
  · change SmoothQuotientGeneratedMatching.restriction a (.ext hΓ hB) _ ⋙
      Grothendieck.forget _ = Grothendieck.forget _ ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ _
    rw [SmoothQuotientGeneratedMatching.restriction_extend]
    rfl
  · change SmoothQuotientGeneratedMatching.restriction a (.ext hΓ hB) _ ⋙
      Grothendieck.forget _ = Grothendieck.forget _ ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ _
    rw [SmoothQuotientGeneratedMatching.restriction_extend]
    rfl

def relativeSquareFunctor := (relativeSquareMap a hΓ hB u v square).functor

/-- Every independently supplied local total arrow is restricted as supplied. -/
theorem relativeSquareFunctor_localArrow {d e : CechMatching.Datum
    ((relativeFamilyData a hΓ hB f).total (relativeFamilyCoherence a hΓ hB f)).toDiagram}
    (p : d ⟶ e) :
    ((relativeSquareFunctor a hΓ hB u v square).map p).localArrow =
      (SmoothQuotientGeneratedMatching.restriction a (.ext hΓ hB) v).map p.localArrow := rfl

/-- The fixed-fiber map needs no invertibility of either cover-square map. -/
def familySquare (d : Datum a hΓ f) :
    (relativeMatchingFamily a hΓ hB f).obj d ⥤
      (relativeMatchingFamily a hΓ hB k).obj ((squareFunctor a hΓ u v square).obj d) :=
  CechMatching.Comprehension.fiberMap (squareMap a hΓ u v square)
    (relativeSquareMap a hΓ hB u v square) (relativeSquare_projection a hΓ hB u v square) d

/-- Extraction recovers the complete total square functor through selected
base-transport isomorphisms, including all matching arrows. -/
def familySquare_recovery (d : Datum a hΓ f) :
    familySquare a hΓ hB u v square d ⋙ CechMatching.Comprehension.Fiber.forget ≅
      CechMatching.Comprehension.Fiber.forget ⋙ relativeSquareFunctor a hΓ hB u v square :=
  CechMatching.Comprehension.fixedBaseComparison _ _ _ _ _

/-- Recovery commutes with every supplied vertical matching arrow. -/
theorem familySquare_arrow_recovery (d : Datum a hΓ f)
    {x y : (relativeMatchingFamily a hΓ hB f).obj d} (p : x ⟶ y) :
    ((familySquare a hΓ hB u v square d).map p).matchingArrow ≫
        (familySquare_recovery a hΓ hB u v square d).hom.app y =
      (familySquare_recovery a hΓ hB u v square d).hom.app x ≫
        (relativeSquareFunctor a hΓ hB u v square).map p.matchingArrow :=
  (familySquare_recovery a hΓ hB u v square d).hom.naturality p

/-- Relative reconstruction and the original extended-context cover map form
an exact square on complete matching functors. -/
theorem relativeMatchingEquivalence_square :
    (relativeMatchingEquivalence a hΓ hB f).functor ⋙
        squareFunctor a (.ext hΓ hB) u v square =
      relativeSquareFunctor a hΓ hB u v square ⋙
        (relativeMatchingEquivalence a hΓ hB k).functor := by
  change (relativeToGenerated a hΓ hB f).functor ⋙
      (squareMap a (.ext hΓ hB) u v square).functor =
    (relativeSquareMap a hΓ hB u v square).functor ⋙
      (relativeToGenerated a hΓ hB k).functor
  rw [← CechMatching.StrictMap.functor_comp, ← CechMatching.StrictMap.functor_comp]
  congr 1

theorem relativeSquareMap_id :
    relativeSquareMap a hΓ hB (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) =
      CechMatching.StrictMap.id _ := by
  apply CechMatching.StrictMap.ext
  · have hh := congrArg CechMatching.StrictMap.localMap (squareMap_id a (.ext hΓ hB) (f := f))
    exact hh
  · have hh := congrArg CechMatching.StrictMap.doubleMap (squareMap_id a (.ext hΓ hB) (f := f))
    exact hh
  · have hh := congrArg CechMatching.StrictMap.tripleMap (squareMap_id a (.ext hΓ hB) (f := f))
    exact hh

variable {X'' Y'' : Sheaf topology Type} {l : Y'' ⟶ X''}
variable (u' : X'' ⟶ X') (v' : Y'' ⟶ Y') (square' : v' ≫ k = l ≫ u')

theorem relativeSquareMap_comp :
    (relativeSquareMap a hΓ hB u v square).comp (relativeSquareMap a hΓ hB u' v' square') =
      relativeSquareMap a hΓ hB (u' ≫ u) (v' ≫ v) (by
        rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  apply CechMatching.StrictMap.ext
  · have hh := congrArg CechMatching.StrictMap.localMap (squareMap_comp a (.ext hΓ hB) u v square u' v' square')
    exact hh
  · have hh := congrArg CechMatching.StrictMap.doubleMap (squareMap_comp a (.ext hΓ hB) u v square u' v' square')
    exact hh
  · have hh := congrArg CechMatching.StrictMap.tripleMap (squareMap_comp a (.ext hΓ hB) u v square u' v' square')
    exact hh

theorem relativeSquareFunctor_id :
    relativeSquareFunctor a hΓ hB (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) = 𝟭 _ := by
  unfold relativeSquareFunctor
  rw [relativeSquareMap_id, CechMatching.StrictMap.functor_id]

theorem relativeSquareFunctor_comp :
    relativeSquareFunctor a hΓ hB u v square ⋙ relativeSquareFunctor a hΓ hB u' v' square' =
      relativeSquareFunctor a hΓ hB (u' ≫ u) (v' ≫ v) (by
        rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  unfold relativeSquareFunctor
  rw [← CechMatching.StrictMap.functor_comp, relativeSquareMap_comp]

end SquareKit.SmoothQuotientCoverMatching

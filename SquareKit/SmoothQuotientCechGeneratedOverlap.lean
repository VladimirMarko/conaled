import SquareKit.SmoothQuotientCechGeneratedLocal
import SquareKit.Internal.PathTransport.AlignedSignatureComparisonLaws

/-! Generated overlap comparisons retain the primitive diagonal and cocycle. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

def firstRestrictionFiber (f : Y ⟶ SplitSheaf.Cech.double A) :=
  firstFiber a A ≫ whiskerLeft
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A))
    (restrictionFamily f)

def secondRestrictionFiber (f : Y ⟶ SplitSheaf.Cech.double A) :=
  secondFiber a A ≫ whiskerLeft
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A))
    (restrictionFamily f)

theorem overlapRestriction_square (f : Y ⟶ SplitSheaf.Cech.double A) :
    firstRestrictionFiber a A f ≫
      whiskerRight (isoWhiskerRight (overlap a A) (restriction f)).hom (family a Y) =
    secondRestrictionFiber a A f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro b
  change transport (d.overlap.hom.reindex f) (restrict f (restrict (SplitSheaf.Cech.first A) b.val)) =
    restrict f (restrict (SplitSheaf.Cech.second A) b.val)
  rw [← transport_restrict, b.property]

def restrictedComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) (f : Y ⟶ SplitSheaf.Cech.double A) :
    parameterMap a A hΓ (f ≫ SplitSheaf.Cech.first A) ≅
      parameterMap a A hΓ (f ≫ SplitSheaf.Cech.second A) :=
  alignedContextComparison (isoWhiskerRight (overlap a A) (restriction f))
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A)) (family a Y)
    (firstRestrictionFiber a A f) (secondRestrictionFiber a A f)
    (overlapRestriction_square a A f) hΓ

theorem restrictedComparison_formula (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (f : Y ⟶ SplitSheaf.Cech.double A) :
    restrictedComparison a A hΓ f =
      (eqToIso (alignedGenerated_comp
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.double A)) (restriction f) (family a Y)
        (firstFiber a A) (restrictionFamily f) hΓ)).symm ≪≫
      isoWhiskerRight
        (alignedContextComparison (overlap a A)
          (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
          (family a (SplitSheaf.Cech.double A)) (firstFiber a A) (secondFiber a A)
          (overlap_square a A) hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ f) ≪≫
      eqToIso (alignedGenerated_comp
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.double A)) (restriction f) (family a Y)
        (secondFiber a A) (restrictionFamily f) hΓ) :=
  alignedContextComparison_postcompose
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.double A)) (restriction f) (family a Y)
    (overlap a A) (firstFiber a A) (secondFiber a A) (restrictionFamily f)
    (overlap_square a A) (overlapRestriction_square a A f) hΓ

theorem restrictedComparison_diagonal (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    restrictedComparison a A hΓ (SplitSheaf.Cech.diagonal A) =
      Iso.refl (localMap a A hΓ) := by
  unfold restrictedComparison
  simp only [overlap_diagonal]
  apply alignedContextComparison_refl

theorem firstRestrictionFiber_triple :
    firstRestrictionFiber a A (SplitSheaf.Cech.firstSecond A) =
      firstRestrictionFiber a A (SplitSheaf.Cech.firstThird A) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro b
  apply Deformation.ext
  rfl

theorem middleRestrictionFiber_triple :
    secondRestrictionFiber a A (SplitSheaf.Cech.firstSecond A) =
      firstRestrictionFiber a A (SplitSheaf.Cech.secondThird A) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro b
  apply Deformation.ext
  rfl

theorem lastRestrictionFiber_triple :
    secondRestrictionFiber a A (SplitSheaf.Cech.secondThird A) =
      secondRestrictionFiber a A (SplitSheaf.Cech.firstThird A) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro b
  apply Deformation.ext
  rfl

theorem tripleFirstMap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    parameterMap a A hΓ (SplitSheaf.Cech.firstSecond A ≫ SplitSheaf.Cech.first A) =
      parameterMap a A hΓ (SplitSheaf.Cech.firstThird A ≫ SplitSheaf.Cech.first A) :=
  congrArg (parameterMap a A hΓ) (SplitSheaf.Cech.firstSecond_first A)

theorem tripleMiddleMap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    parameterMap a A hΓ (SplitSheaf.Cech.firstSecond A ≫ SplitSheaf.Cech.second A) =
      parameterMap a A hΓ (SplitSheaf.Cech.secondThird A ≫ SplitSheaf.Cech.first A) :=
  congrArg (parameterMap a A hΓ) (SplitSheaf.Cech.firstSecond_second A)

theorem tripleLastMap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    parameterMap a A hΓ (SplitSheaf.Cech.secondThird A ≫ SplitSheaf.Cech.second A) =
      parameterMap a A hΓ (SplitSheaf.Cech.firstThird A ≫ SplitSheaf.Cech.second A) :=
  congrArg (parameterMap a A hΓ) (SplitSheaf.Cech.firstThird_second A).symm

end SquareKit.SmoothQuotientCechLocal

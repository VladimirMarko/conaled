import SquareKit.SmoothQuotientCechGeneratedOverlap

/-! Explicit equality of the three primitive overlap vertices. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem triple_middle_primitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.firstSecond A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.secondThird A) := rfl

theorem triple_first_primitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.firstSecond A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.firstThird A) := rfl

theorem triple_last_primitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.secondThird A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.firstThird A) := rfl

theorem overlap_triple_cocycle :
    isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstSecond A)) ≪≫
      eqToIso (triple_middle_primitive a A) ≪≫
      isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.secondThird A)) =
    eqToIso (triple_first_primitive a A) ≪≫
      isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstThird A)) ≪≫
      (eqToIso (triple_last_primitive a A)).symm := by
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  exact (overlap_cocycle a A).trans (Iso.trans_refl _).symm

theorem first_triple_fiber_heq :
    HEq (firstRestrictionFiber a A (SplitSheaf.Cech.firstSecond A))
      (firstRestrictionFiber a A (SplitSheaf.Cech.firstThird A)) :=
  heq_of_eq (firstRestrictionFiber_triple a A)

theorem middle_triple_fiber_heq :
    HEq (secondRestrictionFiber a A (SplitSheaf.Cech.firstSecond A))
      (firstRestrictionFiber a A (SplitSheaf.Cech.secondThird A)) :=
  heq_of_eq (restriction_fiber_triple_middle a A)

theorem last_triple_fiber_heq :
    HEq (secondRestrictionFiber a A (SplitSheaf.Cech.secondThird A))
      (secondRestrictionFiber a A (SplitSheaf.Cech.firstThird A)) :=
  heq_of_eq (secondRestrictionFiber_triple_last a A)

/-- Use the composite parameter map as the primitive endpoint before generation. -/
def parameterOverlap {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Cech.double A) :
    SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (f ≫ SplitSheaf.Cech.first A) ≅
      SheafActionQuotient.Cech.localFunctor ⋙ restriction (f ≫ SplitSheaf.Cech.second A) :=
  isoWhiskerRight (overlap a A) (restriction f)

theorem parameterOverlap_square {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Cech.double A) :
    parameterFiber a A (f ≫ SplitSheaf.Cech.first A) ≫
      whiskerRight (parameterOverlap a A f).hom (family a Y) =
    parameterFiber a A (f ≫ SplitSheaf.Cech.second A) :=
  overlap_restriction_square a A f

theorem localFunctor_restriction_congr {Y : Sheaf topology Type}
    {f g : Y ⟶ SplitSheaf.extension A} (h : f = g) :
    SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) f =
      SheafActionQuotient.Cech.localFunctor ⋙ restriction g := by cases h; rfl

theorem parameterFiber_heq {Y : Sheaf topology Type}
    {f g : Y ⟶ SplitSheaf.extension A} (h : f = g) :
    HEq (parameterFiber a A f) (parameterFiber a A g) := by cases h; rfl

theorem parameterOverlap_cocycle :
    parameterOverlap a A (SplitSheaf.Cech.firstSecond A) ≪≫
      eqToIso (localFunctor_restriction_congr a A (SplitSheaf.Cech.firstSecond_second A)) ≪≫
      parameterOverlap a A (SplitSheaf.Cech.secondThird A) =
    eqToIso (localFunctor_restriction_congr a A (SplitSheaf.Cech.firstSecond_first A)) ≪≫
      parameterOverlap a A (SplitSheaf.Cech.firstThird A) ≪≫
      (eqToIso (localFunctor_restriction_congr a A (SplitSheaf.Cech.firstThird_second A).symm)).symm :=
  overlap_triple_cocycle a A

def primitiveTriangle : AlignedTriangle
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.triple A)) where
  F₁ := _
  F₂ := _
  G₁ := _
  G₂ := _
  H₁ := _
  H₂ := _
  η := parameterOverlap a A (SplitSheaf.Cech.firstSecond A)
  θ := parameterOverlap a A (SplitSheaf.Cech.secondThird A)
  ζ := parameterOverlap a A (SplitSheaf.Cech.firstThird A)
  α := parameterFiber a A (SplitSheaf.Cech.firstSecond A ≫ SplitSheaf.Cech.first A)
  β := parameterFiber a A (SplitSheaf.Cech.firstSecond A ≫ SplitSheaf.Cech.second A)
  β' := parameterFiber a A (SplitSheaf.Cech.secondThird A ≫ SplitSheaf.Cech.first A)
  δ := parameterFiber a A (SplitSheaf.Cech.secondThird A ≫ SplitSheaf.Cech.second A)
  α' := parameterFiber a A (SplitSheaf.Cech.firstThird A ≫ SplitSheaf.Cech.first A)
  δ' := parameterFiber a A (SplitSheaf.Cech.firstThird A ≫ SplitSheaf.Cech.second A)
  hm := localFunctor_restriction_congr a A (SplitSheaf.Cech.firstSecond_second A)
  hf := localFunctor_restriction_congr a A (SplitSheaf.Cech.firstSecond_first A)
  hl := localFunctor_restriction_congr a A (SplitSheaf.Cech.firstThird_second A).symm
  ha := parameterFiber_heq a A (SplitSheaf.Cech.firstSecond_first A)
  hb := parameterFiber_heq a A (SplitSheaf.Cech.firstSecond_second A)
  hd := parameterFiber_heq a A (SplitSheaf.Cech.firstThird_second A).symm
  cocycle := parameterOverlap_cocycle a A
  squareη := parameterOverlap_square a A (SplitSheaf.Cech.firstSecond A)
  squareθ := parameterOverlap_square a A (SplitSheaf.Cech.secondThird A)
  squareζ := parameterOverlap_square a A (SplitSheaf.Cech.firstThird A)

end SquareKit.SmoothQuotientCechLocal

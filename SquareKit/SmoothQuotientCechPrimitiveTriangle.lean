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

theorem tripleMiddlePrimitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.firstSecond A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.secondThird A) := rfl

theorem tripleFirstPrimitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.firstSecond A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)) ⋙
        restriction (SplitSheaf.Cech.firstThird A) := rfl

theorem tripleLastPrimitive :
    (SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.secondThird A) =
      (SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A)) ⋙
        restriction (SplitSheaf.Cech.firstThird A) := rfl

theorem triplePrimitive_cocycle :
    isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstSecond A)) ≪≫
      eqToIso (tripleMiddlePrimitive a A) ≪≫
      isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.secondThird A)) =
    eqToIso (tripleFirstPrimitive a A) ≪≫
      isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstThird A)) ≪≫
      (eqToIso (tripleLastPrimitive a A)).symm := by
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  exact (overlap_cocycle a A).trans (Iso.trans_refl _).symm

theorem firstTripleFiberHEq :
    HEq (firstRestrictionFiber a A (SplitSheaf.Cech.firstSecond A))
      (firstRestrictionFiber a A (SplitSheaf.Cech.firstThird A)) :=
  heq_of_eq (firstRestrictionFiber_triple a A)

theorem middleTripleFiberHEq :
    HEq (secondRestrictionFiber a A (SplitSheaf.Cech.firstSecond A))
      (firstRestrictionFiber a A (SplitSheaf.Cech.secondThird A)) :=
  heq_of_eq (middleRestrictionFiber_triple a A)

theorem lastTripleFiberHEq :
    HEq (secondRestrictionFiber a A (SplitSheaf.Cech.secondThird A))
      (secondRestrictionFiber a A (SplitSheaf.Cech.firstThird A)) :=
  heq_of_eq (lastRestrictionFiber_triple a A)

/-- Use the composite parameter map as the primitive endpoint before generation. -/
def parameterOverlap {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Cech.double A) :
    SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) (f ≫ SplitSheaf.Cech.first A) ≅
      SheafActionQuotient.Cech.localFunctor ⋙ restriction (f ≫ SplitSheaf.Cech.second A) :=
  isoWhiskerRight (overlap a A) (restriction f)

theorem parameterOverlap_square {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Cech.double A) :
    parameterFiber a A (f ≫ SplitSheaf.Cech.first A) ≫
      whiskerRight (parameterOverlap a A f).hom (family a Y) =
    parameterFiber a A (f ≫ SplitSheaf.Cech.second A) :=
  overlapRestriction_square a A f

theorem parameterFunctor_eq {Y : Sheaf topology Type}
    {f g : Y ⟶ SplitSheaf.Ext A} (h : f = g) :
    SheafActionQuotient.Cech.localFunctor ⋙ restriction (a := a) f =
      SheafActionQuotient.Cech.localFunctor ⋙ restriction g := by cases h; rfl

theorem parameterFiber_heq {Y : Sheaf topology Type}
    {f g : Y ⟶ SplitSheaf.Ext A} (h : f = g) :
    HEq (parameterFiber a A f) (parameterFiber a A g) := by cases h; rfl

theorem parameterTriangle_cocycle :
    parameterOverlap a A (SplitSheaf.Cech.firstSecond A) ≪≫
      eqToIso (parameterFunctor_eq a A (SplitSheaf.Cech.firstSecond_second A)) ≪≫
      parameterOverlap a A (SplitSheaf.Cech.secondThird A) =
    eqToIso (parameterFunctor_eq a A (SplitSheaf.Cech.firstSecond_first A)) ≪≫
      parameterOverlap a A (SplitSheaf.Cech.firstThird A) ≪≫
      (eqToIso (parameterFunctor_eq a A (SplitSheaf.Cech.firstThird_second A).symm)).symm :=
  triplePrimitive_cocycle a A

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
  hm := parameterFunctor_eq a A (SplitSheaf.Cech.firstSecond_second A)
  hf := parameterFunctor_eq a A (SplitSheaf.Cech.firstSecond_first A)
  hl := parameterFunctor_eq a A (SplitSheaf.Cech.firstThird_second A).symm
  ha := parameterFiber_heq a A (SplitSheaf.Cech.firstSecond_first A)
  hb := parameterFiber_heq a A (SplitSheaf.Cech.firstSecond_second A)
  hd := parameterFiber_heq a A (SplitSheaf.Cech.firstThird_second A).symm
  cocycle := parameterTriangle_cocycle a A
  squareη := parameterOverlap_square a A (SplitSheaf.Cech.firstSecond A)
  squareθ := parameterOverlap_square a A (SplitSheaf.Cech.secondThird A)
  squareζ := parameterOverlap_square a A (SplitSheaf.Cech.firstThird A)

end SquareKit.SmoothQuotientCechLocal

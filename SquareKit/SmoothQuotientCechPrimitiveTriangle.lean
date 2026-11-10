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

def primitiveTriangle : AlignedTriangle
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.triple A)) where
  F₁ := _
  F₂ := _
  G₁ := _
  G₂ := _
  H₁ := _
  H₂ := _
  η := isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstSecond A))
  θ := isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.secondThird A))
  ζ := isoWhiskerRight (overlap a A) (restriction (SplitSheaf.Cech.firstThird A))
  α := firstRestrictionFiber a A (SplitSheaf.Cech.firstSecond A)
  β := secondRestrictionFiber a A (SplitSheaf.Cech.firstSecond A)
  β' := firstRestrictionFiber a A (SplitSheaf.Cech.secondThird A)
  δ := secondRestrictionFiber a A (SplitSheaf.Cech.secondThird A)
  α' := firstRestrictionFiber a A (SplitSheaf.Cech.firstThird A)
  δ' := secondRestrictionFiber a A (SplitSheaf.Cech.firstThird A)
  hm := tripleMiddlePrimitive a A
  hf := tripleFirstPrimitive a A
  hl := tripleLastPrimitive a A
  ha := firstTripleFiberHEq a A
  hb := middleTripleFiberHEq a A
  hd := lastTripleFiberHEq a A
  cocycle := triplePrimitive_cocycle a A
  squareη := overlapRestriction_square a A (SplitSheaf.Cech.firstSecond A)
  squareθ := overlapRestriction_square a A (SplitSheaf.Cech.secondThird A)
  squareζ := overlapRestriction_square a A (SplitSheaf.Cech.firstThird A)

end SquareKit.SmoothQuotientCechLocal

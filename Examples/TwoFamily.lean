import SquareKit.Internal.PathTransport.TwoFamily
import Examples.TwoGroupoidHom

/-! The integer path action inhabits the general higher-family interface,
including its horizontal laws. -/
namespace Examples.TwoFamily
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev fiber : StrictTwoCategory := ⟨LocallyDiscrete TwoGroupoidPath.Fiber⟩

/-- Every base 2-cell acts by its integer component, not by an erased cell. -/
def pathFamily : TwoFamily.Family TwoGroupoidPath.Base := StrictPseudofunctor.mk'' {
  obj := fun _ => fiber
  map := fun _ => StrictPseudofunctor.id _
  map₂ := fun α => TwoGroupoidHom.integerTrans (Multiplicative.toAdd α)
  map₂_id := fun _ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
  map₂_comp := fun α β => by
    change TwoGroupoidHom.integerTrans (Multiplicative.toAdd β + Multiplicative.toAdd α) = _
    rw [add_comm]
    exact (TwoGroupoidHom.integerTrans_comp _ _).symm
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun f _ _ α => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Discrete.mk (Multiplicative.ofAdd (Multiplicative.toAdd α))) =
      𝟙 a ≫ Discrete.mk (Multiplicative.ofAdd (Multiplicative.toAdd α)) ≫ 𝟙 a
    simp
  map₂_whisker_right := fun α f => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Discrete.mk (Multiplicative.ofAdd (Multiplicative.toAdd α))) =
      𝟙 a ≫ Discrete.mk (Multiplicative.ofAdd (Multiplicative.toAdd α)) ≫ 𝟙 a
    simp
}

def point : TwoFamily.Total pathFamily :=
  ⟨DoubleDelooping.point _, TwoGroupoidHom.pathTarget⟩

def arrow (n : ℤ) : TwoFamily.Hom pathFamily point point :=
  TwoGroupoidHom.arrow (TwoFamily.evaluation pathFamily point.fiber) point.fiber
    (DoubleDelooping.arrow _) (Discrete.mk (Multiplicative.ofAdd n))

/-- General family evaluation gives exactly the original integer boundary. -/
def cell {m n : ℤ} (p : TwoGroupoidPath.Cell m n) : arrow m ⟶ arrow n :=
  TwoGroupoidHom.cell (Multiplicative.ofAdd p.base)
    (eqToHom (Discrete.ext p.boundary))

theorem retains_nonzero_action : (cell (TwoGroupoidPath.comparison 1 0)).base =
    Multiplicative.ofAdd (1 : ℤ) := rfl

theorem compose_integers (m n : ℤ) :
    TwoFamily.compose pathFamily (arrow m) (arrow n) = arrow (m + n) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  change HEq ((show point.fiber ⟶ point.fiber from 𝟙 point.fiber) ≫ Discrete.mk (Multiplicative.ofAdd m) ≫
    Discrete.mk (Multiplicative.ofAdd n)) (Discrete.mk (Multiplicative.ofAdd (m + n)))
  simp only [Category.id_comp, heq_eq_eq]
  apply Discrete.ext
  exact congrArg Multiplicative.ofAdd (add_comm n m)

theorem right_whisker_retains_base (k : ℤ) :
    (TwoFamily.whiskerRight pathFamily (cell (TwoGroupoidPath.comparison 1 0))
      (arrow k)).base = Multiplicative.ofAdd (1 : ℤ) := rfl

theorem left_whisker_retains_base (k : ℤ) :
    (TwoFamily.whiskerLeft pathFamily (arrow k)
      (cell (TwoGroupoidPath.comparison 1 0))).base = Multiplicative.ofAdd (1 : ℤ) := rfl

end Examples.TwoFamily

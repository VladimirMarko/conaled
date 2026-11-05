import SquareKit.Internal.PathTransport.TwoOpenIdentityHigher
import Examples.TwoIdentityTransport

/-! Endpoint comparison acts by the difference of two genuine integer 2-cells. -/
namespace Examples.TwoOpenIdentityHigher
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev B := DoubleDelooping.Space (Multiplicative ℤ)
abbrev point : B := DoubleDelooping.point _
abbrev arrow : point ⟶ point := DoubleDelooping.arrow _

local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩

/-- A constant higher family whose fiber has every integer as a genuine 2-cell. -/
def integerFamily : TwoFamily.Family B := StrictPseudofunctor.mk'' {
  obj := fun _ => ⟨B⟩
  map := fun _ => StrictPseudofunctor.id B
  map₂ := fun _ => 𝟙 (StrictPseudofunctor.id B)
  map₂_id := fun _ => rfl
  map₂_comp := fun _ _ => (Category.id_comp _).symm
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun _ _ _ _ => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (𝟙 a : a ⟶ a) = 𝟙 a ≫ 𝟙 a ≫ 𝟙 a
    simp
  map₂_whisker_right := fun _ _ => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (𝟙 a : a ⟶ a) = 𝟙 a ≫ 𝟙 a ≫ 𝟙 a
    simp
}
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

def endpoints : TwoFamily.Total (TwoFamily.endpointFamily integerFamily) :=
  ⟨point, (point, point)⟩
def endpointArrow : endpoints ⟶ endpoints := ⟨arrow, (arrow, arrow)⟩
def endpointCell (m n : ℤ) : endpointArrow ⟶ endpointArrow where
  base := 𝟙 arrow
  fiber := (Multiplicative.ofAdd m, Multiplicative.ofAdd n)

/-- The hom-functor retains the difference of the two endpoint comparison cells. -/
theorem endpoint_difference (m n : ℤ) :
    ((TwoFamily.openIdHomFunctor integerFamily endpoints endpoints).map
      (endpointCell m n)).app arrow = Multiplicative.ofAdd (n - m) := by
  exact Examples.TwoIdentityTransport.comparison_integer m n

/-- Vertical composition of arbitrary endpoint cells uses the constructed general law. -/
theorem endpoint_pasting (m n r s : ℤ) :
    TwoFamily.openIdCell integerFamily (endpointCell m n ≫ endpointCell r s) =
      TwoFamily.openIdCell integerFamily (endpointCell m n) ≫
        TwoFamily.openIdCell integerFamily (endpointCell r s) :=
  TwoFamily.openIdCell_comp integerFamily _ _

/-- The locally discrete embedding still observes both integer endpoint cells. -/
theorem embedded_endpoint_difference (m n : ℤ) :
    (((TwoFamily.openIdHigherPrelax integerFamily).map₂ (endpointCell m n)).app
      ⟨arrow⟩).as = Multiplicative.ofAdd (n - m) := endpoint_difference m n

/-- Original fiber 2-cells remain arrows in the embedded identity fiber. -/
theorem embedded_fiber_cell (k : ℤ) :
    (((TwoFamily.openIdHigherPrelax integerFamily).map endpointArrow).map
      (show (LocallyDiscrete.mk arrow) ⟶ LocallyDiscrete.mk arrow from
        Discrete.mk (Multiplicative.ofAdd k))).as = Multiplicative.ofAdd k := rfl

end Examples.TwoOpenIdentityHigher

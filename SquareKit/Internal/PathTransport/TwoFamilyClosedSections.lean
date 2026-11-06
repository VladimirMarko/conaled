import SquareKit.Internal.PathTransport.TwoFamilySectionValues
/-! Closed sections retain a chosen fiber object over the constructed terminal
higher context. The constant strict functor supplies all arrow and cell data. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (Γ Δ : Context.{u})
def pointFunctor (d : Δ) : StrictPseudofunctor Γ Δ :=
  StrictPseudofunctor.mk'' {
    obj := fun _ => d
    map := fun _ => 𝟙 d
    map₂ := fun _ => 𝟙 (𝟙 d)
    map_comp := fun _ _ => (Category.id_comp _).symm
  }
def emptyPoint : Context.empty.{u} := ⟨⟨PUnit.unit⟩⟩
theorem empty_obj_eq (x y : Context.empty.{u}) : x = y := by
  rcases x with ⟨⟨⟨⟩⟩⟩
  rcases y with ⟨⟨⟨⟩⟩⟩
  rfl

theorem empty_hom_heq {x y x' y' : Context.empty.{u}} (f : x ⟶ y) (g : x' ⟶ y') :
    HEq f g := by
  rcases x with ⟨⟨⟨⟩⟩⟩
  rcases y with ⟨⟨⟨⟩⟩⟩
  rcases x' with ⟨⟨⟨⟩⟩⟩
  rcases y' with ⟨⟨⟨⟩⟩⟩
  apply heq_of_eq
  apply Discrete.ext
  exact Subsingleton.elim _ _

theorem empty_cell_heq {x y x' y' : Context.empty.{u}} {f g : x ⟶ y} {f' g' : x' ⟶ y'}
    (α : f ⟶ g) (β : f' ⟶ g') : HEq α β := by
  rcases x with ⟨⟨⟨⟩⟩⟩
  rcases y with ⟨⟨⟨⟩⟩⟩
  rcases x' with ⟨⟨⟨⟩⟩⟩
  rcases y' with ⟨⟨⟨⟩⟩⟩
  have hf := eq_of_heq (empty_hom_heq f f')
  have hg := eq_of_heq (empty_hom_heq g g')
  cases hf
  cases hg
  exact heq_of_eq (Discrete.hom_eq (f := α) (g := β))

theorem empty_functor_eq (F G : StrictPseudofunctor Γ Context.empty.{u}) : F = G := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x; exact empty_obj_eq _ _
  · intro x y f; exact empty_hom_heq _ _
  · intro x y f g α; exact empty_cell_heq _ _

def closedSection (A : Family Context.empty.{u}) (a : A.data.obj emptyPoint) : TwoFamily.Section A.data where
  lift := pointFunctor Context.empty A.total ⟨emptyPoint,a⟩
  over := empty_functor_eq _ _ _

theorem closedSection_value (A : Family Context.empty.{u}) (a : A.data.obj emptyPoint) :
    ((closedSection A a).normalObj A.data emptyPoint).fiber = a := by
  exact eq_of_heq ((closedSection A a).normalObj_fiber_heq A.data emptyPoint)
end SquareKit.Internal.PathTransport.HigherInterpretation

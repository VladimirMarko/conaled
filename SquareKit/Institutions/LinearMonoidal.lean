import SquareKit.Institutions.LinearModels
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! The source model laws supply Mathlib's symmetric monoidal contract. This
bridge checks the structural law coverage against an independent interface. -/
namespace SquareKit.Institutions.Linear.Model
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The category of interpreted context arrows. -/
@[instance_reducible] def category (M : Model α) : Category (Formula α) where
  Hom := M.Hom
  id := M.identity
  comp f g := M.compose g f
  id_comp f := M.laws.id_right f
  comp_id f := M.laws.id_left f
  assoc f g h := M.laws.compose_assoc f g h

@[instance_reducible] def monoidalStruct (M : Model α) : letI := category M; MonoidalCategoryStruct (Formula α) := by
  letI := category M
  let swap (A B) : Formula.tensor A B ≅ Formula.tensor B A :=
    ⟨M.swap A B, M.swap B A, M.laws.swap_swap A B, M.laws.swap_swap B A⟩
  let unit (A) : Formula.tensor .unit A ≅ A :=
    ⟨M.unit A, M.ununit A, M.laws.ununit_unit A, M.laws.unit_ununit A⟩
  exact {
    tensorObj := Formula.tensor
    tensorHom := M.tensor
    whiskerLeft := fun A {_ _} f => M.tensor (M.identity A) f
    whiskerRight := fun {_ _} f A => M.tensor f (M.identity A)
    tensorUnit := .unit
    associator := fun A B C =>
      ⟨M.assoc A B C, M.unassoc A B C, M.laws.unassoc_assoc A B C, M.laws.assoc_unassoc A B C⟩
    leftUnitor := unit
    rightUnitor := fun A => (swap A .unit).trans (unit A)
  }

@[instance_reducible] def monoidal (M : Model α) : letI := category M; MonoidalCategory (Formula α) := by
  letI := category M
  letI := monoidalStruct M
  exact @MonoidalCategory.ofTensorHom _ (category M) (monoidalStruct M)
    (id_tensorHom_id := M.laws.tensor_id)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f h g k => (M.laws.tensor_comp f g h k).symm)
    (associator_naturality := M.laws.assoc_natural)
    (leftUnitor_naturality := M.laws.unit_natural)
    (rightUnitor_naturality := M.laws.right_unit_natural)
    (pentagon := by
      intro A B C D
      change M.compose (M.compose (M.tensor (M.identity A) (M.assoc B C D))
          (M.assoc A (.tensor B C) D)) (M.tensor (M.assoc A B C) (M.identity D)) = _
      rw [← M.laws.compose_assoc]
      exact (M.laws.pentagon A B C D).symm)
    (triangle := M.laws.triangle)

@[instance_reducible] def symmetric (M : Model α) :
    letI := category M; letI := monoidal M; SymmetricCategory (Formula α) := by
  letI := category M
  letI := monoidal M
  exact {
    braiding := fun A B =>
      ⟨M.swap A B, M.swap B A, M.laws.swap_swap A B, M.laws.swap_swap B A⟩
    braiding_naturality_right := fun A {_ _} f => M.laws.swap_natural (M.identity A) f
    braiding_naturality_left := fun f B => M.laws.swap_natural f (M.identity B)
    hexagon_forward := by
      intro A B C
      change M.compose (M.compose (M.assoc B C A) (M.swap A (.tensor B C))) (M.assoc A B C) =
        M.compose (M.compose (M.tensor (M.identity B) (M.swap A C)) (M.assoc B A C))
          (M.tensor (M.swap A B) (M.identity C))
      rw [← M.laws.compose_assoc, ← M.laws.compose_assoc]
      exact M.laws.hexagon_forward A B C
    hexagon_reverse := by
      intro A B C
      change M.compose (M.compose (M.unassoc C A B) (M.swap (.tensor A B) C)) (M.unassoc A B C) =
        M.compose (M.compose (M.tensor (M.swap A C) (M.identity B)) (M.unassoc A C B))
          (M.tensor (M.identity A) (M.swap B C))
      rw [← M.laws.compose_assoc, ← M.laws.compose_assoc]
      exact M.laws.hexagon_reverse A B C
    symmetry := M.laws.swap_swap
  }

end SquareKit.Institutions.Linear.Model

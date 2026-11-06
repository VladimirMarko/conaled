import Mathlib.Logic.Equiv.Basic

/-! Range subtypes retain selected data across a change of presentation. -/
namespace SquareKit.Cubical.Presheaf
universe u

theorem rangePredicate_heq {X Y A B : Type u} (e : X ≃ Y) (h : A = B)
    (f : X → A) (g : Y → B) (he : ∀ x, HEq (f x) (g (e x))) :
    HEq (fun a => ∃ x, f x = a) (fun b => ∃ y, g y = b) := by
  cases h
  apply heq_of_eq
  funext a
  apply propext
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨e x,(eq_of_heq (he x)).symm⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨x,rfl⟩ := e.surjective y
    exact ⟨x,eq_of_heq (he x)⟩

theorem rangeSubtype_eq {X Y A B : Type u} (e : X ≃ Y) (h : A = B)
    (f : X → A) (g : Y → B) (he : ∀ x, HEq (f x) (g (e x))) :
    {a : A // ∃ x, f x = a} = {b : B // ∃ y, g y = b} := by
  cases h
  exact congrArg Subtype (eq_of_heq (rangePredicate_heq e rfl f g he))

end SquareKit.Cubical.Presheaf

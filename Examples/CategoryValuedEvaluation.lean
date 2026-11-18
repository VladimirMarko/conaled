import SquareKit.Internal.RepresentableEvaluation
import Mathlib.CategoryTheory.Category.Preorder

/-! Evaluation recovery in a category with noninvertible order arrows. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CategoryValuedEvaluation
open CategoryTheory SquareKit.RepresentableClassification

def context : Context.{0} ℕ := (Functor.const ℕᵒᵖ).obj PUnit

def family : context.Elements ⥤ ℕᵒᵖ := Functor.Elements.π context

def decoded : context.Elements ⥤ ℕᵒᵖ := evaluatedFunctor context ⋙ family

theorem evaluation : CategoricalEvaluation family decoded :=
  ⟨fun _ => rfl, fun _ => Subsingleton.elim _ _⟩

def recovery : decoded ≅ family := evaluation.iso

abbrev point (n : ℕ) : context.Elements := context.elementsMk (Opposite.op n) PUnit.unit

def step : point 2 ⟶ point 1 :=
  Functor.Elements.homMk (Quiver.Hom.op (homOfLE (by decide : 1 ≤ 2))) rfl

example : family.obj (point 2) ≠ family.obj (point 1) := by
  change (Opposite.op 2 : ℕᵒᵖ) ≠ Opposite.op 1
  intro h
  have := congrArg Opposite.unop h
  contradiction
example : IsEmpty (family.obj (point 1) ⟶ family.obj (point 2)) :=
  ⟨fun f => by have h := leOfHom f.unop; change 2 ≤ 1 at h; omega⟩

example : decoded.map step ≫ recovery.hom.app (point 1) =
    recovery.hom.app (point 2) ≫ family.map step := recovery.hom.naturality step

end Examples.CategoryValuedEvaluation

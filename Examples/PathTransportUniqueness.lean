import SquareKit.Internal.PathTransport.EliminationUniqueness
import Mathlib.CategoryTheory.CodiscreteCategory
/-!
# Why elimination uniqueness requires discrete fibers

An equivalence can omit objects that are merely isomorphic to objects in its
image. Two sections of a constant groupoid family can agree on that image and
choose different isomorphic objects elsewhere. This example checks that
restriction need not be injective for arbitrary groupoid-valued families.
-/
noncomputable section
namespace Examples.PathTransportUniqueness
open SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory
local instance : Groupoid (Codiscrete Bool) where
  inv _ := ()

/-- The singleton category includes the object `false`; both Boolean objects
are isomorphic, so this is an equivalence. -/
def inclusionEquivalence : Codiscrete Unit ≌ Codiscrete Bool where
  functor := Codiscrete.functorOfFun (fun _ => false)
  inverse := Codiscrete.functorOfFun (fun _ => ())
  unitIso := Codiscrete.natIso
  counitIso := Codiscrete.natIso

/-- A section choosing `false` at both objects. -/
def zero : Section (constant (Γ := Codiscrete Bool) (Codiscrete Bool)) :=
  constantSection (Codiscrete.functorOfFun (fun _ => false))
/-- A section choosing each base object itself. -/
def diagonal : Section (constant (Γ := Codiscrete Bool) (Codiscrete Bool)) :=
  constantSection (𝟭 _)

theorem unrestricted_reindex_not_injective : ¬ Function.Injective (fun s : Section (constant (Γ := Codiscrete Bool) (Codiscrete Bool)) =>
    s.reindex inclusionEquivalence.functor) := by
  intro h
  have he : zero = diagonal := h (show zero.reindex inclusionEquivalence.functor =
      diagonal.reindex inclusionEquivalence.functor from rfl)
  have hf := congrArg (fun s => (s.obj ⟨true⟩).as) he
  change false = true at hf
  cases hf
end Examples.PathTransportUniqueness

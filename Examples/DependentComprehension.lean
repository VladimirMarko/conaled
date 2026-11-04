import SquareKit.Internal.PathTransport.Representability
import SquareKit.FamilySquares
import SquareKit.TypeFamilyRepresentation
import SquareKit.UniformOperations
import Examples.DependentStructureBoundary
import Examples.GroupoidComprehensionBoundary
import Examples.GroupoidRoutes

/-! Checked specializations for #314: genuinely varying Type fibers,
noncommuting context substitutions, groupoid reindexing, and uniform syntax. -/
namespace Examples.DependentComprehension
open SquareKit.Internal.PathTransport.Typed
open CategoryTheory CategoryTheory.Limits

namespace Families
open SquareKit.FamilySquares

def first (n : Nat) (i : Fin (n+1)) : Fin ((n+1)+1) := i.castSucc

def second (n : Nat) (i : Fin (n+1)) : Fin ((2*n)+1) :=
  ⟨i.val, by omega⟩

/-- Increment then double sends base 3 to 8, keeping the selected index 2.
Reversing the base maps gives 7, so the case detects composition order. -/
def square : Square ((fun n => 2*n) ∘ (fun n => n+1))
    (fun n => Fin (n+1)) (fun n => Fin (n+1)) :=
  (equivalence (fun n => n+1) first).comp (equivalence (fun n => 2*n) second)

theorem concrete_total : square.total ⟨3, ⟨2, by decide⟩⟩ = ⟨8, ⟨2, by decide⟩⟩ := by
  rw [square, ← equivalence_comp]
  rfl

/-- Recovering the fiber function retains its dependent result type. -/
example (n : Nat) (i : Fin (n+1)) :
    (equivalence ((fun n => 2*n) ∘ (fun n => n+1))).symm square n i =
      second (n+1) (first n i) := by
  rw [square, ← equivalence_comp, Equiv.symm_apply_apply]

/-- The independent presentation admits Fin(n+1) without signature assignments. -/
example : (SquareKit.TypeFamilyRepresentation.representation.generic
    (fun n : Nat => Fin (n+1))).down ⟨3, ⟨2, by decide⟩⟩ = ⟨2, by decide⟩ :=
  SquareKit.TypeFamilyRepresentation.generic_apply _ _ _

end Families

namespace Groupoids
open SquareKit.Internal.PathTransport
open GroupoidTransport

noncomputable abbrev M := GroupoidModel.Instance.structuralModel C4 GroupoidRoutes.binary

/-- Both substitutions may be arbitrary functors, not just source substitutions.
The varying binary action therefore has an actual comprehension pullback. -/
example {Γ Δ : Grpd} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    IsPullback (C := M.ContextCat) (M.weaken Δ (M.subTy A σ)) (M.lift A σ)
      σ (M.weaken Γ A) := M.displayPullback A σ

example {Γ Δ Θ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (τ : M.Substitution Θ Δ) :
    M.compSub (M.lift A σ) (M.lift (M.subTy A σ) τ) =
      M.compSub (M.lift A (M.compSub σ τ)) (M.familyComparison (M.subTy_comp A σ τ)) :=
  M.lift_comp A σ τ

/-- The independent representation recovers the selected term, including its
fiber arrows, rather than just an isomorphism class of terms. -/
example {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (t : M.Section Δ (M.subTy A σ)) :
    HEq (M.subTm (M.genericVariable Γ A) (M.representation.pair A σ t)) t := by
  rw [M.representation_pair]
  exact M.variable_pair _ _ _

end Groupoids

namespace Uniform
open SquareKit

def second : UniformOperation 2 := UniformOperation.syntaxEquiv ⟨1, by decide⟩

example : second.run Nat (fun i => if i.val = 0 then 3 else 8) = 8 := by
  rw [second.reconstruction]
  rfl

example (t : UniformOperation 2) (ρ : Fin 2 → Nat) :
    t.run Nat (fun i => 2 * ρ i) = 2 * t.run Nat ρ :=
  (t.natural Nat Nat (fun n => 2*n) ρ).symm

example (choose : (A : Type) → Nonempty A → A) :
    ¬ (∀ (A : Type) (h : Nonempty A) (e : A ≃ A), e (choose A h) = choose A h) :=
  no_equivariant_choice choose

end Uniform
end Examples.DependentComprehension

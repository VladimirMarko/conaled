import SquareKit.Internal.Frobenius
import SquareKit.Internal.Presheaf

/-! Source Frobenius, model validity, and objectwise comparison remain separate. -/
namespace SquareKit.Internal.Presheaf
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J] {S : Type u} {F P : S → S → Type u}
variable {Γ : List S} {s : S}
variable (M : Model.{u,v,w} (J := J) F P) (h : Formula F Γ P) (p : Formula F (s :: Γ) P)

/-- Interpret exactly the source sequents, without using semantic Frobenius. -/
theorem frobenius_valid :
    M.formula (.conj h (.ex p)) = M.formula (.ex (.conj h.shift p)) :=
  le_antisymm (M.sound (Frobenius.forward h p)) (M.sound (Frobenius.backward h p))

/-- The semantic law puts P first. Commuting both intersections gives the
H-first order of the source theorem. Weakening is preimage along projection. -/
theorem frobenius_semantic_comparison :
    M.formula (.ex (.conj h.shift p)) =
      M.formula h ⊓ (M.formula p).image M.projection := by
  change ((M.formula h.shift) ⊓ M.formula p).image M.projection = _
  have shift : M.formula (h.shift (s := s)) = (M.formula h).preimage M.projection :=
    M.formula_substitution h (fun i => .var (.succ i))
  rw [shift, inf_comm, M.frobenius, inf_comm]

/-- Obtain the fiber equivalence by evaluating model validity. -/
theorem frobenius_evaluation (j : Jᵒᵖ) (ρ : Env (M.fiber j) Γ) :
    (h.eval (M.fiber j) ρ ∧ ∃ x, p.eval (M.fiber j) (ρ.extend x)) ↔
      ∃ x, h.shift.eval (M.fiber j) (ρ.extend x) ∧ p.eval (M.fiber j) (ρ.extend x) := by
  have e := congrArg (fun Q => Q.obj j ρ) (frobenius_valid M h p)
  exact (M.evaluation (.conj h (.ex p)) j ρ).symm.trans
    ((iff_of_eq e).trans (M.evaluation (.ex (.conj h.shift p)) j ρ))
end SquareKit.Internal.Presheaf

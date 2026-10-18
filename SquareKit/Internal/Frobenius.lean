import SquareKit.Internal.Substitution

/-! Frobenius as two restricted sequents, with a condition independent of the witness. -/
namespace SquareKit.Internal
universe u v
variable {S : Type u} {F P : S → S → Type u} {Γ : List S} {s : S}

namespace Rules
/-- Use the current head variable as a witness, discharging insertion bookkeeping. -/
theorem existsHere (p : Formula F (s :: Γ) P) : Derives p (FormulaCore.ex p).shift := by
  change Derives p (.ex (p.subst (Sub.lift (fun i => .var (.succ i)))))
  have d := existsIntro (p.subst (Sub.lift (fun i => .var (.succ i)))) (.var .zero)
  rw [FormulaCore.lift_shift_instantiate] at d
  exact d
end Rules

namespace Frobenius
variable (h : Formula F Γ P) (p : Formula F (s :: Γ) P)

theorem forward : Derives (.conj h (.ex p)) (.ex (.conj h.shift p)) :=
  Rules.existsElimWith (Rules.existsHere (.conj h.shift p))

theorem backward : Derives (.ex (.conj h.shift p)) (.conj h (.ex p)) :=
  Rules.existsElim (Rules.andIntro Rules.andLeft
    (Rules.cut Rules.andRight (Rules.existsHere p)))

/-- The equivalence is obtained solely from the two source derivations. -/
theorem inSet (M : Interpretation F P) (ρ : Env M Γ) :
    (h.eval M ρ ∧ ∃ x, p.eval M (ρ.extend x)) ↔
      ∃ x, h.shift.eval M (ρ.extend x) ∧ p.eval M (ρ.extend x) :=
  ⟨sound M (forward h p) ρ, sound M (backward h p) ρ⟩
end Frobenius
end SquareKit.Internal

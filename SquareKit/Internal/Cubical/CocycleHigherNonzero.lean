import SquareKit.Internal.Cubical.CocycleIdentityHomotopy
import SquareKit.Internal.Cubical.CocycleRootedFamily

/-! A genuine nonzero second identity in the same full cubical model used by the dependent client. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

def secondZero (Γ : Context.{0}) : Term (SecondIdentityFamily Γ) :=
  normalizedIdentityRefl (normalizedIdentityRefl (zeroTerm Γ))

theorem secondValue_zero (Γ : Context.{0}) (x : Γ.Elements) (r s : (interval Γ).obj x) :
    secondValue (secondZero Γ) x r s = zeroCocycle (Over x.obj.unop) :=
  (congrArg (fun p : (FirstIdentityFamily Γ).obj x => p.eval s)
    (LocalIdentity.eval_refl (normalizedIdentityRefl (zeroTerm Γ)) x r)).trans
      (LocalIdentity.eval_refl (zeroTerm Γ) x s)

theorem secondObservation_zero : secondObservation (secondZero terminal.{0}) = 0 :=
  (congrArg observeSquare (secondValue_zero terminal (terminalPoint ⟨2⟩) ⟨squareAxis 0⟩ ⟨squareAxis 1⟩)).trans
    observeSquare_zero

/-- The observer detects erasure even up to an actual third identity. -/
theorem secondIdentity_no_erasure :
    IsEmpty (Term (normalizedIdentity (SecondIdentityFamily terminal.{0})
      (secondIdentity terminal) (secondZero terminal))) := ⟨by
  intro h
  have e := secondObservation_identity h
  rw [secondObservation_selected,secondObservation_zero] at e
  exact Int.one_ne_zero e⟩

/-- A host equality erasing the chosen higher witness is also rejected. -/
theorem secondIdentity_ne_zero : secondIdentity terminal.{0} ≠ secondZero terminal := by
  intro h
  have e := congrArg secondObservation h
  rw [secondObservation_selected,secondObservation_zero] at e
  exact Int.one_ne_zero e

end SquareKit.Cubical.CategoryCocycles

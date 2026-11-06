import SquareKit.Internal.Cubical.CocycleSquareTerms
import SquareKit.Internal.Cubical.CocycleSquareValues
import SquareKit.Internal.Cubical.NormalizedIdentity
import SquareKit.Internal.Cubical.FaceEndpoints

/-! The selected square gives marked identity loops, with full marks at its ends. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

noncomputable def squarePath {Γ : Context.{0}} (r : Term (interval Γ)) :
    Term (path (reindex (cocycleFamily Γ) (projection (interval Γ))) (zeroTerm Γ) (zeroTerm Γ)) :=
  pathLam (squareTerm (r.reindex (projection (interval Γ))) (generic (interval Γ)))
    (squareTerm_right_endpoint r false) (squareTerm_right_endpoint r true)

def squareMark {Γ : Context.{0}} (r : Term (interval Γ)) : Cofibration Γ :=
  (Cofibration.endpoint r false).join (Cofibration.endpoint r true)

noncomputable def squareIdentity {Γ : Context.{0}} (r : Term (interval Γ)) :
    Term (identity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)) :=
  identityIntro (squarePath r) (squareMark r) (by
    intro x hx s
    rcases (Cofibration.full_join _ _ x).mp hx with hx | hx
    · have hr := congrArg ULift.down ((Cofibration.full_endpoint r false x).mp hx)
      change squareValue (r.val x).down s.down = zeroCocycle (Over x.obj.unop)
      exact (congrArg (fun a => squareValue a s.down) hr).trans (squareValue_left s.down false)
    · have hr := congrArg ULift.down ((Cofibration.full_endpoint r true x).mp hx)
      change squareValue (r.val x).down s.down = zeroCocycle (Over x.obj.unop)
      exact (congrArg (fun a => squareValue a s.down) hr).trans (squareValue_left s.down true))

theorem squareIdentity_endpoint (Γ : Context.{0}) (b : Bool) :
    squareIdentity (endpoint Γ b) = identityRefl (zeroTerm Γ) := by
  apply Term.ext
  intro x
  apply IdentityElement.ext
  · apply Subtype.ext
    apply PiElement.ext
    intro y f s
    exact squareValue_left s.down b
  · apply (Face.full_iff_top _).mp
    apply (Cofibration.full_join _ _ x).mpr
    cases b
    · exact Or.inl ((Cofibration.full_endpoint (endpoint Γ false) false x).mpr rfl)
    · exact Or.inr ((Cofibration.full_endpoint (endpoint Γ true) true x).mpr rfl)

noncomputable def normalizedSquareIdentity {Γ : Context.{0}} (r : Term (interval Γ)) :
    Term (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)) :=
  Term.map (normalizedIdentityIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)).hom (squareIdentity r)

theorem normalizedSquareIdentity_endpoint (Γ : Context.{0}) (b : Bool) :
    normalizedSquareIdentity (endpoint Γ b) = normalizedIdentityRefl (zeroTerm Γ) :=
  congrArg (Term.map (normalizedIdentityIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)).hom)
    (squareIdentity_endpoint Γ b)

end SquareKit.Cubical.CategoryCocycles

import SquareKit.Internal.Cubical.CocycleSquareIdentity

/-! The boundary generator inhabits the full model's normalized second identity. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

theorem normalizedSquareIdentity_val_reindex {Γ Δ : Context.{0}}
    (r : Term (interval Γ)) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    HEq ((normalizedSquareIdentity r).val (σ.mapElements.obj x))
      ((normalizedSquareIdentity (r.reindex σ)).val x) :=
  identityToLocal_substitution (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ) σ x
    ((squareIdentity r).val (σ.mapElements.obj x))

noncomputable def secondIdentityBody (Γ : Context.{0}) :
    Term (reindex (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
      (projection (interval Γ))) :=
  (normalizedSquareIdentity (generic (interval Γ))).convert
    (normalizedIdentity_reindex (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ) (projection (interval Γ))).symm

theorem secondIdentityBody_endpoint (Γ : Context.{0}) (b : Bool) :
    (secondIdentityBody Γ).reindex (endpointSub Γ b) = normalizedIdentityRefl (zeroTerm Γ) := by
  apply Term.ext
  intro x
  have h₁ := Term.convert_val_heq
    (normalizedIdentity_reindex (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ) (projection (interval Γ))).symm
    (normalizedSquareIdentity (generic (interval Γ))) ((endpointSub Γ b).mapElements.obj x)
  have h₂ := normalizedSquareIdentity_val_reindex (generic (interval Γ)) (endpointSub Γ b) x
  have h₃ := congrArg (fun t => t.val x) (normalizedSquareIdentity_endpoint Γ b)
  exact eq_of_heq (h₁.trans (h₂.trans (heq_of_eq h₃)))

noncomputable def secondIdentityPath (Γ : Context.{0}) :
    Term (path (reindex (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
      (projection (interval Γ))) (normalizedIdentityRefl (zeroTerm Γ)) (normalizedIdentityRefl (zeroTerm Γ))) :=
  pathLam (secondIdentityBody Γ) (secondIdentityBody_endpoint Γ false) (secondIdentityBody_endpoint Γ true)

noncomputable def secondIdentityRaw (Γ : Context.{0}) :
    Term (identity (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
      (normalizedIdentityRefl (zeroTerm Γ)) (normalizedIdentityRefl (zeroTerm Γ))) :=
  identityIntro (secondIdentityPath Γ) (Cofibration.bot Γ) (by intro x hx; cases hx)

noncomputable def secondIdentity (Γ : Context.{0}) :
    Term (normalizedIdentity (normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ))
      (normalizedIdentityRefl (zeroTerm Γ)) (normalizedIdentityRefl (zeroTerm Γ))) :=
  Term.map (normalizedIdentityIso _ _ _).hom (secondIdentityRaw Γ)

end SquareKit.Cubical.CategoryCocycles

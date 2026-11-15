import SquareKit.Internal.Cubical.Judgments.FillingTheory

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

abbrev transportEnvironment (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
    (F : Filling B) (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false))) :
    Fin 5 → Value.{u} := ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a]

theorem transportEnvironment_valid (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
    (F : Filling B) (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
    (hF : F.Lawful) (hc : RestrictedConstancy B φ) (i : Fin 4) :
    (transpRule.premise i).eval algebra (transportEnvironment Γ B F φ a) := by
  let ρ := transportEnvironment Γ B F φ a
  have hI := intervalContext_eval (.var (0 : Fin 5)) ρ Γ rfl
  have hep := endpointSub_eval (.var (0 : Fin 5)) ρ Γ rfl false
  have hp := projection_eval (.var (0 : Fin 5)) ρ Γ rfl
  have hface := intervalFace_eval (.var (0 : Fin 5)) (.var 3) ρ Γ φ rfl rfl
  have hB0 := subTy_eval (.var (1 : Fin 5)) (endpointSub (.var 0) false) ρ _ _ B _ rfl hep
  have hBconst := subTy_eval (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0))
    ρ _ _ _ _ hB0 hp
  fin_cases i
  · exact ⟨total (Presheaf.interval Γ),B,F,hI,rfl,rfl,hF⟩
  · exact ⟨Γ,φ,rfl,rfl⟩
  · exact ⟨Γ,reindex B (Presheaf.endpointSub Γ false),a,rfl,hB0,rfl⟩
  · have hleft := restrictedType_eval (intervalContext (.var (0 : Fin 5))) (.var 1)
      (intervalFace (.var 0) (.var 3)) ρ _ B _ hI rfl hface
    have hright := restrictedType_eval (intervalContext (.var (0 : Fin 5)))
      (subTy (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0)))
      (intervalFace (.var 0) (.var 3)) ρ _ _ _ hI hBconst hface
    exact hleft.trans ((congrArg (Value.family _) hc).trans hright.symm)

end SquareKit.Cubical.Source.Fillings

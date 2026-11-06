import SquareKit.Internal.Cubical.Judgments.FillingTermEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem transpSchema_inputs (out : Judgment (Fin 5)) (ρ : Fin 5 → Value.{u})
    (h : ∀ i, ((transpSchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ))) (F : Filling B)
      (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false))),
      F.Lawful ∧ RestrictedConstancy B φ ∧
      ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a] := by
  obtain ⟨Γ,φ,hΓ,hφ⟩ := h 1
  change ρ 0 = .context Γ at hΓ
  change ρ 3 = .cofibration Γ φ at hφ
  have hI := intervalContext_eval (.var (0 : Fin 5)) ρ Γ hΓ
  obtain ⟨Δ,B,F,hΔ,hB,hF,hFL⟩ := h 0
  change (intervalContext (.var 0)).eval algebra ρ = .context Δ at hΔ
  have he : Δ = total (Presheaf.interval Γ) := Value.context.inj (hΔ.symm.trans hI)
  subst Δ
  change ρ 1 = .family (total (Presheaf.interval Γ)) B at hB
  change ρ 2 = .filling (total (Presheaf.interval Γ)) B F at hF
  have hep := endpointSub_eval (.var (0 : Fin 5)) ρ Γ hΓ false
  have hB0 := subTy_eval (.var 1) (endpointSub (.var 0) false) ρ _ _ B _ hB hep
  have ha := h 2
  change Source.predicate .term ![ρ 0,(subTy (.var 1) (endpointSub (.var 0) false)).eval algebra ρ,ρ 4] at ha
  rw [hΓ,hB0] at ha
  obtain ⟨a,ha⟩ := Value.term_input _ _ _ ha
  have hp := projection_eval (.var (0 : Fin 5)) ρ Γ hΓ
  have hBconst := subTy_eval (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0))
    ρ _ _ _ _ hB0 hp
  have hface := intervalFace_eval (.var (0 : Fin 5)) (.var 3) ρ Γ φ hΓ hφ
  have hleft := restrictedType_eval (intervalContext (.var (0 : Fin 5))) (.var 1)
    (intervalFace (.var 0) (.var 3)) ρ _ B _ hI hB hface
  have hright := restrictedType_eval (intervalContext (.var (0 : Fin 5)))
    (subTy (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0)))
    (intervalFace (.var 0) (.var 3)) ρ _ _ _ hI hBconst hface
  have hc := h 3
  change (subTy (.var 1) (inclusion (intervalContext (.var 0)) (intervalFace (.var 0) (.var 3)))).eval algebra ρ =
    (subTy (subTy (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0)))
      (inclusion (intervalContext (.var 0)) (intervalFace (.var 0) (.var 3)))).eval algebra ρ at hc
  rw [hleft,hright] at hc
  have hc' : RestrictedConstancy B φ := eq_of_heq (Value.family.inj hc).2
  refine ⟨Γ,B,F,φ,a,hFL,hc',?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hB | exact hF | exact hφ | exact ha

end SquareKit.Cubical.Source.Fillings

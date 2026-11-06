import SquareKit.Internal.Cubical.Judgments.FillingEvaluation
import SquareKit.Internal.Cubical.Judgments.FillingSubstitutionSyntax

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem faceTop_valid : Satisfies algebra.{u} faceTopRule := by
  intro ρ h
  obtain ⟨Γ,hΓ⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  exact ⟨Γ,Cofibration.top Γ,hΓ,by change extraOperation .faceTop ![ρ 0] = _; rw [hΓ]; rfl⟩

theorem faceBot_valid : Satisfies algebra.{u} faceBotRule := by
  intro ρ h
  obtain ⟨Γ,hΓ⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  exact ⟨Γ,Cofibration.bot Γ,hΓ,by change extraOperation .faceBot ![ρ 0] = _; rw [hΓ]; rfl⟩

theorem restriction_valid : Satisfies algebra.{u} restrictionRule := by
  intro ρ h
  obtain ⟨Γ,φ,hΓ,hφ⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .cofibration Γ φ at hφ
  refine ⟨restrictContext φ,?_⟩
  change extraOperation .restriction ![ρ 0,ρ 1] = _
  rw [hΓ,hφ,extra_restriction]

theorem inclusion_valid : Satisfies algebra.{u} inclusionRule := by
  intro ρ h
  obtain ⟨Γ,φ,hΓ,hφ⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .cofibration Γ φ at hφ
  refine ⟨restrictContext φ,Γ,restrictInclusion φ,?_,hΓ,?_⟩
  · change extraOperation .restriction ![ρ 0,ρ 1] = _
    rw [hΓ,hφ,extra_restriction]
  · change extraOperation .inclusion ![ρ 0,ρ 1] = _
    rw [hΓ,hφ,extra_inclusion]

theorem faceJoin_valid : Satisfies algebra.{u} faceJoinRule := by
  intro ρ h
  obtain ⟨Γ,φ,hΓ,hφ⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .cofibration Γ φ at hφ
  obtain ⟨Γ',ψ,hΓ',hψ⟩ := h 1
  change ρ 0 = .context Γ' at hΓ'
  change ρ 2 = .cofibration Γ' ψ at hψ
  have he : Γ' = Γ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  refine ⟨Γ,φ.join ψ,hΓ,?_⟩
  change extraOperation .faceJoin ![ρ 0,ρ 1,ρ 2] = _
  rw [hΓ,hφ,hψ,extra_faceJoin]

theorem faceSubSchema_inputs (out : Judgment (Fin 4)) (ρ : Fin 4 → Value.{u})
    (h : ∀ i, ((faceSubSchema out).premise i).eval algebra ρ) :
    ∃ (Γ Δ : Context.{u}) (φ : Cofibration Γ) (σ : Δ ⟶ Γ),
      ρ = ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ] := by
  obtain ⟨Γ,φ,hΓ,hφ⟩ := h 0
  change ρ 1 = .context Γ at hΓ
  change ρ 2 = .cofibration Γ φ at hφ
  obtain ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩ := h 1
  change ρ 0 = .context Δ at hΔ
  change ρ 1 = .context Γ' at hΓ'
  have he : Γ' = Γ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  change ρ 3 = .substitution Δ Γ σ at hσ
  refine ⟨Γ,Δ,φ,σ,?_⟩
  funext i
  fin_cases i <;> first | exact hΔ | exact hΓ | exact hφ | exact hσ

theorem faceSub_valid : Satisfies algebra.{u} faceSubRule := by
  intro ρ h
  obtain ⟨Γ,Δ,φ,σ,rfl⟩ := faceSubSchema_inputs _ ρ h
  exact ⟨Δ,φ.reindex σ,rfl,extra_subFace Γ Δ φ σ⟩

theorem restrictedSub_valid : Satisfies algebra.{u} restrictedSubRule := by
  intro ρ h
  obtain ⟨Γ,Δ,φ,σ,rfl⟩ := faceSubSchema_inputs _ ρ h
  refine ⟨restrictContext (φ.reindex σ),restrictContext φ,restrictSubstitution φ σ,?_,?_,?_⟩
  · change extraOperation .restriction ![.context Δ,
      extraOperation .subFace ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ]] = _
    rw [extra_subFace,extra_restriction]
  · exact extra_restriction Γ φ
  · exact extra_restrictedSub Γ Δ φ σ

theorem providerSub_valid : Satisfies algebra.{u} providerSubRule := by
  intro ρ h
  obtain ⟨Γ,A,F,hΓ,hA,hF,hFL⟩ := h 0
  change ρ 1 = .context Γ at hΓ
  change ρ 2 = .family Γ A at hA
  change ρ 3 = .filling Γ A F at hF
  obtain ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩ := h 1
  change ρ 0 = .context Δ at hΔ
  change ρ 1 = .context Γ' at hΓ'
  have he : Γ' = Γ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  change ρ 4 = .substitution Δ Γ σ at hσ
  refine ⟨Δ,reindex A σ,F.reindex σ,hΔ,?_,?_,hFL.reindex σ⟩
  · change Source.operation .subTy ![ρ 2,ρ 4] = _
    rw [hA,hσ]
    simp [Source.operation,Value.familyAt_family]
  · change extraOperation .subProvider ![ρ 0,ρ 1,ρ 3,ρ 4] = _
    rw [hΔ,hΓ,hF,hσ,extra_subProvider]

theorem faceEndpoint_valid (b : Bool) : Satisfies algebra.{u} (faceEndpointRule b) := by
  intro ρ h
  obtain ⟨Γ,A,r,hΓ,hA,hr⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  change Intervals.extraOperation .interval ![ρ 0] = .family Γ A at hA
  rw [hΓ,Intervals.extra_interval] at hA
  have he : A = Presheaf.interval Γ := (eq_of_heq (Value.family.inj hA).2).symm
  subst A
  change ρ 1 = .term Γ (Presheaf.interval Γ) r at hr
  refine ⟨Γ,Cofibration.endpoint r b,hΓ,?_⟩
  change extraOperation (.faceEndpoint b) ![ρ 0,ρ 1] = _
  rw [hΓ,hr,extra_faceEndpoint]

end SquareKit.Cubical.Source.Fillings

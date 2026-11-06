import SquareKit.Internal.Cubical.Judgments.FillingTermEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem hcompSchema_inputs (out : Judgment (Fin 6)) (ρ : Fin 6 → Value.{u})
    (h : ∀ i, ((hcompSchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
      (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ), F.Lawful ∧
      ρ = ![.context Γ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
        .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
          (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
            (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
        .term Γ A b.base] := by
  obtain ⟨Γ,A,F,hΓ,hA,hF,hFL⟩ := h 0
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .filling Γ A F at hF
  obtain ⟨Γ',φ,hΓ',hφ⟩ := h 1
  change ρ 0 = .context Γ' at hΓ'
  have he : Γ' = Γ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  change ρ 3 = .cofibration Γ φ at hφ
  have hI := intervalContext_eval (.var (0 : Fin 6)) ρ Γ hΓ
  have hp := projection_eval (.var (0 : Fin 6)) ρ Γ hΓ
  have hB := subTy_eval (.var 1) (projection (.var 0)) ρ _ _ A _ hA hp
  have hface := intervalFace_eval (.var (0 : Fin 6)) (.var 3) ρ Γ φ hΓ hφ
  obtain ⟨u,hu⟩ := restrictedTerm_input (intervalContext (.var (0 : Fin 6)))
    (subTy (.var 1) (projection (.var 0))) (intervalFace (.var 0) (.var 3)) (.var 4) ρ
    _ _ _ hI hB hface (h 2)
  change ρ 4 = .term _ _ u at hu
  have ha := h 3
  change Source.predicate .term ![ρ 0,ρ 1,ρ 5] at ha
  rw [hΓ,hA] at ha
  obtain ⟨a,ha⟩ := Value.term_input Γ A _ ha
  have hzero := tubeEndpoint_eval (.var (0 : Fin 6)) (.var 3) (.var 4) ρ Γ
    (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ u hΓ hφ hu false
  have hinc := inclusion_eval (.var (0 : Fin 6)) (.var 3) ρ Γ φ hΓ hφ
  have hbase := subTm_eval (.var 5) (inclusion (.var 0) (.var 3)) ρ Γ _ A a _ ha hinc
  have hc := h 4
  change (tubeEndpoint (.var 0) (.var 3) (.var 4) false).eval algebra ρ =
    (subTm (.var 5) (inclusion (.var 0) (.var 3))).eval algebra ρ at hc
  rw [hzero,hbase] at hc
  have heq : u.reindex (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ)))
      (Presheaf.endpointSub Γ false)) = a.reindex (restrictInclusion φ) :=
    eq_of_heq (Value.term.inj hc).2.2
  let b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ :=
    { tube := PartialSection.ofRestricted u
      base := a
      boundary := fun x hx => congrArg
        (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩)) heq }
  refine ⟨Γ,A,F,φ,b,hFL,?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hA | exact hF | exact hφ | exact hu | exact ha

end SquareKit.Cubical.Source.Fillings

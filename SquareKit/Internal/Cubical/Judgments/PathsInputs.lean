import SquareKit.Internal.Cubical.Judgments.PathsAlgebra

namespace SquareKit.Cubical.Source.Paths
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem formationSchema_inputs (out : Judgment (Fin 4)) (ρ : Fin 4 → Value.{u})
    (h : ∀ i, ((formationSchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))),
      ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁] := by
  rcases h 0 with ⟨Γ,hΓ⟩
  change ρ 0 = .context Γ at hΓ
  have hb := h 1
  change ∃ Δ B, Source.operation .extend ![ρ 0,Intervals.extraOperation .interval ![ρ 0]] = .context Δ ∧
    ρ 1 = .family Δ B at hb
  rw [hΓ,Intervals.extra_interval] at hb
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hb
  rcases hb with ⟨Δ,B,eΔ,hB⟩
  have he := Value.context.inj eΔ
  subst Δ
  have hep₀ := endpointSub_eval (.var (0 : Fin 4)) ρ Γ hΓ false
  have hep₁ := endpointSub_eval (.var (0 : Fin 4)) ρ Γ hΓ true
  have ha₀ := h 2
  change Source.predicate .term ![ρ 0,Source.operation .subTy ![ρ 1,(endpointSub (.var 0) false).eval algebra ρ],ρ 2] at ha₀
  rw [hΓ,hB,hep₀] at ha₀
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at ha₀
  obtain ⟨a₀,ha₀⟩ := Value.term_input Γ (reindex B (Presheaf.endpointSub Γ false)) _ ha₀
  have ha₁ := h 3
  change Source.predicate .term ![ρ 0,Source.operation .subTy ![ρ 1,(endpointSub (.var 0) true).eval algebra ρ],ρ 3] at ha₁
  rw [hΓ,hB,hep₁] at ha₁
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at ha₁
  obtain ⟨a₁,ha₁⟩ := Value.term_input Γ (reindex B (Presheaf.endpointSub Γ true)) _ ha₁
  refine ⟨Γ,B,a₀,a₁,?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hB | exact ha₀ | exact ha₁

theorem formationSchema_valid (out : Judgment (Fin 4))
    (valid : ∀ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))),
      out.eval algebra ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁]) :
    Satisfies algebra.{u} (formationSchema out) := by
  intro ρ h
  rcases formationSchema_inputs out ρ h with ⟨Γ,B,a₀,a₁,rfl⟩
  exact valid Γ B a₀ a₁

theorem bodySchema_inputs (out : Judgment (Fin 5)) (ρ : Fin 5 → Value.{u})
    (h : ∀ i, ((bodySchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true)))
      (b : Presheaf.Term B), b.reindex (Presheaf.endpointSub Γ false) = a₀ ∧
      b.reindex (Presheaf.endpointSub Γ true) = a₁ ∧
      ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b] := by
  have hp : ∀ i, formationRule.premise i |>.eval algebra (fun j => ρ (j.castAdd 1)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 4 < 7)⟩
    simpa only [bodySchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  rcases formationSchema_inputs _ _ hp with ⟨Γ,B,a₀,a₁,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 1 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have ha₀ : ρ 2 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ := congrFun e 2
  have ha₁ : ρ 3 = .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁ := congrFun e 3
  have hb := h 4
  change Source.predicate .term ![Source.operation .extend ![ρ 0,Intervals.extraOperation .interval ![ρ 0]],ρ 1,ρ 4] at hb
  rw [hΓ,hB,Intervals.extra_interval] at hb
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hb
  obtain ⟨b,hb⟩ := Value.term_input (total (Presheaf.interval Γ)) B _ hb
  have hep₀ := endpointSub_eval (.var (0 : Fin 5)) ρ Γ hΓ false
  have hep₁ := endpointSub_eval (.var (0 : Fin 5)) ρ Γ hΓ true
  have h₀ := h 5
  change Source.operation .subTm ![ρ 4,(endpointSub (.var 0) false).eval algebra ρ] = ρ 2 at h₀
  rw [hb,hep₀,ha₀] at h₀
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h₀
  have h₀' := eq_of_heq (Value.term.inj h₀).2.2
  have h₁ := h 6
  change Source.operation .subTm ![ρ 4,(endpointSub (.var 0) true).eval algebra ρ] = ρ 3 at h₁
  rw [hb,hep₁,ha₁] at h₁
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h₁
  have h₁' := eq_of_heq (Value.term.inj h₁).2.2
  have he : ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hB | exact ha₀ | exact ha₁ | exact hb
  exact ⟨Γ,B,a₀,a₁,b,h₀',h₁',he⟩

theorem bodySchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))) (b : Presheaf.Term B),
      b.reindex (Presheaf.endpointSub Γ false) = a₀ →
      b.reindex (Presheaf.endpointSub Γ true) = a₁ →
      out.eval algebra ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b]) :
    Satisfies algebra.{u} (bodySchema out) := by
  intro ρ h
  rcases bodySchema_inputs out ρ h with ⟨Γ,B,a₀,a₁,b,h₀,h₁,rfl⟩
  exact valid Γ B a₀ a₁ b h₀ h₁

theorem functionSchema_inputs (out : Judgment (Fin 5)) (ρ : Fin 5 → Value.{u})
    (h : ∀ i, ((functionSchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true)))
      (p : Presheaf.Term (normalizedPath B a₀ a₁)),
      ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p] := by
  have hp : ∀ i, formationRule.premise i |>.eval algebra (fun j => ρ (j.castAdd 1)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 4 < 5)⟩
    simpa only [functionSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  rcases formationSchema_inputs _ _ hp with ⟨Γ,B,a₀,a₁,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 1 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have ha₀ : ρ 2 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ := congrFun e 2
  have ha₁ : ρ 3 = .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁ := congrFun e 3
  have hp := h 4
  change Source.predicate .term ![ρ 0,extraOperation .path ![ρ 0,ρ 1,ρ 2,ρ 3],ρ 4] at hp
  rw [hΓ,hB,ha₀,ha₁,extra_path] at hp
  obtain ⟨p,hp⟩ := Value.term_input Γ (normalizedPath B a₀ a₁) _ hp
  have he : ρ = ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hB | exact ha₀ | exact ha₁ | exact hp
  exact ⟨Γ,B,a₀,a₁,p,he⟩

theorem functionSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))) (p : Presheaf.Term (normalizedPath B a₀ a₁)),
      out.eval algebra ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p]) :
    Satisfies algebra.{u} (functionSchema out) := by
  intro ρ h
  rcases functionSchema_inputs out ρ h with ⟨Γ,B,a₀,a₁,p,rfl⟩
  exact valid Γ B a₀ a₁ p

end SquareKit.Cubical.Source.Paths

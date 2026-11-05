import SquareKit.Internal.Cubical.Judgments.PathsInputs

namespace SquareKit.Cubical.Source.Paths
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem substitutionSchema_valid (out : Judgment (Fin 6))
    (valid : ∀ (Γ Δ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))) (σ : Δ ⟶ Γ),
      out.eval algebra ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (substitutionSchema out) := by
  intro ρ h
  have hp : ∀ i, (formationRule.premise i).eval algebra (fun j => ρ (![0,2,3,4] j)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 4 < 5)⟩
    simpa only [substitutionSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  rcases formationSchema_inputs _ _ hp with ⟨Γ,B,a₀,a₁,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 2 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have ha₀ : ρ 3 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ := congrFun e 2
  have ha₁ : ρ 4 = .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁ := congrFun e 3
  have hσ := h 4
  change Source.predicate .substitution ![ρ 1,ρ 0,ρ 5] at hσ
  rcases hσ with ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hB | exact ha₀ | exact ha₁ | exact hσ
  subst ρ
  exact valid Γ Δ B a₀ a₁ σ

theorem bodySubstitutionSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ (Γ Δ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))) (b : Presheaf.Term B) (σ : Δ ⟶ Γ),
      b.reindex (Presheaf.endpointSub Γ false) = a₀ →
      b.reindex (Presheaf.endpointSub Γ true) = a₁ →
      out.eval algebra ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (bodySubstitutionSchema out) := by
  intro ρ h
  have hp : ∀ i, (lamRule.premise i).eval algebra (fun j => ρ (![0,2,3,4,5] j)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 7 < 8)⟩
    simpa only [bodySubstitutionSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  rcases bodySchema_inputs _ _ hp with ⟨Γ,B,a₀,a₁,b,h₀,h₁,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 2 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have ha₀ : ρ 3 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ := congrFun e 2
  have ha₁ : ρ 4 = .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁ := congrFun e 3
  have ht : ρ 5 = .term (total (Presheaf.interval Γ)) B b := congrFun e 4
  have hσ := h 7
  change Source.predicate .substitution ![ρ 1,ρ 0,ρ 6] at hσ
  rcases hσ with ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hB | exact ha₀ | exact ha₁ | exact ht | exact hσ
  subst ρ
  exact valid Γ Δ B a₀ a₁ b σ h₀ h₁

theorem functionSubstitutionSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ (Γ Δ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
      (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
      (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true))) (p : Presheaf.Term (normalizedPath B a₀ a₁)) (σ : Δ ⟶ Γ),
      out.eval algebra ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
        .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (functionSubstitutionSchema out) := by
  intro ρ h
  have hp : ∀ i, (appRule.premise i).eval algebra (fun j => ρ (![0,2,3,4,5] j)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 5 < 6)⟩
    simpa only [functionSubstitutionSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  rcases functionSchema_inputs _ _ hp with ⟨Γ,B,a₀,a₁,p,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 2 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have ha₀ : ρ 3 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ := congrFun e 2
  have ha₁ : ρ 4 = .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁ := congrFun e 3
  have ht : ρ 5 = .term Γ (normalizedPath B a₀ a₁) p := congrFun e 4
  have hσ := h 5
  change Source.predicate .substitution ![ρ 1,ρ 0,ρ 6] at hσ
  rcases hσ with ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hB | exact ha₀ | exact ha₁ | exact ht | exact hσ
  subst ρ
  exact valid Γ Δ B a₀ a₁ p σ

end SquareKit.Cubical.Source.Paths

import SquareKit.Internal.Cubical.Judgments.NaturalsAlgebra

namespace SquareKit.Cubical.Source.Naturals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem contextSchema_valid (out : Judgment (Fin 1))
    (valid : ∀ (Γ : Context.{u}), out.eval algebra ![.context Γ]) :
    Satisfies algebra.{u} (contextSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,hΓ⟩
  have he : ρ = ![.context Γ] := by funext i; fin_cases i; exact hΓ
  subst ρ
  exact valid Γ

theorem successorSchema_valid (out : Judgment (Fin 2))
    (valid : ∀ (Γ : Context.{u}) (n : Presheaf.Term (natFamily Γ)),
      out.eval algebra ![.context Γ,.term Γ (natFamily Γ) n]) :
    Satisfies algebra.{u} (successorSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,hΓ⟩
  change ρ 0 = .context Γ at hΓ
  have hn := h 1
  change Source.predicate .term ![ρ 0,extraOperation .nat ![ρ 0],ρ 1] at hn
  rw [hΓ,extra_nat] at hn
  obtain ⟨n,hn⟩ := Value.term_input Γ (natFamily Γ) _ hn
  have he : ρ = ![.context Γ,.term Γ (natFamily Γ) n] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hn
  subst ρ
  exact valid Γ n

theorem eliminationSchema_valid (out : Judgment (Fin 4))
    (valid : ∀ (Γ : Context.{u}) (B : Family (total (natFamily Γ)))
      (z : Presheaf.Term (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ)))) (s : NatStepTerm B),
      out.eval algebra ![.context Γ,.family (total (natFamily Γ)) B,
        .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
        .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s]) :
    Satisfies algebra.{u} (eliminationSchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,hΓ⟩
  change ρ 0 = .context Γ at hΓ
  have hb := h 1
  change ∃ Δ B, Source.operation .extend ![ρ 0,extraOperation .nat ![ρ 0]] = .context Δ ∧
    ρ 1 = .family Δ B at hb
  rw [hΓ,extra_nat] at hb
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hb
  rcases hb with ⟨Δ,B,eΔ,hB⟩
  have he := Value.context.inj eΔ
  subst Δ
  have hzsub := zeroSub_eval (.var (0 : Fin 4)) ρ Γ hΓ
  have hssub := successorSub_eval (.var (0 : Fin 4)) ρ Γ hΓ
  have hz := h 2
  change Source.predicate .term ![ρ 0,Source.operation .subTy ![ρ 1,(zeroSub (.var 0)).eval algebra ρ],ρ 2] at hz
  rw [hΓ,hB,hzsub] at hz
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family] at hz
  obtain ⟨z,hz⟩ := Value.term_input Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) _ hz
  have hs := h 3
  change Source.predicate .term ![Source.operation .extend ![Source.operation .extend ![ρ 0,extraOperation .nat ![ρ 0]],ρ 1],
    Source.operation .subTy ![ρ 1,Source.operation .comp ![(successorSub (.var 0)).eval algebra ρ,
      Source.operation .weaken ![Source.operation .extend ![ρ 0,extraOperation .nat ![ρ 0]],ρ 1]]],ρ 3] at hs
  rw [hΓ,hB,hssub,extra_nat] at hs
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.familyAt_family,Value.substitutionAt_substitution] at hs
  obtain ⟨s,hs⟩ := Value.term_input (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) _ hs
  have he : ρ = ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hB | exact hz | exact hs
  subst ρ
  exact valid Γ B z s

end SquareKit.Cubical.Source.Naturals

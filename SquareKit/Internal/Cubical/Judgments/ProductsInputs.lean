import SquareKit.Internal.Cubical.Judgments.ProductsAlgebra

/-! Inversion of the independently specified Π source guards recovers arbitrary
dependent semantic inputs. These are model-builder proofs, not author premises. -/
namespace SquareKit.Cubical.Source.Products
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem formationSchema_inputs (out : Judgment (Fin 3)) (ρ : Fin 3 → Value.{u})
    (h : ∀ i, ((formationSchema out).premise i).eval algebra ρ) :
    ∃ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)),
      ρ = ![.context Γ, .family Γ A, .family (total A) B] := by
  rcases h 0 with ⟨Γ,A,hΓ,hA⟩
  have hb := h 1
  change ∃ Δ B, Source.operation .extend ![ρ 0,ρ 1] = .context Δ ∧ ρ 2 = .family Δ B at hb
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  simp only [hΓ,hA,Source.operation, Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.familyAt_family] at hb
  rcases hb with ⟨Δ,B,eΔ,hB⟩
  have he := Value.context.inj eΔ
  subst Δ
  refine ⟨Γ,A,B,?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hA | exact hB

theorem formationSchema_valid (out : Judgment (Fin 3))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)),
      out.eval algebra ![.context Γ,.family Γ A,.family (total A) B]) :
    Satisfies algebra.{u} (formationSchema out) := by
  intro ρ h
  rcases formationSchema_inputs out ρ h with ⟨Γ,A,B,rfl⟩
  exact valid Γ A B

theorem bodySchema_valid (out : Judgment (Fin 4))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A)) (b : Presheaf.Term B),
      out.eval algebra ![.context Γ,.family Γ A,.family (total A) B,.term (total A) B b]) :
    Satisfies algebra.{u} (bodySchema out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,A,hΓ,hA⟩
  have hb := h 1
  change ∃ Δ B b, Source.operation .extend ![ρ 0,ρ 1] = .context Δ ∧
    ρ 2 = .family Δ B ∧ ρ 3 = .term Δ B b at hb
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  simp only [hΓ,hA,Source.operation, Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.familyAt_family] at hb
  rcases hb with ⟨Δ,B,b,eΔ,hB,hb⟩
  have he := Value.context.inj eΔ
  subst Δ
  have e : ρ = ![.context Γ,.family Γ A,.family (total A) B,.term (total A) B b] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hb
  subst ρ
  exact valid Γ A B b

theorem functionSchema_valid (out : Judgment (Fin 4))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (B : Family (total A))
      (p : Presheaf.Term (normalizedPi A B)),
      out.eval algebra ![.context Γ,.family Γ A,.family (total A) B,.term Γ (normalizedPi A B) p]) :
    Satisfies algebra.{u} (functionSchema out) := by
  intro ρ h
  have hf : ∀ i, (formationRule.premise i).eval algebra (fun j => ρ (j.castAdd 1)) := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs _ _ hf with ⟨Γ,A,B,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hA : ρ 1 = .family Γ A := congrFun e 1
  have hB : ρ 2 = .family (total A) B := congrFun e 2
  have hp := h 2
  change ∃ Δ C p, ρ 0 = .context Δ ∧ extraOperation .pi ![ρ 1,ρ 2] = .family Δ C ∧
    ρ 3 = .term Δ C p at hp
  simp only [hΓ,hA,hB,extra_pi] at hp
  rcases hp with ⟨Δ,C,p,eΓ,eC,hp⟩
  have he := Value.context.inj eΓ
  subst Δ
  have hc := eq_of_heq (Value.family.inj eC).2
  subst C
  have he : ρ = ![.context Γ,.family Γ A,.family (total A) B,.term Γ (normalizedPi A B) p] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hp
  subst ρ
  exact valid Γ A B p

theorem substitutionSchema_inputs (out : Judgment (Fin 5)) (ρ : Fin 5 → Value.{u})
    (h : ∀ i, ((substitutionSchema out).premise i).eval algebra ρ) :
    ∃ (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ),
      ρ = ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ] := by
  have hf : ∀ i, (formationRule.premise i).eval algebra (fun j => ρ (![0,2,3] j)) := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs _ _ hf with ⟨Γ,A,B,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hA : ρ 2 = .family Γ A := congrFun e 1
  have hB : ρ 3 = .family (total A) B := congrFun e 2
  rcases h 2 with ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hB | exact hσ
  exact ⟨Γ,Δ,A,B,σ,he⟩

theorem substitutionSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ),
      out.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (substitutionSchema out) := by
  intro ρ h
  rcases substitutionSchema_inputs out ρ h with ⟨Γ,Δ,A,B,σ,rfl⟩
  exact valid Γ Δ A B σ

theorem lamSubSchema_valid (out : Judgment (Fin 6))
    (valid : ∀ (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A))
      (σ : Δ ⟶ Γ) (t : Presheaf.Term (B)),
      out.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
        .term (total A) (B) t,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (lamSubSchema out) := by
  intro ρ h
  have hs : ∀ i, (piSubRule.premise i).eval algebra (fun j => ρ (![0,1,2,3,5] j)) := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2
  rcases substitutionSchema_inputs _ _ hs with ⟨Γ,Δ,A,B,σ,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hΔ : ρ 1 = .context Δ := congrFun e 1
  have hA : ρ 2 = .family Γ A := congrFun e 2
  have hB : ρ 3 = .family (total A) B := congrFun e 3
  have hσ : ρ 5 = .substitution Δ Γ σ := congrFun e 4
  have ht := h 3
  change Source.predicate .term ![Source.operation .extend ![ρ 0,ρ 2],ρ 3,ρ 4] at ht
  simp only [hΓ,hA,hB,Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.familyAt_family] at ht
  obtain ⟨t,ht⟩ := Value.term_input (total A) (B) (ρ 4) ht
  have he : ρ = ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
      .term (total A) (B) t,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hB | exact ht | exact hσ
  subst ρ
  exact valid Γ Δ A B σ t

theorem appSubSchema_valid (out : Judgment (Fin 6))
    (valid : ∀ (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A))
      (σ : Δ ⟶ Γ) (t : Presheaf.Term (normalizedPi A B)),
      out.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
        .term (Γ) (normalizedPi A B) t,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (appSubSchema out) := by
  intro ρ h
  have hs : ∀ i, (piSubRule.premise i).eval algebra (fun j => ρ (![0,1,2,3,5] j)) := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2
  rcases substitutionSchema_inputs _ _ hs with ⟨Γ,Δ,A,B,σ,e⟩
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hΔ : ρ 1 = .context Δ := congrFun e 1
  have hA : ρ 2 = .family Γ A := congrFun e 2
  have hB : ρ 3 = .family (total A) B := congrFun e 3
  have hσ : ρ 5 = .substitution Δ Γ σ := congrFun e 4
  have ht := h 3
  change Source.predicate .term ![ρ 0,extraOperation .pi ![ρ 2,ρ 3],ρ 4] at ht
  simp only [hΓ,hA,hB,extra_pi] at ht
  obtain ⟨t,ht⟩ := Value.term_input (Γ) (normalizedPi A B) (ρ 4) ht
  have he : ρ = ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
      .term (Γ) (normalizedPi A B) t,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hB | exact ht | exact hσ
  subst ρ
  exact valid Γ Δ A B σ t

end SquareKit.Cubical.Source.Products

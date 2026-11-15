import SquareKit.Internal.Cubical.Judgments.IntervalsAlgebra

namespace SquareKit.Cubical.Source.Intervals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

theorem formation_valid : Satisfies algebra.{u} formationRule := by
  intro ρ h
  rcases h 0 with ⟨Γ,hΓ⟩
  change ρ 0 = .context Γ at hΓ
  refine ⟨Γ,Presheaf.interval Γ,hΓ,?_⟩
  change extraOperation .interval ![ρ 0] = _
  rw [hΓ,extra_interval]

theorem dimension_valid {n : ℕ} (e : Expr (Fin n)) : Satisfies algebra.{u} (dimensionRule e) := by
  apply dimensionSchema_valid
  intro Γ r
  exact ⟨Γ,Presheaf.interval Γ,intervalDimension e r,rfl,rfl,extra_dimension Γ e r⟩

theorem variable_valid {n : ℕ} (k : Fin n) : Satisfies algebra.{u} (variableRule k) := by
  apply dimensionSchema_valid
  intro Γ r
  change extraOperation (.dimension (.var k)) (Matrix.vecCons (.context Γ)
    (fun i => .term Γ (Presheaf.interval Γ) (r i))) = .term Γ (Presheaf.interval Γ) (r k)
  rw [extra_dimension,intervalDimension_var]

theorem conversion_valid {n : ℕ} {e e' : Expr (Fin n)} (h : Expr.Conv e e') :
    Satisfies algebra.{u} (conversionRule e e') := by
  apply dimensionSchema_valid
  intro Γ r
  change extraOperation (.dimension e) (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i))) =
    extraOperation (.dimension e') (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i)))
  rw [extra_dimension,extra_dimension,intervalDimension_congr h]

theorem composition_valid {m n : ℕ} (e : Expr (Fin m)) (σ : Fin m → Expr (Fin n)) :
    Satisfies algebra.{u} (compositionRule e σ) := by
  apply dimensionSchema_valid
  intro Γ r
  change extraOperation (.dimension (Expr.subst σ e))
    (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i))) =
    extraOperation (.dimension e) (Matrix.vecCons (.context Γ)
      (fun k => extraOperation (.dimension (σ k)) (Matrix.vecCons (.context Γ)
        (fun i => .term Γ (Presheaf.interval Γ) (r i)))))
  have h : (fun k => extraOperation (.dimension (σ k)) (Matrix.vecCons (.context Γ)
      (fun i => .term Γ (Presheaf.interval Γ) (r i)))) =
      (fun k => Value.term Γ (Presheaf.interval Γ) (intervalDimension (σ k) r)) :=
    funext (fun k => extra_dimension Γ (σ k) r)
  rw [h,extra_dimension,extra_dimension,intervalDimension_subst]

theorem intervalSub_valid : Satisfies algebra.{u} intervalSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ σ r
  change Source.operation .subTy ![extraOperation .interval ![.context Γ],.substitution Δ Γ σ] =
    extraOperation .interval ![.context Δ]
  rw [extra_interval,extra_interval]
  simp [Source.operation]

theorem dimensionSub_valid {n : ℕ} (e : Expr (Fin n)) : Satisfies algebra.{u} (dimensionSubRule e) := by
  apply substitutionSchema_valid
  intro Γ Δ σ r
  change Source.operation .subTm ![extraOperation (.dimension e)
      (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i))),.substitution Δ Γ σ] =
    extraOperation (.dimension e) (Matrix.vecCons (.context Δ)
      (fun i => Source.operation .subTm ![.term Γ (Presheaf.interval Γ) (r i),.substitution Δ Γ σ]))
  rw [extra_dimension]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  exact (extra_dimension Δ e (fun i => (r i).reindex σ)).symm

end SquareKit.Cubical.Source.Intervals

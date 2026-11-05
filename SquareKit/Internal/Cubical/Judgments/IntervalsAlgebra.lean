import SquareKit.Internal.Cubical.Judgments.IntervalsSyntax
import SquareKit.Internal.Cubical.Judgments.NaturalsTheory
import SquareKit.Internal.Cubical.DimensionEvaluation

namespace SquareKit.Cubical.Source.Intervals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def termsAt {n : ℕ} (Γ : Context.{u}) (A : Family Γ)
    (args : Fin n → Value.{u}) : Option (Fin n → Presheaf.Term A) := by
  classical
  exact if h : ∀ i, ∃ t, (args i).termAt Γ A = some t then
    some (fun i => Classical.choose (h i)) else none

@[simp] theorem termsAt_terms {n : ℕ} (Γ : Context.{u}) (A : Family Γ)
    (r : Fin n → Presheaf.Term A) :
    termsAt Γ A (fun i => .term Γ A (r i)) = some r := by
  classical
  have h : ∀ i, ∃ t, Value.termAt Γ A (.term Γ A (r i)) = some t :=
    fun i => ⟨r i,Value.termAt_term _ _ _⟩
  rw [termsAt,dite_eq_left h]
  congr 1
  funext i
  exact (Option.some.inj ((Value.termAt_term Γ A (r i)).symm.trans (Classical.choose_spec (h i)))).symm

noncomputable def extraOperation (op : Operation)
    (args : Fin (extraSignature.arity op) → Value.{u}) : Value.{u} :=
  match args ⟨0, by cases op <;> simp⟩ with
  | .context Γ => match op with
    | .interval => .family Γ (Presheaf.interval Γ)
    | .dimension e => match termsAt Γ (Presheaf.interval Γ) (fun i => args i.succ) with
      | some r => .term Γ (Presheaf.interval Γ) (intervalDimension e r)
      | none => .invalid
  | _ => .invalid

@[simp] theorem extra_interval (Γ : Context.{u}) :
    extraOperation .interval ![.context Γ] = .family Γ (Presheaf.interval Γ) := rfl

@[simp] theorem extra_dimension {n : ℕ} (Γ : Context.{u}) (e : Expr (Fin n))
    (r : Fin n → Presheaf.Term (Presheaf.interval Γ)) :
    extraOperation (.dimension e) (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i))) =
      .term Γ (Presheaf.interval Γ) (intervalDimension e r) := by
  simp only [extraOperation,Matrix.cons_val_zero',Matrix.cons_val_succ,termsAt_terms]

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation
    | .inl op => Naturals.algebra.operation op
    | .inr op => extraOperation op
  predicate
    | .inl p => Naturals.algebra.predicate p
    | .inr p => nomatch p

theorem dimensionSchema_valid (n : ℕ) (out : Judgment (Fin (n+1)))
    (valid : ∀ (Γ : Context.{u}) (r : Fin n → Presheaf.Term (Presheaf.interval Γ)),
      out.eval algebra (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i)))) :
    Satisfies algebra.{u} (dimensionSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ,hΓ⟩
  change ρ 0 = .context Γ at hΓ
  have hr : ∀ i : Fin n, ∃ t : Presheaf.Term (Presheaf.interval Γ),
      ρ i.succ = .term Γ (Presheaf.interval Γ) t := by
    intro i
    have hi := h i.succ
    change Source.predicate .term ![ρ 0,extraOperation .interval ![ρ 0],ρ i.succ] at hi
    rw [hΓ,extra_interval] at hi
    exact Value.term_input Γ (Presheaf.interval Γ) _ hi
  choose r hr using hr
  have he : ρ = Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) (r i)) := by
    funext i
    refine Fin.cases hΓ (fun i => hr i) i
  subst ρ
  exact valid Γ r

theorem substitutionSchema_valid (n : ℕ) (out : Judgment (Fin (n+3)))
    (valid : ∀ (Γ Δ : Context.{u}) (σ : Δ ⟶ Γ) (r : Fin n → Presheaf.Term (Presheaf.interval Γ)),
      out.eval algebra (Matrix.vecCons (.context Γ) (Matrix.vecCons (.context Δ)
        (Matrix.vecCons (.substitution Δ Γ σ) (fun i => .term Γ (Presheaf.interval Γ) (r i)))))) :
    Satisfies algebra.{u} (substitutionSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Δ,Γ,σ,hΔ,hΓ,hσ⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .context Δ at hΔ
  change ρ 2 = .substitution Δ Γ σ at hσ
  have hr : ∀ i : Fin n, ∃ t : Presheaf.Term (Presheaf.interval Γ),
      ρ i.succ.succ.succ = .term Γ (Presheaf.interval Γ) t := by
    intro i
    have hi := h i.succ
    change Source.predicate .term ![ρ 0,extraOperation .interval ![ρ 0],ρ i.succ.succ.succ] at hi
    rw [hΓ,extra_interval] at hi
    exact Value.term_input Γ (Presheaf.interval Γ) _ hi
  choose r hr using hr
  have he : ρ = Matrix.vecCons (.context Γ) (Matrix.vecCons (.context Δ)
      (Matrix.vecCons (.substitution Δ Γ σ) (fun i => .term Γ (Presheaf.interval Γ) (r i)))) := by
    funext i
    refine Fin.cases hΓ (fun i => ?_) i
    refine Fin.cases hΔ (fun i => ?_) i
    exact Fin.cases hσ (fun i => hr i) i
  subst ρ
  exact valid Γ Δ σ r

end SquareKit.Cubical.Source.Intervals

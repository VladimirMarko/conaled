import SquareKit.Internal.Cubical.PathConversion
import SquareKit.Internal.DependentJudgments.Comprehension

/-! Concrete presheaf operations used by the annotation-free source algebra.
No identity eliminator or unrelated model capability is assumed. -/
namespace SquareKit.Cubical.Source.Semantics
open CategoryTheory
universe u
abbrev Context := SquareKit.Cubical.Presheaf.Context.{u}
abbrev Family := SquareKit.Cubical.Presheaf.Family.{u}
abbrev Section (Γ : Context) (A : Family Γ) := SquareKit.Cubical.Presheaf.Term A
abbrev Substitution (Δ Γ : Context) := Δ ⟶ Γ
abbrev empty : Context := SquareKit.Cubical.Presheaf.terminal
abbrev extend (Γ : Context) (A : Family Γ) := SquareKit.Cubical.Presheaf.total A
abbrev idSub (Γ : Context) : Substitution Γ Γ := 𝟙 Γ
abbrev compSub {Γ Δ Θ : Context} (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) := τ ≫ σ
abbrev subTy {Γ Δ : Context} (A : Family Γ) (σ : Substitution Δ Γ) := SquareKit.Cubical.Presheaf.reindex A σ
abbrev subTm {Γ Δ : Context} {A : Family Γ} (t : Section Γ A) (σ : Substitution Δ Γ) := t.reindex σ
abbrev weaken (Γ : Context) (A : Family Γ) := SquareKit.Cubical.Presheaf.projection A
abbrev genericVariable (Γ : Context) (A : Family Γ) := SquareKit.Cubical.Presheaf.generic A
abbrev pairSub {Γ Δ : Context} (A : Family Γ) (σ : Substitution Δ Γ)
    (t : Section Δ (subTy A σ)) := SquareKit.Cubical.Presheaf.pair σ t

theorem weaken_pair {Γ Δ : Context} (A : Family Γ) (σ : Substitution Δ Γ)
    (t : Section Δ (subTy A σ)) : compSub (weaken Γ A) (pairSub A σ t) = σ :=
  SquareKit.Cubical.Presheaf.pair_projection σ t

theorem variable_pair {Γ Δ : Context} (A : Family Γ) (σ : Substitution Δ Γ)
    (t : Section Δ (subTy A σ)) : HEq (subTm (genericVariable Γ A) (pairSub A σ t)) t :=
  heq_of_eq (SquareKit.Cubical.Presheaf.generic_pair σ t)
theorem subTy_comp {Γ Δ Θ : Context} (A : Family Γ) (σ : Substitution Δ Γ)
    (τ : Substitution Θ Δ) : subTy (subTy A σ) τ = subTy A (compSub σ τ) := rfl
theorem comp_id_left {Γ Δ : Context} (σ : Substitution Δ Γ) : compSub (idSub Γ) σ = σ :=
  Category.comp_id σ
theorem comp_id_right {Γ Δ : Context} (σ : Substitution Δ Γ) : compSub σ (idSub Δ) = σ :=
  Category.id_comp σ
theorem comp_assoc {Γ Δ Θ Ξ : Context} (σ : Substitution Δ Γ) (τ : Substitution Θ Δ)
    (υ : Substitution Ξ Θ) : compSub (compSub σ τ) υ = compSub σ (compSub τ υ) :=
  (Category.assoc υ τ σ).symm
theorem subTy_id {Γ : Context} (A : Family Γ) : subTy A (idSub Γ) = A := rfl
theorem subTm_id {Γ : Context} {A : Family Γ} (t : Section Γ A) : HEq (subTm t (idSub Γ)) t :=
  heq_of_eq (SquareKit.Cubical.Presheaf.Term.reindex_id t)
theorem subTm_comp {Γ Δ Θ : Context} {A : Family Γ} (t : Section Γ A)
    (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) :
    HEq (subTm (subTm t σ) τ) (subTm t (compSub σ τ)) := HEq.rfl
end SquareKit.Cubical.Source.Semantics

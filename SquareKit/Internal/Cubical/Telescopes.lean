import SquareKit.Internal.Cubical.Conversion

/-! Finite dependent tails and their actual substitutions. Iterated normalized
products abstract every tail variable without changing the result fiber. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

inductive Telescope : Context.{u} → Type (u+1) where
  | nil (Γ : Context.{u}) : Telescope Γ
  | cons {Γ : Context.{u}} (A : Family Γ) (T : Telescope (total A)) : Telescope Γ

namespace Telescope

def context {Γ : Context.{u}} : Telescope Γ → Context.{u}
  | .nil Γ => Γ
  | .cons _ T => T.context

def reindex {Γ Δ : Context.{u}} (T : Telescope Γ) (σ : Δ ⟶ Γ) : Telescope Δ :=
  match T with
  | .nil _ => .nil Δ
  | .cons A T => .cons (Presheaf.reindex A σ) (T.reindex (liftSub A σ))

def map {Γ Δ : Context.{u}} (T : Telescope Γ) (σ : Δ ⟶ Γ) : (T.reindex σ).context ⟶ T.context :=
  match T with
  | .nil _ => σ
  | .cons A T => T.map (liftSub A σ)

def pi {Γ : Context.{u}} (T : Telescope Γ) (C : Family T.context) : Family Γ :=
  match T with
  | .nil _ => C
  | .cons A T => normalizedPi A (T.pi C)

def abstract {Γ : Context.{u}} (T : Telescope Γ) {C : Family T.context} (d : Term C) : Term (T.pi C) :=
  match T with
  | .nil _ => d
  | .cons _ T => normalizedLam (T.abstract d)

def apply {Γ : Context.{u}} (T : Telescope Γ) {C : Family T.context} (d : Term (T.pi C)) : Term C :=
  match T with
  | .nil _ => d
  | .cons _ T => T.apply (normalizedApp d)

theorem apply_abstract {Γ : Context.{u}} (T : Telescope Γ) {C : Family T.context} (d : Term C) :
    T.apply (T.abstract d) = d := by
  induction T with
  | nil => rfl
  | cons A T ih =>
    exact (congrArg T.apply (normalizedApp_lam (T.abstract d))).trans (ih d)

theorem abstract_apply {Γ : Context.{u}} (T : Telescope Γ) {C : Family T.context} (d : Term (T.pi C)) :
    T.abstract (T.apply d) = d := by
  induction T with
  | nil => rfl
  | cons A T ih =>
    exact (congrArg normalizedLam (ih (normalizedApp d))).trans (normalizedLam_app d)

theorem pi_reindex {Γ Δ : Context.{u}} (T : Telescope Γ) (C : Family T.context) (σ : Δ ⟶ Γ) :
    Presheaf.reindex (T.pi C) σ = (T.reindex σ).pi (Presheaf.reindex C (T.map σ)) := by
  induction T generalizing Δ with
  | nil => rfl
  | cons A T ih =>
    exact (normalizedPi_reindex A (T.pi C) σ).trans
      (congrArg (normalizedPi (Presheaf.reindex A σ)) (ih C (liftSub A σ)))

theorem normalizedLam_convert {Γ : Context.{u}} {A : Family Γ} {B C : Family (total A)}
    (h : B = C) (d : Term B) :
    normalizedLam (d.convert h) = (normalizedLam d).convert (congrArg (normalizedPi A) h) := by
  cases h
  rfl

theorem abstract_reindex {Γ Δ : Context.{u}} (T : Telescope Γ) {C : Family T.context}
    (d : Term C) (σ : Δ ⟶ Γ) :
    ((T.abstract d).reindex σ).convert (T.pi_reindex C σ) =
      (T.reindex σ).abstract (d.reindex (T.map σ)) := by
  induction T generalizing Δ with
  | nil => rfl
  | cons A T ih =>
    change ((normalizedLam (T.abstract d)).reindex σ).convert
      ((normalizedPi_reindex A (T.pi C) σ).trans
        (congrArg (normalizedPi (Presheaf.reindex A σ)) (T.pi_reindex C (liftSub A σ)))) = _
    rw [← Term.convert_trans (normalizedPi_reindex A (T.pi C) σ)
      (congrArg (normalizedPi (Presheaf.reindex A σ)) (T.pi_reindex C (liftSub A σ)))]
    rw [normalizedLam_reindex, ← normalizedLam_convert (T.pi_reindex C (liftSub A σ))]
    exact congrArg normalizedLam (ih d (liftSub A σ))

theorem abstract_injective {Γ : Context.{u}} (T : Telescope Γ) {C : Family T.context} :
    Function.Injective (T.abstract (C := C)) := by
  intro a b h
  exact (T.apply_abstract a).symm.trans ((congrArg T.apply h).trans (T.apply_abstract b))

theorem apply_reindex {Γ Δ : Context.{u}} (T : Telescope Γ) {C : Family T.context}
    (d : Term (T.pi C)) (σ : Δ ⟶ Γ) :
    (T.reindex σ).apply ((d.reindex σ).convert (T.pi_reindex C σ)) =
      (T.apply d).reindex (T.map σ) := by
  apply (T.reindex σ).abstract_injective
  rw [abstract_apply]
  have h := T.abstract_reindex (T.apply d) σ
  rw [abstract_apply] at h
  exact h

end Telescope
end SquareKit.Cubical.Presheaf

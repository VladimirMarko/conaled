import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Experimental dependent families as morphisms and terms as sections.
Substitution uses Mathlib pullbacks. Identity and composition hold through
canonical comparison isomorphisms; no strict split structure is asserted. -/
noncomputable section
namespace SquareKit.Family
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A Γ Δ Ξ T : C}

/-- A term of the family p is a global section of its display map. -/
abbrev Term (p : A ⟶ Γ) := {t : Γ ⟶ A // t ≫ p = 𝟙 Γ}

abbrev reindex (p : A ⟶ Γ) (σ : Δ ⟶ Γ) : pullback p σ ⟶ Δ := pullback.snd p σ
abbrev comparison (p : A ⟶ Γ) (σ : Δ ⟶ Γ) : pullback p σ ⟶ A := pullback.fst p σ

/-- Pair a base map with a dependent value satisfying its display equation. -/
def pair (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (a : T ⟶ A) (d : T ⟶ Δ)
    (h : a ≫ p = d ≫ σ) : T ⟶ pullback p σ := pullback.lift a d h

@[simp, reassoc] theorem pair_comparison (p : A ⟶ Γ) (σ : Δ ⟶ Γ)
    (a : T ⟶ A) (d : T ⟶ Δ) (h) : pair p σ a d h ≫ comparison p σ = a := by
  simp [pair]

@[simp, reassoc] theorem pair_reindex (p : A ⟶ Γ) (σ : Δ ⟶ Γ)
    (a : T ⟶ A) (d : T ⟶ Δ) (h) : pair p σ a d h ≫ reindex p σ = d := by
  simp [pair]

theorem pair_unique (p : A ⟶ Γ) (σ : Δ ⟶ Γ)
    (a : T ⟶ A) (d : T ⟶ Δ) (h) (k : T ⟶ pullback p σ)
    (ha : k ≫ comparison p σ = a) (hd : k ≫ reindex p σ = d) : k = pair p σ a d h := by
  apply pullback.hom_ext
  · simpa [pair] using ha
  · simpa [pair] using hd

/-- Pairing the two projections of any map recovers that map. -/
theorem pair_eta (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (k : T ⟶ pullback p σ) :
    pair p σ (k ≫ comparison p σ) (k ≫ reindex p σ)
      (by simp only [Category.assoc, pullback.condition]) = k :=
  (pair_unique p σ _ _ _ k rfl rfl).symm

/-- The generic variable is the diagonal section of p pulled back along p. -/
def variableTerm (p : A ⟶ Γ) : Term (reindex p p) :=
  ⟨pair p p (𝟙 A) (𝟙 A) rfl, by simp⟩

@[simp] theorem variable_comparison (p : A ⟶ Γ) :
    (variableTerm p).val ≫ comparison p p = 𝟙 A := by simp [variableTerm]

def termSub (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (t : Term p) : Term (reindex p σ) :=
  ⟨pair p σ (σ ≫ t.val) (𝟙 Δ) (by simp [t.property]), by simp⟩

@[simp, reassoc] theorem termSub_comparison (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (t : Term p) :
    (termSub p σ t).val ≫ comparison p σ = σ ≫ t.val := by simp [termSub]

@[simp] theorem termSub_section (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (t : Term p) :
    (termSub p σ t).val ≫ reindex p σ = 𝟙 Δ := (termSub p σ t).property

/-- A term over σ is equivalently a dependent value a with a ≫ p = σ. -/
def termEquiv (p : A ⟶ Γ) (σ : Δ ⟶ Γ) :
    Term (reindex p σ) ≃ {a : Δ ⟶ A // a ≫ p = σ} where
  toFun t := ⟨t.val ≫ comparison p σ, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, t.property, Category.id_comp]⟩
  invFun a := ⟨pair p σ a.val (𝟙 Δ) (by simpa using a.property), by simp⟩
  left_inv t := by apply Subtype.ext; apply pullback.hom_ext <;> simp [pair, t.property]
  right_inv a := by apply Subtype.ext; simp [pair]

/-- Identity substitution compares to the original total space over Γ. -/
def identityIso (p : A ⟶ Γ) : pullback p (𝟙 Γ) ≅ A where
  hom := comparison p (𝟙 Γ)
  inv := pair p (𝟙 Γ) (𝟙 A) p (by simp)
  hom_inv_id := by apply pullback.hom_ext <;> simp [pair, pullback.condition]
  inv_hom_id := by simp

@[simp] theorem identityIso_display (p : A ⟶ Γ) :
    (identityIso p).hom ≫ p = reindex p (𝟙 Γ) := by simp [identityIso, pullback.condition]

@[simp] theorem termSub_identity (p : A ⟶ Γ) (t : Term p) :
    (termSub p (𝟙 Γ) t).val ≫ (identityIso p).hom = t.val := by
  simp [identityIso]

/-- Iterated substitution compares to substitution by the composite. -/
def compositionIso (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    pullback (reindex p σ) τ ≅ pullback p (τ ≫ σ) := pullbackLeftPullbackSndIso p σ τ

@[simp, reassoc] theorem compositionIso_comparison (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    (compositionIso p σ τ).hom ≫ comparison p (τ ≫ σ) =
      comparison (reindex p σ) τ ≫ comparison p σ := by simp [compositionIso]

@[simp, reassoc] theorem compositionIso_display (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    (compositionIso p σ τ).hom ≫ reindex p (τ ≫ σ) = reindex (reindex p σ) τ := by
  simp [compositionIso]

theorem termSub_composition (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (t : Term p) :
    (termSub (reindex p σ) τ (termSub p σ t)).val ≫ (compositionIso p σ τ).hom =
      (termSub p (τ ≫ σ) t).val := by
  apply pullback.hom_ext <;> simp [Category.assoc, termSub, pair, compositionIso]
end SquareKit.Family

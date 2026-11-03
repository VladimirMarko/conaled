import SquareKit.Family
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Dependent

/-! Experimental comparison of categorical families with the existing split
Type-family model. Its strict equations become equations through pullback isos. -/
noncomputable section
namespace SquareKit.TypeFamily
open CategoryTheory Limits Family
universe u
variable {Γ Δ Ξ : Type u} (A : Γ → Type u)

abbrev display : DependentSquares.Ext Γ A ⟶ Γ := ↾DependentSquares.p

def asSection (t : DependentSquares.Tm A) : Term (display A) :=
  ⟨↾(DependentSquares.extend DependentSquares.idSub t), rfl⟩

/-- Sections contain exactly the existing dependent terms. -/
def terms : DependentSquares.Tm A ≃ Term (display A) where
  toFun := asSection A
  invFun t γ := (congrArg A (congrArg (fun f : Γ ⟶ Γ => f γ) t.property)) ▸ (t.val γ).2
  left_inv t := by funext γ; rfl
  right_inv t := by
    apply Subtype.ext
    apply ConcreteCategory.hom_ext
    intro γ
    have h := congrArg (fun f : Γ ⟶ Γ => f γ) t.property
    change (t.val γ).1 = γ at h
    change Sigma.mk γ ((congrArg A h) ▸ (t.val γ).2) = t.val γ
    generalize t.val γ = z at h ⊢
    rcases z with ⟨x,a⟩
    dsimp at h
    cases h
    rfl

/-- The split reindexed Sigma is a genuine pullback of the display map. -/
theorem split_pullback (σ : Δ → Γ) :
    IsPullback (↾(DependentSquares.lift (A := A) σ)) (display (DependentSquares.tySub A σ)) (display A) (↾σ) := by
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨δ,a⟩ ⟨ε,b⟩ ⟨ha,hδ⟩
    change δ = ε at hδ
    cases hδ
    have he : a = b := eq_of_heq (Sigma.mk.inj_iff.mp ha).2
    cases he
    rfl
  · rintro ⟨γ,a⟩ δ h
    change γ = σ δ at h
    cases h
    exact ⟨⟨δ,a⟩, rfl, rfl⟩

def pullbackIso (σ : Δ → Γ) :
    DependentSquares.Ext Δ (DependentSquares.tySub A σ) ≅ pullback (display A) (↾σ) :=
  (split_pullback A σ).isoPullback

@[simp, reassoc] theorem pullbackIso_display (σ : Δ → Γ) :
    (pullbackIso A σ).hom ≫ reindex (display A) (↾σ) = display (DependentSquares.tySub A σ) :=
  (split_pullback A σ).isoPullback_hom_snd

@[simp, reassoc] theorem pullbackIso_comparison (σ : Δ → Γ) :
    (pullbackIso A σ).hom ≫ comparison (display A) (↾σ) = ↾(DependentSquares.lift (A := A) σ) :=
  (split_pullback A σ).isoPullback_hom_fst

/-- Ordinary split term substitution agrees after the actual comparison. -/
theorem term_substitution (σ : Δ → Γ) (t : DependentSquares.Tm A) :
    (asSection (DependentSquares.tySub A σ) (DependentSquares.tmSub t σ)).val ≫ (pullbackIso A σ).hom =
      (termSub (display A) (↾σ) (asSection A t)).val := by
  apply pullback.hom_ext <;> simp [Category.assoc, asSection, termSub, Family.pair]
  all_goals rfl

/-- A split dependent value is the same context-extension pairing. -/
theorem pairing (σ : Δ → Γ) (a : DependentSquares.Tm (DependentSquares.tySub A σ)) :
    Family.pair (display A) (↾σ) (↾(DependentSquares.extend σ a)) (𝟙 Δ) rfl =
      (asSection (DependentSquares.tySub A σ) a).val ≫ (pullbackIso A σ).hom := by
  apply pullback.hom_ext <;> simp [Family.pair, Category.assoc, asSection]
  all_goals rfl

/-- Generic variable has the split p/q values, through context-extension pairing. -/
theorem variable_pairing :
    (asSection (DependentSquares.tySub A (DependentSquares.p (A := A))) (DependentSquares.q (A := A))).val ≫
      (pullbackIso A (DependentSquares.p (A := A))).hom = (variableTerm (display A)).val := by
  apply pair_unique (display A) (display A) (𝟙 _) (𝟙 _) rfl
  · rw [Category.assoc, pullbackIso_comparison]
    exact congrArg (fun f : DependentSquares.Ext Γ A → DependentSquares.Ext Γ A => (↾f))
      DependentSquares.extend_eta
  · rw [Category.assoc, pullbackIso_display]
    rfl

/-- The original eta equation, now checked as equality of display morphisms. -/
theorem pairing_eta (f : Δ → DependentSquares.Ext Γ A) :
    (↾(DependentSquares.extend (DependentSquares.compSub DependentSquares.p f) (DependentSquares.tmSub DependentSquares.q f)) : Δ ⟶ DependentSquares.Ext Γ A) = ↾f :=
  congrArg (fun g : Δ → DependentSquares.Ext Γ A => (↾g)) (DependentSquares.extend_eta_sub f)
end SquareKit.TypeFamily

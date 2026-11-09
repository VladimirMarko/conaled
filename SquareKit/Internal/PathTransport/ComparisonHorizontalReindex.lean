import SquareKit.Internal.PathTransport.ComparisonHorizontal

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem whiskerLeft_transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) {A B : D ⥤ E} (h : A = B) :
    whiskerLeft F (eqToHom h) = eqToHom (congrArg (F ⋙ ·) h) := by
  cases h
  simp

private theorem whiskerLeft_transport_naturality {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (h : F = G) {A B : D ⥤ E} (α : A ⟶ B) :
    whiskerLeft F α ≫ eqToHom (congrArg (· ⋙ B) h) =
      eqToHom (congrArg (· ⋙ A) h) ≫ whiskerLeft G α := by
  cases h
  simp

/-- Naturality of horizontal composition with respect to two strict squares. -/
theorem horizontal_reindex_map {C₀ C₁ C₂ D₀ D₁ D₂ : Grpd.{u,u}}
    (R : C₀ ⥤ C₁) (S : C₁ ⥤ C₂) (T : D₀ ⥤ D₁) (U : D₁ ⥤ D₂)
    (f₀ : D₀ ⥤ C₀) (f₁ : D₁ ⥤ C₁) (f₂ : D₂ ⥤ C₂)
    (h : f₀ ⋙ R = T ⋙ f₁) (k : f₁ ⋙ S = U ⋙ f₂)
    {A₀ : C₀ ⥤ Grpd.{u,u}} {A₁ : C₁ ⥤ Grpd.{u,u}} {A₂ : C₂ ⥤ Grpd.{u,u}}
    (α : A₀ ⟶ R ⋙ A₁) (β : A₁ ⟶ S ⋙ A₂)
    (hk : f₀ ⋙ (R ⋙ S) = (T ⋙ U) ⋙ f₂) :
    whiskerLeft f₀ (α ≫ whiskerLeft R β) ≫ eqToHom (congrArg (· ⋙ A₂) hk) =
      (whiskerLeft f₀ α ≫ eqToHom (congrArg (· ⋙ A₁) h)) ≫
        whiskerLeft T (whiskerLeft f₁ β ≫ eqToHom (congrArg (· ⋙ A₂) k)) := by
  rw [whiskerLeft_comp, whiskerLeft_comp, whiskerLeft_transport]
  rw [Category.assoc, Category.assoc]
  congr 1
  change whiskerLeft (f₀ ⋙ R) β ≫ eqToHom (congrArg (· ⋙ A₂) hk) =
    eqToHom (congrArg (· ⋙ A₁) h) ≫
      whiskerLeft (T ⋙ f₁) β ≫ eqToHom (congrArg (T ⋙ ·) (congrArg (· ⋙ A₂) k))
  rw [← Category.assoc, ← whiskerLeft_transport_naturality h β, Category.assoc]
  rw [eqToHom_trans]

theorem Family.horizontal_reindex_middle {Γ Δ Γ' Δ' : Context.{u}}
    (A : Family Γ) (B : Family Γ') (σ : Substitution Δ Γ) (τ : Substitution Δ' Γ')
    (hΓ : Γ.right = Γ'.left) (hΔ : Δ.right = Δ'.left)
    (hA : HEq A.right B.left) (hσ : HEq σ.right τ.left) :
    HEq (A.reindex σ).right (B.reindex τ).left := by
  cases Γ; cases Γ'; cases Δ; cases Δ'
  dsimp at hΓ hΔ
  cases hΓ; cases hΔ
  cases A; cases B; cases σ; cases τ
  dsimp at hA hσ
  cases eq_of_heq hA; cases eq_of_heq hσ
  rfl

/-- Reindexing preserves horizontal family composition with its constructed
substitution square and all equality transports. -/
theorem Family.horizontal_reindex {Γ Δ Γ' Δ' : Context.{u}}
    (A : Family Γ) (B : Family Γ') (σ : Substitution Δ Γ) (τ : Substitution Δ' Γ')
    (hΓ : Γ.right = Γ'.left) (hΔ : Δ.right = Δ'.left)
    (hA : HEq A.right B.left) (hσ : HEq σ.right τ.left) :
    (A.horizontal B hΓ hA).reindex (σ.horizontal τ hΓ hΔ hσ) =
      (A.reindex σ).horizontal (B.reindex τ) hΔ
        (A.horizontal_reindex_middle B σ τ hΓ hΔ hA hσ) := by
  rcases Γ with ⟨C₀, C₁, R⟩
  rcases Γ' with ⟨C₁', C₂, S⟩
  rcases Δ with ⟨D₀, D₁, T⟩
  rcases Δ' with ⟨D₁', D₂, U⟩
  dsimp at hΓ hΔ
  cases hΓ; cases hΔ
  rcases A with ⟨A₀, A₁, α⟩
  rcases B with ⟨A₁', A₂, β⟩
  rcases σ with ⟨f₀, f₁, h⟩
  rcases τ with ⟨f₁', f₂, k⟩
  dsimp at hA hσ
  cases eq_of_heq hA; cases eq_of_heq hσ
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  exact horizontal_reindex_map R S T U f₀ f₁ f₂ h k α β (by
    rw [← CategoryTheory.Functor.assoc, h, CategoryTheory.Functor.assoc, k]
    rfl)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

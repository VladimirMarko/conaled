import SquareKit.Internal.PathTransport.ComparisonComposition

/-! Horizontal composition of ordinary comparison data. These operations
express the identity/composition invariant for generated restriction; they do
not introduce a second interpretation of source syntax. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Compose comparisons whose middle groupoids agree. -/
def Context.horizontal (Γ Δ : Context.{u}) (h : Γ.right = Δ.left) : Context.{u} where
  left := Γ.left
  right := Δ.right
  map := Γ.map ⋙ Δ.relabel h.symm rfl

/-- Compose fiber comparisons after identifying their common middle family. -/
def Family.horizontal {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left) : Family (Γ.horizontal Δ h) := by
  cases Γ with | mk C D R =>
  cases Δ with | mk D' E S =>
  dsimp at h
  cases h
  cases A with | mk A₀ A₁ α =>
  cases B with | mk B₀ B₁ β =>
  dsimp at hA
  cases eq_of_heq hA
  exact ⟨A₀, B₁, α ≫ whiskerLeft R β⟩

/-- The middle total categories agree once both base and family agree. -/
theorem Family.horizontal_middle {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left) : A.extend.right = B.extend.left := by
  cases Γ; cases Δ; dsimp at h; cases h
  cases A; cases B; dsimp at hA
  cases eq_of_heq hA
  rfl

/-- Comprehension preserves the horizontal composite, including arrow action. -/
theorem Family.horizontal_extend {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left) :
    (A.horizontal B h hA).extend =
      A.extend.horizontal B.extend (A.horizontal_middle B h hA) := by
  cases Γ with | mk C D R =>
  cases Δ with | mk D' E S =>
  dsimp at h
  cases h
  cases A with | mk A₀ A₁ α =>
  cases B with | mk B₀ B₁ β =>
  dsimp at hA
  cases eq_of_heq hA
  exact congrArg (fun F : Extend A₀ ⥤ Extend B₁ =>
    Context.mk (@Grpd.of (Extend A₀) Groupoid.ofIsGroupoid)
      (@Grpd.of (Extend B₁) Groupoid.ofIsGroupoid) F) (totalMap_comp R S α β).symm

/-- Horizontal composition of simultaneous substitutions uses their actual
middle functor equality, rather than a pointwise comparison of objects. -/
def Substitution.horizontal {Γ Δ Γ' Δ' : Context.{u}}
    (σ : Substitution Δ Γ) (τ : Substitution Δ' Γ')
    (hΓ : Γ.right = Γ'.left) (hΔ : Δ.right = Δ'.left)
    (hσ : HEq σ.right τ.left) :
    Substitution (Δ.horizontal Δ' hΔ) (Γ.horizontal Γ' hΓ) := by
  rcases Γ with ⟨C₀, C₁, R⟩
  rcases Γ' with ⟨C₁', C₂, S⟩
  rcases Δ with ⟨D₀, D₁, T⟩
  rcases Δ' with ⟨D₁', D₂, U⟩
  dsimp at hΓ hΔ
  cases hΓ; cases hΔ
  rcases σ with ⟨f₀, f₁, hf⟩
  rcases τ with ⟨f₁', f₂, hg⟩
  dsimp at hσ
  cases eq_of_heq hσ
  refine ⟨f₀, f₂, ?_⟩
  change f₀ ⋙ (R ⋙ S) = (T ⋙ U) ⋙ f₂
  rw [← CategoryTheory.Functor.assoc, hf, CategoryTheory.Functor.assoc, hg]
  rfl

/-- Compatible sections compose using their unchanged endpoint sections. -/
def Section.horizontal {Γ Δ : Context.{u}} {A : Family Γ} {B : Family Δ}
    (s : Section A) (t : Section B) (h : Γ.right = Δ.left)
    (hA : HEq A.right B.left) (hs : HEq s.right t.left) : Section (A.horizontal B h hA) := by
  rcases Γ with ⟨C, D, R⟩
  rcases Δ with ⟨D', E, T⟩
  dsimp at h
  cases h
  rcases A with ⟨A₀, A₁, α⟩
  rcases B with ⟨B₀, B₁, β⟩
  dsimp at hA
  cases eq_of_heq hA
  rcases s with ⟨s₀, s₁, hc⟩
  rcases t with ⟨s₁', s₂, hd⟩
  dsimp at hs
  cases eq_of_heq hs
  refine ⟨s₀, s₂, ?_⟩
  change s₀.familyImage (α ≫ whiskerLeft R β) = s₂.reindex (R ⋙ T)
  rw [GroupoidModel.Section.familyImage_comp, hc,
    GroupoidModel.Section.familyImage_reindex, hd]
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Assemble two successive endpoint restrictions into a rectangle pullback. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SquareKit

variable {C : Type*} [Category C] [HasBinaryProducts C]
  {A B R X Y U V : C}
  {f : A ⟶ X} {g : A ⟶ Y} {u : U ⟶ X} {v : V ⟶ Y}
  {i : B ⟶ A} {p : B ⟶ U} {j : R ⟶ B} {q : R ⟶ V}

/-- Restrict the first endpoint, then the second, retaining both complete maps. -/
theorem rectangle_isPullback (h₁ : IsPullback i p f u)
    (h₂ : IsPullback j q (i ≫ g) v) :
    IsPullback (j ≫ i) (prod.lift (j ≫ p) q) (prod.lift f g) (prod.map u v) := by
  apply IsPullback.mk'
  · apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst]
      simpa only [Category.assoc, prod.lift_fst_assoc] using congrArg (j ≫ ·) h₁.w
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd]
      simpa only [← Category.assoc, prod.lift_snd] using h₂.w
  · intro T a b hab hpq
    apply h₂.hom_ext
    · apply h₁.hom_ext
      · simpa only [Category.assoc] using hab
      · have h := congrArg (fun k => k ≫ prod.fst) hpq
        simpa only [Category.assoc, prod.lift_fst] using h
    · have h := congrArg (fun k => k ≫ prod.snd) hpq
      simpa only [Category.assoc, prod.lift_snd] using h
  · intro T a b h
    have hx : a ≫ f = (b ≫ prod.fst) ≫ u := by
      have he := congrArg (fun k => k ≫ prod.fst) h
      simpa only [Category.assoc, prod.lift_fst, prod.map_fst] using he
    have hy : a ≫ g = (b ≫ prod.snd) ≫ v := by
      have he := congrArg (fun k => k ≫ prod.snd) h
      simpa only [Category.assoc, prod.lift_snd, prod.map_snd] using he
    let a₁ := h₁.lift a (b ≫ prod.fst) hx
    have ha₁ : a₁ ≫ i = a := h₁.lift_fst _ _ _
    have ha₂ : a₁ ≫ p = b ≫ prod.fst := h₁.lift_snd _ _ _
    have hxy : a₁ ≫ (i ≫ g) = (b ≫ prod.snd) ≫ v := by
      rw [← Category.assoc, ha₁, hy]
    refine ⟨h₂.lift a₁ (b ≫ prod.snd) hxy, ?_, ?_⟩
    · rw [← Category.assoc, h₂.lift_fst, ha₁]
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst]
        rw [← Category.assoc, h₂.lift_fst, ha₂]
      · simp only [Category.assoc, prod.lift_snd, h₂.lift_snd]

end SquareKit

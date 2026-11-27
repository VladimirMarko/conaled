import Mathlib.CategoryTheory.Equivalence

/-! Transport a commuting square across equivalences of independently sized categories.
The specification, composition and recovery equations are shared by local sheaf
substitution and stackification. -/

noncomputable section
set_option autoImplicit false

namespace CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
variable {A₀ : Type u₀} [Category.{v₀} A₀]
variable {A₁ : Type u₁} [Category.{v₁} A₁]
variable {A₂ : Type u₂} [Category.{v₂} A₂]
variable {D₀ : Type w₀} [Category.{z₀} D₀]
variable {D₁ : Type w₁} [Category.{z₁} D₁]
variable {D₂ : Type w₂} [Category.{z₂} D₂]
variable (E₀ : A₀ ≌ D₀) (E₁ : A₁ ≌ D₁) (E₂ : A₂ ≌ D₂)
variable (R₀₁ : D₀ ⥤ D₁) (R₁₂ : D₁ ⥤ D₂) (R₀₂ : D₀ ⥤ D₂)
variable (L₀₁ : A₀ ⥤ A₁) (L₁₂ : A₁ ⥤ A₂) (L₀₂ : A₀ ⥤ A₂)
variable (i₀₁ : E₀.functor ⋙ R₀₁ ≅ L₀₁ ⋙ E₁.functor)
variable (i₁₂ : E₁.functor ⋙ R₁₂ ≅ L₁₂ ⋙ E₂.functor)
variable (i₀₂ : E₀.functor ⋙ R₀₂ ≅ L₀₂ ⋙ E₂.functor)

def inverseSquareAcross : R₀₁ ⋙ E₁.inverse ≅ E₀.inverse ⋙ L₀₁ :=
  (Iso.isoCompInverse (H := E₁) (Functor.associator _ _ _ ≪≫
    Iso.inverseCompIso (G := E₀) i₀₁.symm)).symm

@[reassoc] theorem inverseSquareAcross_spec (d : D₀) :
    E₁.counitIso.inv.app (R₀₁.obj d) ≫
        E₁.functor.map ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d) =
      R₀₁.map (E₀.counitIso.inv.app d) ≫ i₀₁.hom.app (E₀.inverse.obj d) := by
  dsimp [inverseSquareAcross, Iso.isoCompInverse, Iso.inverseCompIso]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [← E₁.counit_app_functor]
  simp [Equivalence.fun_inv_map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem inverseSquareAcross_comp (c : R₀₁ ⋙ R₁₂ ≅ R₀₂) (l : L₀₁ ⋙ L₁₂ ≅ L₀₂)
    (hc : ∀ a : A₀, R₁₂.map (i₀₁.hom.app a) ≫ i₁₂.hom.app (L₀₁.obj a) ≫
      E₂.functor.map (l.hom.app a) = c.hom.app (E₀.functor.obj a) ≫ i₀₂.hom.app a)
    (d : D₀) :
    (inverseSquareAcross E₁ E₂ R₁₂ L₁₂ i₁₂).hom.app (R₀₁.obj d) ≫
      L₁₂.map ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d) ≫
      l.hom.app (E₀.inverse.obj d) =
    E₂.inverse.map (c.hom.app d) ≫
      (inverseSquareAcross E₀ E₂ R₀₂ L₀₂ i₀₂).hom.app d := by
  apply E₂.functor.map_injective
  apply (cancel_epi (E₂.counitIso.inv.app (R₁₂.obj (R₀₁.obj d)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquareAcross_spec_assoc]
  simp only [Equivalence.fun_inv_map, Category.assoc, Equivalence.counit, Equivalence.counitInv]
  rw [inverseSquareAcross_spec]
  have hn := i₁₂.hom.naturality ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d)
  dsimp at hn
  rw [← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, inverseSquareAcross_spec]
  rw [Functor.map_comp, Category.assoc, hc]
  have hn := c.hom.naturality (E₀.counitIso.inv.app d)
  dsimp at hn
  rw [← Category.assoc, hn]
  simp [Functor.comp_obj]


theorem inverseSquareAcross_canonical (a : A₀) :
    E₁.inverse.map (i₀₁.hom.app a) ≫ E₁.unitIso.inv.app (L₀₁.obj a) =
      (inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app (E₀.functor.obj a) ≫
        L₀₁.map (E₀.unitIso.inv.app a) := by
  apply E₁.functor.map_injective
  apply (cancel_epi (E₁.counitIso.inv.app (R₀₁.obj (E₀.functor.obj a)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquareAcross_spec_assoc]
  rw [← E₁.counit_app_functor]
  simp only [Equivalence.fun_inv_map, Equivalence.counit, Equivalence.counitInv,
    Category.assoc]
  have hn := i₀₁.hom.naturality (E₀.unitIso.inv.app a)
  dsimp at hn
  rw [← hn, ← Functor.map_comp_assoc, ← E₀.counit_app_functor]
  simp

end CategoryTheory

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates

/-! Experimental operation laws for canonical right-adjoint uniqueness. -/
namespace SquareKit.AdjointComparison
open CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R S : D ⥤ C} (a : L ⊣ R) (b : L ⊣ S)

theorem curry {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ (a.rightAdjointUniq b).hom.app Y = b.homEquiv X Y f := by
  apply (b.homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_hom_app_counit]
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

theorem uncurry {X : C} {Y : D} (f : X ⟶ R.obj Y) :
    (b.homEquiv X Y).symm (f ≫ (a.rightAdjointUniq b).hom.app Y) = (a.homEquiv X Y).symm f := by
  have h := curry a b ((a.homEquiv X Y).symm f)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (b.homEquiv X Y).symm h |>.trans ((b.homEquiv X Y).symm_apply_apply _)

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
variable {L' : C' ⥤ D'} {R' S' : D' ⥤ C'} (a' : L' ⊣ R') (b' : L' ⊣ S')
variable {G : C ⥤ C'} {H : D ⥤ D'} (t : G ⋙ L' ⟶ L ⋙ H)

/-- Changing both chosen right adjoints conjugates the same canonical mate. -/
theorem mate (Y : D) :
    G.map ((a.rightAdjointUniq b).hom.app Y) ≫ (mateEquiv b b' t).app Y =
      (mateEquiv a a' t).app Y ≫ (a'.rightAdjointUniq b').hom.app (H.obj Y) := by
  apply (b'.homEquiv _ _).symm.injective
  rw [uncurry a' b']
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, mateEquiv_counit]
  have hn := t.naturality ((a.rightAdjointUniq b).hom.app Y)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← H.map_comp,
    Adjunction.rightAdjointUniq_hom_app_counit]

end SquareKit.AdjointComparison

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
/-! Canonical projection, base-change and Künneth maps. Construction and the
counit calculation do not require invertibility. -/
namespace SquareKit.Kunneth
open CategoryTheory MonoidalCategory Functor
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {S : Type u₁} {X : Type u₂} {Y : Type u₃} {W : Type u₄}
  [Category.{v₁} S] [Category.{v₂} X]
  [Category.{v₃} Y] [Category.{v₄} W]
  [MonoidalCategory S] [MonoidalCategory X] [MonoidalCategory W]
variable {F : S ⥤ X} {RF : X ⥤ S} (af : F ⊣ RF) [F.OplaxMonoidal]
  {G : S ⥤ Y} {RG : Y ⥤ S} (ag : G ⊣ RG)
  {P : X ⥤ W} {RP : W ⥤ X} (ap : P ⊣ RP) [P.OplaxMonoidal]
  {Q : Y ⥤ W} (e : F ⋙ P ⟶ G ⋙ Q)
/-- Projection formula map, defined as the transpose of the tensor with the counit. -/
noncomputable def projection (A : X) (N : S) : RF.obj A ⊗ N ⟶ RF.obj (A ⊗ F.obj N) :=
  af.homEquiv _ _ (OplaxMonoidal.δ F _ _ ≫ (af.counit.app A ⊗ₘ 𝟙 _))
/-- Right-handed projection formula before applying any symmetry assumptions. -/
noncomputable def projectionRight (N : S) (A : X) : N ⊗ RF.obj A ⟶ RF.obj (F.obj N ⊗ A) :=
  af.homEquiv _ _ (OplaxMonoidal.δ F _ _ ≫ (𝟙 _ ⊗ₘ af.counit.app A))
/-- Canonical mate of the specified square. -/
noncomputable def baseChange (B : Y) : F.obj (RG.obj B) ⟶ RP.obj (Q.obj B) :=
  ap.homEquiv _ _ (e.app (RG.obj B) ≫ Q.map (ag.counit.app B))
/-- The projection/base-change composite (K), with iterated pushforward target. -/
noncomputable def map (A : X) (B : Y) :
  RF.obj A ⊗ RG.obj B ⟶ RF.obj (RP.obj (P.obj A ⊗ Q.obj B)) :=
  projection af A (RG.obj B) ≫ RF.map (𝟙 A ⊗ₘ baseChange ag ap e B) ≫
  RF.map (projectionRight ap A (Q.obj B))
/-- The composite (K) has precisely the tensor-of-counits transpose (E). -/
theorem counit_characterization (A : X) (B : Y) :
  ((af.comp ap).homEquiv _ _).symm (map af ag ap e A B) =
  P.map (OplaxMonoidal.δ F _ _) ≫ OplaxMonoidal.δ P _ _ ≫
  (P.map (af.counit.app A) ⊗ₘ (e.app (RG.obj B) ≫ Q.map (ag.counit.app B))) := by
  simp only [map, projection, projectionRight, baseChange, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  rw [← Functor.map_comp]
  rw [← af.homEquiv_naturality_right]
  rw [Equiv.symm_apply_apply]
  rw [ap.homEquiv_naturality_left_symm, ap.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Functor.map_comp, Category.assoc]
  rw [← OplaxMonoidal.δ_natural_assoc]
  rw [← OplaxMonoidal.δ_natural_assoc]
  simp only [Functor.map_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [← ap.homEquiv_counit, Equiv.symm_apply_apply]

omit [MonoidalCategory S] [MonoidalCategory X] [MonoidalCategory W]
  [F.OplaxMonoidal] [P.OplaxMonoidal] in
/-- The canonical base-change component is the ordinary mate. -/
theorem baseChange_eq_mate (B : Y) :
    baseChange ag ap e B = (mateEquiv ag ap e).app B := by
  apply (ap.homEquiv _ _).symm.injective
  rw [baseChange, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit ag ap e B).symm

/-- Invertibility uses the two projection components and the base-change component,
not merely commutativity of the input square. -/
noncomputable def iso (A : X) (B : Y)
    [IsIso (projection af A (RG.obj B))]
    [IsIso (baseChange ag ap e B)]
    [IsIso (projectionRight ap A (Q.obj B))] :
    RF.obj A ⊗ RG.obj B ≅ RF.obj (RP.obj (P.obj A ⊗ Q.obj B)) :=
  letI : IsIso (map af ag ap e A B) := by unfold map; infer_instance
  asIso (map af ag ap e A B)

@[simp] theorem iso_hom (A : X) (B : Y)
    [IsIso (projection af A (RG.obj B))]
    [IsIso (baseChange ag ap e B)]
    [IsIso (projectionRight ap A (Q.obj B))] :
    (iso af ag ap e A B).hom = map af ag ap e A B := rfl

end SquareKit.Kunneth

namespace SquareKit.Kunneth
open CategoryTheory MonoidalCategory Functor
variable {S : Type u₁} {X : Type u₂} [Category.{v₁} S] [Category.{v₂} X]
  [MonoidalCategory S] [MonoidalCategory X] [SymmetricCategory S] [SymmetricCategory X]
  {F : S ⥤ X} {RF : X ⥤ S} (af : F ⊣ RF) [F.Braided]
/-- The right projection formula is the usual projection formula conjugated
by symmetry, as in the third line of the proper Künneth calculation. -/
theorem projectionRight_eq (N : S) (A : X) :
    projectionRight af N A =
      (β_ N (RF.obj A)).hom ≫ projection af A N ≫ RF.map (β_ A (F.obj N)).hom := by
  apply (af.homEquiv _ _).symm.injective
  unfold projectionRight projection
  rw [Equiv.symm_apply_apply, ← Category.assoc,
    af.homEquiv_naturality_right_symm, af.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  simp

end SquareKit.Kunneth

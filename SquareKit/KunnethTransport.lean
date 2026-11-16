import SquareKit.Kunneth
import SquareKit.AdjointSquareTransport

/-! Transport of the tensor-of-counits characterization through a monoidal
adjoint square. Comparisons are retained as maps before invertibility is used. -/
namespace SquareKit.Kunneth
open CategoryTheory MonoidalCategory Functor
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
 [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
 [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
 {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
 (a : L ⊣ R) (a' : L' ⊣ R')
 {G : C ⥤ C'} {H : D ⥤ D'}
 [L.OplaxMonoidal] [L'.OplaxMonoidal] [G.OplaxMonoidal] [H.OplaxMonoidal]
 (s : G ⋙ L' ⟶ L ⋙ H)

/-- Transpose a pair of evaluation maps using the specified tensor comparison. -/
noncomputable def tensorTranspose {U V : C} {A B : D}
    (x : L.obj U ⟶ A) (y : L.obj V ⟶ B) : U ⊗ V ⟶ R.obj (A ⊗ B) :=
  a.homEquiv _ _ (OplaxMonoidal.δ L U V ≫ (x ⊗ₘ y))

/-- Tensor compatibility of the pullback square, expressed in the direction
consumed by evaluation. This is a structural law for every pair of objects. -/
def TensorCompatible : Prop := ∀ U V,
    L'.map (OplaxMonoidal.δ G U V) ≫ OplaxMonoidal.δ L' _ _ ≫
      (s.app U ⊗ₘ s.app V) =
    s.app (U ⊗ V) ≫ H.map (OplaxMonoidal.δ L U V) ≫ OplaxMonoidal.δ H _ _

/-- Transport of a selected tensor transpose. The two component equations are
counit compatibility and square/composition compatibility in the Künneth use. -/
theorem tensorTranspose_transport
    (hs : TensorCompatible s)
    {U V : C} {A B : D} {U' V' : C'} {A' B' : D'}
    (x : L.obj U ⟶ A) (y : L.obj V ⟶ B)
    (x' : L'.obj U' ⟶ A') (y' : L'.obj V' ⟶ B')
    (i : G.obj U ⟶ U') (j : G.obj V ⟶ V')
    (k : H.obj A ⟶ A') (l : H.obj B ⟶ B')
    (hx : L'.map i ≫ x' = s.app U ≫ H.map x ≫ k)
    (hy : L'.map j ≫ y' = s.app V ≫ H.map y ≫ l) :
    G.map (tensorTranspose a x y) ≫ (mateEquiv a a' s).app (A ⊗ B) ≫
      R'.map (OplaxMonoidal.δ H A B ≫ (k ⊗ₘ l)) =
    (OplaxMonoidal.δ G U V ≫ (i ⊗ₘ j)) ≫ tensorTranspose a' x' y' := by
  unfold tensorTranspose
  rw [← Category.assoc, AdjointSquareTransport.curry a a' s]
  rw [← a'.homEquiv_naturality_right, ← a'.homEquiv_naturality_left]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [← OplaxMonoidal.δ_natural_assoc L' i j]
  simp only [tensorHom_comp_tensorHom, hx, hy]
  rw [← OplaxMonoidal.δ_natural_assoc H x y]
  simp only [← tensorHom_comp_tensorHom, ← Category.assoc]
  have h := hs U V
  simp only [← Category.assoc] at h
  rw [← h]

/-- Conjugation form (T), with specified input and output endpoint isomorphisms.
The output comparison contains the actual mate, not an independently chosen map. -/
theorem tensorTranspose_transport_conjugate
    (hs : TensorCompatible s)
    {U V : C} {A B : D} {U' V' : C'} {A' B' : D'}
    (x : L.obj U ⟶ A) (y : L.obj V ⟶ B)
    (x' : L'.obj U' ⟶ A') (y' : L'.obj V' ⟶ B')
    (i : G.obj U ⟶ U') (j : G.obj V ⟶ V')
    (k : H.obj A ⟶ A') (l : H.obj B ⟶ B')
    (hx : L'.map i ≫ x' = s.app U ≫ H.map x ≫ k)
    (hy : L'.map j ≫ y' = s.app V ≫ H.map y ≫ l)
    (input : G.obj (U ⊗ V) ≅ U' ⊗ V')
    (output : G.obj (R.obj (A ⊗ B)) ≅ R'.obj (A' ⊗ B'))
    (hi : input.hom = OplaxMonoidal.δ G U V ≫ (i ⊗ₘ j))
    (ho : output.hom = (mateEquiv a a' s).app (A ⊗ B) ≫
      R'.map (OplaxMonoidal.δ H A B ≫ (k ⊗ₘ l))) :
    input.inv ≫ G.map (tensorTranspose a x y) ≫ output.hom =
      tensorTranspose a' x' y' := by
  rw [ho, tensorTranspose_transport a a' s hs x y x' y' i j k l hx hy,
    ← hi, Iso.inv_hom_id_assoc]

end SquareKit.Kunneth

namespace SquareKit.Kunneth
open CategoryTheory MonoidalCategory Functor
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {S : Type u₁} {X : Type u₂} {Y : Type u₃} {W : Type u₄}
 [Category.{v₁} S] [Category.{v₂} X] [Category.{v₃} Y] [Category.{v₄} W]
 [MonoidalCategory S] [MonoidalCategory X] [MonoidalCategory W]
 {F : S ⥤ X} {RF : X ⥤ S} (af : F ⊣ RF) [F.OplaxMonoidal]
 {G : S ⥤ Y} {RG : Y ⥤ S} (ag : G ⊣ RG)
 {P : X ⥤ W} {RP : W ⥤ X} (ap : P ⊣ RP) [P.OplaxMonoidal]
 {Q : Y ⥤ W} (e : F ⋙ P ⟶ G ⋙ Q)

/-- The Künneth composite is the shared tensor transpose. This connects its
transport theorem to the independently constructed PF/BC map. -/
theorem map_eq_tensorTranspose (A : X) (B : Y) :
    map af ag ap e A B = tensorTranspose (af.comp ap)
      (P.map (af.counit.app A)) (e.app (RG.obj B) ≫ Q.map (ag.counit.app B)) := by
  apply ((af.comp ap).homEquiv _ _).symm.injective
  rw [counit_characterization]
  unfold tensorTranspose
  dsimp only [Functor.id_obj]
  rw [Equiv.symm_apply_apply]
  simp only [Functor.OplaxMonoidal.comp_δ, Category.assoc]
end SquareKit.Kunneth


namespace SquareKit.Kunneth
open CategoryTheory
universe u v u' v'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
/-- Equality of the transported chosen isomorphisms also transports their
specified inverses and both inverse equations. -/
theorem inverse_transport (G : C ⥤ D) {X Y : C} {X' Y' : D}
    (source : X ≅ Y) (target : X' ≅ Y')
    (input : G.obj X ≅ X') (output : G.obj Y ≅ Y')
    (h : input.inv ≫ G.map source.hom ≫ output.hom = target.hom) :
    output.inv ≫ G.map source.inv ≫ input.hom = target.inv := by
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using
    congrArg Iso.inv (show input.symm ≪≫ G.mapIso source ≪≫ output = target from Iso.ext h)
end SquareKit.Kunneth

namespace SquareKit.Kunneth
open CategoryTheory MonoidalCategory Functor
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
 [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
 [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
 {L : C ⥤ D} {L' : C' ⥤ D'} {G : C ⥤ C'} {H : D ⥤ D'}
 [L.Monoidal] [L'.Monoidal] [G.Monoidal] [H.Monoidal]
 (s : G ⋙ L' ⟶ L ⋙ H) [NatTrans.IsMonoidal s]

/-- Native monoidality supplies the structural tensor compatibility required
by transport; clients need not postulate a second monoidal coherence law. -/
theorem tensorCompatible_of_monoidal : TensorCompatible s := by
  intro U V
  have ht := NatTrans.IsMonoidal.tensor (τ := s) U V
  have he : OplaxMonoidal.δ (G ⋙ L') U V ≫ (s.app U ⊗ₘ s.app V) =
      s.app (U ⊗ V) ≫ OplaxMonoidal.δ (L ⋙ H) U V := by
    apply (cancel_epi (LaxMonoidal.μ (G ⋙ L') U V)).1
    rw [← Category.assoc, Monoidal.μ_δ, Category.id_comp, ← Category.assoc, ht]
    simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id]
  simpa only [OplaxMonoidal.comp_δ, Category.assoc] using he
end SquareKit.Kunneth

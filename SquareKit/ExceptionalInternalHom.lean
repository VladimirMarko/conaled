import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The local exceptional internal Hom

The specified exceptional projection formula and the two adjunctions determine
`[f_! A, B] ≅ f_* [A, f^! B]`. Tensor order is fixed using the braiding.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.ExceptionalInternalHom

universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]

/-- Closed transposition with the test object on the left of the tensor. -/
noncomputable def rightAdj (A : C) : tensorRight A ⊣ ihom A :=
  (ihom.adjunction A).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight A)

variable (pull : D ⥤ C) (shriek : C ⥤ D)

/-- The selected exceptional PF, natural in both its arguments. -/
structure ProjectionFormula where
  iso (A : C) : pull ⋙ (tensorRight A ⋙ shriek) ≅ tensorRight (shriek.obj A)
  naturality {A A' : C} (a : A ⟶ A') (T : D) :
    shriek.map (pull.obj T ◁ a) ≫ (iso A').hom.app T =
      (iso A).hom.app T ≫ (T ◁ shriek.map a)

variable {pull shriek} {push : C ⥤ D} {extra : D ⥤ C}
  (ordinary : pull ⊣ push) (exceptional : shriek ⊣ extra)
  (pf : ProjectionFormula pull shriek)

/-- The composite adjunction supplies the last three steps of the Hom chain. -/
noncomputable def composite (A : C) :
    pull ⋙ (tensorRight A ⋙ shriek) ⊣ (extra ⋙ ihom A) ⋙ push :=
  ordinary.comp ((rightAdj A).comp exceptional)

/-- The exact five-step Hom chain, including the selected PF component. -/
noncomputable def chain (A : C) (B T : D) :
    (T ⟶ (ihom (shriek.obj A)).obj B) ≃
      (T ⟶ push.obj ((ihom A).obj (extra.obj B))) :=
  ((rightAdj (shriek.obj A)).homEquiv T B).symm |>.trans
    (((pf.iso A).app T).symm.homFromEquiv) |>.trans
    ((composite ordinary exceptional A).homEquiv T B)

/-- Conjugation of the selected PF constructs the internal-Hom comparison. -/
noncomputable def iso (A : C) :
    ihom (shriek.obj A) ≅ (extra ⋙ ihom A) ⋙ push :=
  conjugateIsoEquiv (rightAdj (shriek.obj A))
    (composite ordinary exceptional A) (pf.iso A)

@[simp]
theorem chain_naturality_test (A : C) (B : D) {T T' : D}
    (t : T' ⟶ T) (g : T ⟶ (ihom (shriek.obj A)).obj B) :
    chain ordinary exceptional pf A B T' (t ≫ g) =
      t ≫ chain ordinary exceptional pf A B T g := by
  simp only [chain, Equiv.trans_apply, Iso.homFromEquiv_apply,
    Adjunction.homEquiv_naturality_left_symm, Iso.symm_inv, Iso.app_hom]
  rw [← Category.assoc, ← (pf.iso A).hom.naturality t]
  simp only [Category.assoc, Adjunction.homEquiv_naturality_left]

/-- Identification with the specified chain for every test arrow. -/
theorem hom_eq_chain (A : C) (B T : D)
    (g : T ⟶ (ihom (shriek.obj A)).obj B) :
    g ≫ (iso ordinary exceptional pf A).hom.app B =
      chain ordinary exceptional pf A B T g := by
  apply ((composite ordinary exceptional A).homEquiv T B).symm.injective
  simp only [chain, Equiv.trans_apply, Equiv.symm_apply_apply,
    Iso.homFromEquiv_apply, Iso.symm_inv, Iso.app_hom, iso, conjugateIsoEquiv_apply_hom]
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_counit, conjugateEquiv_counit]
  rw [← Category.assoc, (pf.iso A).hom.naturality]
  simp only [Category.assoc, Adjunction.homEquiv_counit]

/-- Inverse map identification uses the inverse of the same selected chain. -/
theorem inv_eq_chain (A : C) (B T : D)
    (g : T ⟶ push.obj ((ihom A).obj (extra.obj B))) :
    g ≫ (iso ordinary exceptional pf A).inv.app B =
      (chain ordinary exceptional pf A B T).symm g := by
  apply (cancel_mono ((iso ordinary exceptional pf A).hom.app B)).mp
  rw [hom_eq_chain ordinary exceptional pf A B T ((chain ordinary exceptional pf A B T).symm g),
    Equiv.apply_symm_apply]
  simp

/-- Covariance in the target is part of the constructed natural isomorphism. -/
theorem naturality_target (A : C) {B B' : D} (b : B ⟶ B') :
    (ihom (shriek.obj A)).map b ≫ (iso ordinary exceptional pf A).hom.app B' =
      (iso ordinary exceptional pf A).hom.app B ≫
        push.map ((ihom A).map (extra.map b)) :=
  (iso ordinary exceptional pf A).hom.naturality b

private theorem right_uncurry_pre {A A' X T : C} (a : A' ⟶ A)
    (g : T ⟶ (ihom A).obj X) :
    ((rightAdj A').homEquiv T X).symm (g ≫ (MonoidalClosed.pre a).app X) =
      (T ◁ a) ≫ ((rightAdj A).homEquiv T X).symm g := by
  simp only [rightAdj, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app]
  change (β_ A' T).inv ≫ MonoidalClosed.uncurry (g ≫ (MonoidalClosed.pre a).app X) = _
  rw [MonoidalClosed.uncurry_pre_app, ← Category.assoc]
  rw [← BraidedCategory.braiding_inv_naturality_right]
  exact Category.assoc _ _ _

/-- Contravariance in the coefficient uses the PF's second naturality law. -/
theorem chain_naturality_coefficient {A A' : C} (a : A' ⟶ A) (B T : D)
    (g : T ⟶ (ihom (shriek.obj A)).obj B) :
    chain ordinary exceptional pf A' B T (g ≫ (MonoidalClosed.pre (shriek.map a)).app B) =
      chain ordinary exceptional pf A B T g ≫
        push.map ((MonoidalClosed.pre a).app (extra.obj B)) := by
  apply (ordinary.homEquiv T _).symm.injective
  simp only [chain, composite, Equiv.trans_apply, Iso.homFromEquiv_apply,
    Iso.symm_inv, Iso.app_hom, Adjunction.comp_homEquiv, Functor.comp_obj,
    Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_right_symm]
  apply ((rightAdj A').homEquiv (pull.obj T) (extra.obj B)).symm.injective
  simp only [Equiv.symm_apply_apply, right_uncurry_pre]
  change exceptional.homEquiv _ _ _ = (pull.obj T ◁ a) ≫ exceptional.homEquiv _ _ _
  rw [← exceptional.homEquiv_naturality_left (pull.obj T ◁ a)]
  congr 1
  rw [← Category.assoc, ← pf.naturality a T, Category.assoc]

/-- The constructed comparison is contravariant in the coefficient. -/
theorem naturality_coefficient {A A' : C} (a : A' ⟶ A) (B : D) :
    (MonoidalClosed.pre (shriek.map a)).app B ≫
        (iso ordinary exceptional pf A').hom.app B =
      (iso ordinary exceptional pf A).hom.app B ≫
        push.map ((MonoidalClosed.pre a).app (extra.obj B)) := by
  rw [hom_eq_chain, ← Category.id_comp ((MonoidalClosed.pre (shriek.map a)).app B),
    chain_naturality_coefficient, ← hom_eq_chain, Category.id_comp]

end CategoryTheory.ExceptionalInternalHom

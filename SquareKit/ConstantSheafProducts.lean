import SquareKit.LocallyConstantSheaf
import SquareKit.SheafIndexedProduct
import Mathlib.CategoryTheory.Limits.Types.Products

/-! Finite products of locally constant sheaves, and the comparison for arbitrary
powers. Finiteness is required only for the inverse, not for the comparison. -/
noncomputable section
namespace SquareKit.LocallyConstantSheaf
open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (X : TopCat.{0}) (I A : Type)

abbrev power := SheafIndexedProduct.obj (fun _ : I => obj X A)

def comparison : obj X (I → A) ⟶ power X I A :=
  ⟨{ app _ := ↾LocallyConstant.flip }⟩

/-- The target is the categorical product; each projection is the mapped evaluation. -/
def canonicalComparison : obj X (I → A) ⟶ ∏ᶜ (fun _ : I => obj X A) :=
  comparison X I A ≫ (SheafIndexedProduct.iso _).hom

theorem canonical_projection (i : I) :
    canonicalComparison X I A ≫ Pi.π (fun _ : I => obj X A) i =
      map X (fun s : I → A => s i) := by
  rw [canonicalComparison, Category.assoc, SheafIndexedProduct.iso_projection]
  rfl

/-- This is Mathlib's product comparison, using the standard Type product isomorphism. -/
theorem canonical_eq_piComparison :
    canonicalComparison X I A =
      (delta X).map (Types.productIso (fun _ : I => A)).inv ≫
        piComparison (delta X) (fun _ : I => A) := by
  apply Pi.hom_ext
  intro i
  rw [canonical_projection, Category.assoc]
  erw [piComparison_comp_π, ← Functor.map_comp,
    Types.productIso_inv_comp_π]
  rfl

def finiteIso [Finite I] : obj X (I → A) ≅ power X I A where
  hom := comparison X I A
  inv := ⟨{ app _ := ↾LocallyConstant.unflip }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

instance finiteComparison_isIso [Finite I] : IsIso (comparison X I A) :=
  (finiteIso X I A).isIso_hom

instance finiteCanonical_isIso [Finite I] : IsIso (canonicalComparison X I A) := by
  unfold canonicalComparison
  infer_instance

/-- Arbitrary finite binary products, with their two projections. -/
def binaryIso (B : Type) : obj X (A × B) ≅ SheafRelation.product (obj X A) (obj X B) where
  hom := SheafRelation.lift (map X Prod.fst) (map X Prod.snd)
  inv := ⟨{ app U := ↾fun (p : LocallyConstant U.unop A × LocallyConstant U.unop B) =>
    ⟨fun x => (p.1 x, p.2 x), p.1.isLocallyConstant.prodMk p.2.isLocallyConstant⟩ }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s <;> rfl

end SquareKit.LocallyConstantSheaf

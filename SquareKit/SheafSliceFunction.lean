import SquareKit.SheafSlice
import SquareKit.SheafFunction
import SquareKit.ClosedComparison
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! Experimental function spaces in arbitrary sheaf slices. The local monoidal
adapter uses ordinary family pullbacks; the public adjunction uses the actual
chosen products in the ordinary slice category. -/
noncomputable section
namespace SquareKit.SheafSliceFunction
open CategoryTheory Limits MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Γ : Sheaf J (Type (max u v)))

local instance : CartesianMonoidalCategory (Over Γ) := Over.cartesianMonoidalCategory Γ

/-- Closure transported along the constructed site-of-elements equivalence. -/
@[instance_reducible] def closed : MonoidalClosed (Over Γ) := by
  let h : MonoidalClosed (SheafSlice.ElementSheaves Γ) := inferInstance
  exact @cartesianClosedOfEquiv (SheafSlice.ElementSheaves Γ) _ inferInstance
    (Over Γ) _ (Over.cartesianMonoidalCategory Γ) (SheafSlice.equivalence Γ).symm h
attribute [local instance] closed

abbrev rightAdjoint (A : Over Γ) : Over Γ ⥤ Over Γ := ihom A
abbrev exponential (A B : Over Γ) : Over Γ := (rightAdjoint Γ A).obj B

/-- Explicit adapter between the pullback tensor and chosen slice products. -/
def productAdapter (A X : Over Γ) : A ⊗ X ≅ A ⨯ X :=
  (CartesianMonoidalCategory.tensorLeftIsoProd A).app X

def adjunction (A : Over Γ) : prod.functor.obj A ⊣ rightAdjoint Γ A :=
  (ihom.adjunction A).ofNatIsoLeft (CartesianMonoidalCategory.tensorLeftIsoProd A)

def homEquiv (A X B : Over Γ) : (A ⨯ X ⟶ B) ≃ (X ⟶ exponential Γ A B) :=
  (adjunction Γ A).homEquiv X B

def curry {A X B : Over Γ} (f : A ⨯ X ⟶ B) : X ⟶ exponential Γ A B :=
  homEquiv Γ A X B f

def uncurry {A X B : Over Γ} (f : X ⟶ exponential Γ A B) : A ⨯ X ⟶ B :=
  (homEquiv Γ A X B).symm f

@[simp] theorem beta {A X B : Over Γ} (f : A ⨯ X ⟶ B) : uncurry Γ (curry Γ f) = f :=
  (homEquiv Γ A X B).symm_apply_apply f
@[simp] theorem eta {A X B : Over Γ} (f : X ⟶ exponential Γ A B) : curry Γ (uncurry Γ f) = f :=
  (homEquiv Γ A X B).apply_symm_apply f

def evaluation (A B : Over Γ) : A ⨯ exponential Γ A B ⟶ B := uncurry Γ (𝟙 _)

theorem curry_parameter {A X Y B : Over Γ} (f : A ⨯ X ⟶ B) (g : Y ⟶ X) :
    curry Γ (prod.map (𝟙 A) g ≫ f) = g ≫ curry Γ f :=
  (adjunction Γ A).homEquiv_naturality_left g f

theorem uncurry_parameter {A X Y B : Over Γ} (f : X ⟶ exponential Γ A B) (g : Y ⟶ X) :
    uncurry Γ (g ≫ f) = prod.map (𝟙 A) g ≫ uncurry Γ f :=
  (adjunction Γ A).homEquiv_naturality_left_symm g f

theorem curry_result {A X B B' : Over Γ} (f : A ⨯ X ⟶ B) (g : B ⟶ B') :
    curry Γ (f ≫ g) = curry Γ f ≫ (rightAdjoint Γ A).map g :=
  (adjunction Γ A).homEquiv_naturality_right f g

/-- The chosen slice product is the existing family pullback, preserving both
ordinary projections. The pullback choice is unchanged. -/
def familyProduct (A X : Over Γ) : (A ⨯ X).left ≅ pullback A.hom X.hom :=
  Over.prodLeftIsoPullback A X

@[reassoc (attr := simp)] theorem familyProduct_fst (A X : Over Γ) :
    (familyProduct Γ A X).hom ≫ Family.comparison A.hom X.hom = (prod.fst : A ⨯ X ⟶ A).left :=
  Over.prodLeftIsoPullback_hom_fst A X

@[reassoc (attr := simp)] theorem familyProduct_snd (A X : Over Γ) :
    (familyProduct Γ A X).hom ≫ Family.reindex A.hom X.hom = (prod.snd : A ⨯ X ⟶ X).left :=
  Over.prodLeftIsoPullback_hom_snd A X

local instance : (SheafSlice.forward Γ).IsEquivalence :=
  inferInstanceAs (SheafSlice.equivalence Γ).functor.IsEquivalence

/-- Product comparison to the explicit pair sheaf on the element site. -/
def productComparison (A X : Over Γ) :
    (SheafSlice.forward Γ).obj (A ⨯ X) ≅
      SheafRelation.product ((SheafSlice.forward Γ).obj A) ((SheafSlice.forward Γ).obj X) :=
  (SheafSlice.forward Γ).mapIso (productAdapter Γ A X).symm ≪≫
    asIso (CartesianMonoidalCategory.prodComparison (SheafSlice.forward Γ) A X) ≪≫
      (SheafFunction.productComparison _ _).symm

local instance elementClosed : @MonoidalClosed (SheafSlice.ElementSheaves Γ)
    (inferInstance : Category (SheafSlice.ElementSheaves Γ))
    (inferInstance : CartesianMonoidalCategory (SheafSlice.ElementSheaves Γ)).toMonoidalCategory := by
  let h : MonoidalClosed (SheafSlice.ElementSheaves Γ) := inferInstance
  exact h

local instance : MonoidalClosedFunctor (SheafSlice.forward Γ) :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    (SheafSlice.forward Γ) (SheafSlice.equivalence Γ).symm.toAdjunction

/-- The canonical mate comparison is a natural isomorphism, not merely an
objectwise identification of exponential objects. -/
def exponentialComparison (A : Over Γ) :
    rightAdjoint Γ A ⋙ SheafSlice.forward Γ ≅
      SheafSlice.forward Γ ⋙ ihom ((SheafSlice.forward Γ).obj A) :=
  @asIso _ _ _ _ (expComparison (SheafSlice.forward Γ) A)
    (MonoidalClosedFunctor.comparison_iso A)

theorem curry_def {A X B : Over Γ} (f : A ⨯ X ⟶ B) :
    curry Γ f = MonoidalClosed.curry ((productAdapter Γ A X).hom ≫ f) := by
  apply Adjunction.homEquiv_ofNatIsoLeft_apply

theorem uncurry_def {A X B : Over Γ} (f : X ⟶ exponential Γ A B) :
    uncurry Γ f = (productAdapter Γ A X).inv ≫ MonoidalClosed.uncurry f := by
  apply Adjunction.homEquiv_ofNatIsoLeft_symm_apply

@[reassoc (attr := simp)] theorem adapter_fst (A X : Over Γ) :
    (productAdapter Γ A X).hom ≫ prod.fst = CartesianMonoidalCategory.fst A X := by
  simp [productAdapter, CartesianMonoidalCategory.tensorLeftIsoProd]

@[reassoc (attr := simp)] theorem adapter_snd (A X : Over Γ) :
    (productAdapter Γ A X).hom ≫ prod.snd = CartesianMonoidalCategory.snd A X := by
  simp [productAdapter, CartesianMonoidalCategory.tensorLeftIsoProd]

private theorem sheaf_adapter_fst (A X : SheafSlice.ElementSheaves Γ) :
    (SheafFunction.productComparison A X).inv ≫ SheafRelation.fst A X =
      CartesianMonoidalCategory.fst A X := by
  simp only [SheafFunction.productComparison, Iso.trans_inv, Iso.symm_inv,
    SheafRelation.productIso, Category.assoc]
  change (CartesianMonoidalCategory.tensorLeftIsoProd A).hom.app X ≫
    (SheafRelation.lift prod.fst prod.snd ≫ _) = _
  erw [show SheafRelation.lift (prod.fst : A ⨯ X ⟶ A) prod.snd ≫
    SheafRelation.fst A X = prod.fst from rfl]
  simp [CartesianMonoidalCategory.tensorLeftIsoProd]

private theorem sheaf_adapter_snd (A X : SheafSlice.ElementSheaves Γ) :
    (SheafFunction.productComparison A X).inv ≫ SheafRelation.snd A X =
      CartesianMonoidalCategory.snd A X := by
  simp only [SheafFunction.productComparison, Iso.trans_inv, Iso.symm_inv,
    SheafRelation.productIso, Category.assoc]
  change (CartesianMonoidalCategory.tensorLeftIsoProd A).hom.app X ≫
    (SheafRelation.lift prod.fst prod.snd ≫ _) = _
  erw [show SheafRelation.lift (prod.fst : A ⨯ X ⟶ A) prod.snd ≫
    SheafRelation.snd A X = prod.snd from rfl]
  simp [CartesianMonoidalCategory.tensorLeftIsoProd]

@[reassoc (attr := simp)] theorem productComparison_fst (A X : Over Γ) :
    (productComparison Γ A X).hom ≫ SheafRelation.fst _ _ =
      (SheafSlice.forward Γ).map (prod.fst : A ⨯ X ⟶ A) := by
  simp only [productComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, sheaf_adapter_fst,
    CartesianMonoidalCategory.prodComparison_fst, ← Functor.map_comp]
  congr 1
  exact (congrArg (fun k => (productAdapter Γ A X).inv ≫ k) (adapter_fst Γ A X)).symm.trans (by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp])

@[reassoc (attr := simp)] theorem productComparison_snd (A X : Over Γ) :
    (productComparison Γ A X).hom ≫ SheafRelation.snd _ _ =
      (SheafSlice.forward Γ).map (prod.snd : A ⨯ X ⟶ X) := by
  simp only [productComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, sheaf_adapter_snd,
    CartesianMonoidalCategory.prodComparison_snd, ← Functor.map_comp]
  congr 1
  exact (congrArg (fun k => (productAdapter Γ A X).inv ≫ k) (adapter_snd Γ A X)).symm.trans (by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp])

/-- Currying on the actual slice commutes with the existing sheaf curry. -/
theorem curry_comparison {A X B : Over Γ} (f : A ⨯ X ⟶ B) :
    (SheafSlice.forward Γ).map (curry Γ f) ≫ (exponentialComparison Γ A).hom.app B =
      SheafFunction.curry ((productComparison Γ A X).inv ≫ (SheafSlice.forward Γ).map f) := by
  rw [curry_def]
  have h := ClosedComparison.curry_compare (SheafSlice.forward Γ)
    ((productAdapter Γ A X).hom ≫ f)
  dsimp only [exponentialComparison, asIso] at ⊢
  simp only [SheafFunction.curry,
    productComparison, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, asIso_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc] at h ⊢
  exact h

/-- The comparison's target is precisely the existing element-site sheaf
exponential, with its natural (rather than pointwise) sections. -/
def exponentialIso (A B : Over Γ) :
    (SheafSlice.forward Γ).obj (exponential Γ A B) ≅
      SheafFunction.exponential ((SheafSlice.forward Γ).obj A) ((SheafSlice.forward Γ).obj B) :=
  (exponentialComparison Γ A).app B

theorem uncurry_comparison {A X B : Over Γ} (f : X ⟶ exponential Γ A B) :
    SheafFunction.uncurry ((SheafSlice.forward Γ).map f ≫ (exponentialIso Γ A B).hom) =
      (productComparison Γ A X).inv ≫ (SheafSlice.forward Γ).map (uncurry Γ f) := by
  have h := curry_comparison Γ (uncurry Γ f)
  rw [eta] at h
  have hh := congrArg (fun k => SheafFunction.uncurry k) h
  rw [SheafFunction.beta] at hh
  exact hh

theorem evaluation_comparison (A B : Over Γ) :
    SheafFunction.parameterMap ((SheafSlice.forward Γ).obj A) (exponentialIso Γ A B).hom ≫
      SheafFunction.evaluation ((SheafSlice.forward Γ).obj A) ((SheafSlice.forward Γ).obj B) =
      (productComparison Γ A (exponential Γ A B)).inv ≫
        (SheafSlice.forward Γ).map (evaluation Γ A B) := by
  rw [← SheafFunction.uncurry_evaluation]
  have h := uncurry_comparison Γ (𝟙 (exponential Γ A B))
  exact h

theorem evaluation_display (A B : Over Γ) :
    (evaluation Γ A B).left ≫ B.hom = (A ⨯ exponential Γ A B).hom :=
  Over.w (evaluation Γ A B)

theorem evaluation_curry {A X B : Over Γ} (f : A ⨯ X ⟶ B) :
    prod.map (𝟙 A) (curry Γ f) ≫ evaluation Γ A B = f := by
  rw [evaluation, ← uncurry_parameter, Category.comp_id, beta]

/-- Componentwise evaluation of the transported curry. This uses the sheaf
exponential's evaluation; it makes no pointwise-function identification. -/
theorem evaluation_curry_apply {A X B : Over Γ} (f : A ⨯ X ⟶ B)
    (U : (ElementSite.Site Γ.obj)ᵒᵖ)
    (a : ((SheafSlice.forward Γ).obj A).obj.obj U)
    (x : ((SheafSlice.forward Γ).obj X).obj.obj U) :
    (SheafFunction.evaluation ((SheafSlice.forward Γ).obj A) ((SheafSlice.forward Γ).obj B)).hom.app U
      (a, (exponentialIso Γ A B).hom.hom.app U
        (((SheafSlice.forward Γ).map (curry Γ f)).hom.app U x)) =
      ((productComparison Γ A X).inv ≫ (SheafSlice.forward Γ).map f).hom.app U (a, x) := by
  have h := congrArg (fun k => k.hom.app U x) (curry_comparison Γ f)
  change (exponentialIso Γ A B).hom.hom.app U
    (((SheafSlice.forward Γ).map (curry Γ f)).hom.app U x) = _ at h
  rw [h]
  exact SheafFunction.evaluation_curry_apply _ U a x

end SquareKit.SheafSliceFunction

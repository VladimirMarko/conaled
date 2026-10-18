import SquareKit.SheafRelation
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-! Experimental ordinary sheaf function spaces from Mathlib's reflective construction.
For a site with objects in `Type u` and arrows in `Type v`, sections live in
`Type (max u v)`. Mathlib discharges sheafification and presheaf closedness in
these universes. Products below put the argument first, then the parameter.
-/
noncomputable section
namespace SquareKit.SheafFunction
open CategoryTheory MonoidalCategory
open SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A B : Sheaf J (Type (max u v)))

/-- The actual sheaf exponential, not the function type of sections. -/
abbrev exponential : Sheaf J (Type (max u v)) := (ihom A).obj B

/-- Explicit pair sections → chosen categorical product → cartesian tensor. -/
def productComparison : product A B ≅ A ⊗ B :=
  productIso A B ≪≫ ((CartesianMonoidalCategory.tensorLeftIsoProd A).app B).symm

variable {A B} {X Y : Sheaf J (Type (max u v))}

def curry (f : product A X ⟶ B) : X ⟶ exponential A B :=
  MonoidalClosed.curry ((productComparison A X).inv ≫ f)

def uncurry (f : X ⟶ exponential A B) : product A X ⟶ B :=
  (productComparison A X).hom ≫ MonoidalClosed.uncurry f

@[simp] theorem beta (f : product A X ⟶ B) : uncurry (curry f) = f := by
  simp [curry, uncurry]

@[simp] theorem eta (f : X ⟶ exponential A B) : curry (uncurry f) = f := by
  simp [curry, uncurry, ← Category.assoc]

/-- Substitution of the parameter; the argument remains the first coordinate. -/
def parameterMap (A : Sheaf J (Type (max u v))) (g : Y ⟶ X) :
    product A Y ⟶ product A X := lift (fst A Y) (snd A Y ≫ g)

private theorem comparison_natural (g : Y ⟶ X) :
    parameterMap A g ≫ (productComparison A X).hom =
      (productComparison A Y).hom ≫ (A ◁ g) := by
  simp only [productComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := (CartesianMonoidalCategory.tensorLeftIsoProd A).inv.naturality g
  change Limits.prod.map (𝟙 A) g ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd A).app X).inv =
    ((CartesianMonoidalCategory.tensorLeftIsoProd A).app Y).inv ≫ (A ◁ g) at h
  rw [← h]
  simp only [← Category.assoc]
  congr 1
  apply Limits.prod.hom_ext <;> simp [parameterMap, productIso] <;> rfl

theorem curry_parameter (f : product A X ⟶ B) (g : Y ⟶ X) :
    curry (parameterMap A g ≫ f) = g ≫ curry f := by
  have h := comparison_natural (A := A) g
  have h' : (productComparison A Y).inv ≫ parameterMap A g =
      (A ◁ g) ≫ (productComparison A X).inv := by
    apply (cancel_mono (productComparison A X).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  simp only [curry, ← Category.assoc, h']
  simpa only [Category.assoc] using
    (MonoidalClosed.curry_natural_left (A := A) g ((productComparison A X).inv ≫ f))

/-- Evaluation has domain argument × function. -/
def evaluation (A B : Sheaf J (Type (max u v))) :
    product A (exponential A B) ⟶ B := uncurry (𝟙 _)

theorem uncurry_evaluation (f : X ⟶ exponential A B) :
    uncurry f = parameterMap A f ≫ evaluation A B := by
  unfold evaluation uncurry
  rw [← Category.assoc, comparison_natural, Category.assoc,
    ← MonoidalClosed.uncurry_natural_left, Category.comp_id]

theorem evaluation_curry (f : product A X ⟶ B) :
    parameterMap A (curry f) ≫ evaluation A B = f := by
  rw [← uncurry_evaluation, beta]

/-- Beta at any stage, without identifying exponential sections with functions. -/
theorem evaluation_curry_apply (f : product A X ⟶ B) (U : Cᵒᵖ)
    (a : A.obj.obj U) (x : X.obj.obj U) :
    (evaluation A B).hom.app U (a, (curry f).hom.app U x) = f.hom.app U (a, x) :=
  congrArg (fun (k : product A X ⟶ B) => k.hom.app U (a, x)) (evaluation_curry f)
end SquareKit.SheafFunction

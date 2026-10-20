import SquareKit.SheafFunction
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Discrete.SumsProducts

/-! Discrete sheaves and the supported mapping groupoids over arbitrary sheaf
parameters. Mapping out of a discrete sheaf uses the actual product parameter. -/
noncomputable section
namespace SquareKit.DiscreteSheaf
open CategoryTheory Opposite SheafRelation SheafFunction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The discrete inclusion is the sheaf Yoneda functor followed by discrete
categories. Objects at X are actual sheaf maps X → F; their arrows are equalities. -/
def inclusion : (Sheaf J (Type (max u v))) ⥤ (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat :=
  yoneda ⋙ (CategoryTheory.Functor.whiskeringRight _ _ _).obj typeToCat

instance : inclusion (J := J) |>.Faithful := inferInstanceAs
  (yoneda ⋙ (CategoryTheory.Functor.whiskeringRight _ _ _).obj typeToCat).Faithful

instance : inclusion (J := J) |>.Full := inferInstanceAs
  (yoneda ⋙ (CategoryTheory.Functor.whiskeringRight _ _ _).obj typeToCat).Full

abbrev sections (F X : (Sheaf J (Type (max u v)))) := Discrete (X ⟶ F)

def restriction (F : (Sheaf J (Type (max u v)))) {X Y : (Sheaf J (Type (max u v)))} (f : Y ⟶ X) : sections F X ⥤ sections F Y :=
  Discrete.functor (fun m => Discrete.mk (f ≫ m))

/-- The particular mapping object used here retains all sheaf parameters. -/
def parameterFunctor (A : (Sheaf J (Type (max u v)))) : (Sheaf J (Type (max u v))) ⥤ (Sheaf J (Type (max u v))) where
  obj X := product A X
  map f := parameterMap A f
  map_id _ := rfl
  map_comp _ _ := rfl

def mapping (A B : (Sheaf J (Type (max u v)))) : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat :=
  (parameterFunctor A).op ⋙ inclusion.obj B

/-- Currying is the comparison of actual sheaf morphisms, not sectionwise
functions on points. -/
def mappingEquiv (A B X : (Sheaf J (Type (max u v)))) :
    sections (exponential A B) X ≌ sections B (product A X) :=
  Discrete.equivalence {
    toFun := uncurry
    invFun := curry
    left_inv := eta
    right_inv := beta }

/-- The comparison respects restriction by every map of parameter sheaves. -/
theorem uncurry_parameter {A B X Y : (Sheaf J (Type (max u v)))} (f : Y ⟶ X) (h : X ⟶ exponential A B) :
    uncurry (f ≫ h) = parameterMap A f ≫ uncurry h := by
  apply (show Function.Injective (curry (A := A) (B := B) (X := Y)) from
    fun a b hab => (beta a).symm.trans ((congrArg uncurry hab).trans (beta b)))
  rw [eta, curry_parameter, eta]

theorem mappingEquiv_natural {A B X Y : (Sheaf J (Type (max u v)))} (f : Y ⟶ X) :
    restriction (exponential A B) f ⋙ (mappingEquiv A B Y).functor =
      (mappingEquiv A B X).functor ⋙ restriction B (parameterMap A f) := by
  apply CategoryTheory.Functor.ext
  · intro x y g
    apply Subsingleton.elim
  · intro x
    exact congrArg Discrete.mk (uncurry_parameter f x.as)

/-- Currying as an isomorphism of the underlying presheaves of maps. -/
def mappingTypeIso (A B : Sheaf J (Type (max u v))) :
    yoneda.obj (exponential A B) ≅ (parameterFunctor A).op ⋙ yoneda.obj B :=
  NatIso.ofComponents (fun X =>
    (show (X.unop ⟶ exponential A B) ≃ (product A X.unop ⟶ B) from
      { toFun := uncurry, invFun := curry, left_inv := eta, right_inv := beta }).toIso)
    (fun {X Y} f => by
      apply ConcreteCategory.hom_ext
      intro h
      exact uncurry_parameter f.unop h)

/-- The all-parameter comparison is an isomorphism of Cat-valued presheaves. -/
def mappingIso (A B : Sheaf J (Type (max u v))) :
    inclusion.obj (exponential A B) ≅ mapping A B :=
  CategoryTheory.Functor.isoWhiskerRight (mappingTypeIso A B) typeToCat

/-- Evaluation is the counit of precisely this comparison. -/
theorem mapping_evaluation (A B : (Sheaf J (Type (max u v)))) :
    ((mappingEquiv A B (exponential A B)).functor.obj ⟨𝟙 _⟩).as = evaluation A B := rfl

/-- The discrete inclusion preserves the specified binary products, including
both projections. -/
def productEquiv (A B X : (Sheaf J (Type (max u v)))) : sections (product A B) X ≌ sections A X × sections B X :=
  (Discrete.equivalence {
    toFun := fun f => (f ≫ fst A B, f ≫ snd A B)
    invFun := fun f => lift f.1 f.2
    left_inv := by intro f; rfl
    right_inv := by intro f; rfl }).trans Discrete.productEquiv

end SquareKit.DiscreteSheaf

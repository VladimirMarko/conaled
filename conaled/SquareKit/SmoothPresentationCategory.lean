import SquareKit.SmoothElementDescent
import SquareKit.SmoothFormalLocalizationStage
import SquareKit.SmoothLocalizationFreeComparison

/-! Experimental small category of finite smooth presentations.
Objects and all smooth morphisms live in Type. Codes retain their actual quotient
algebras, with no classification claim for arbitrary smooth algebras or manifolds. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory Opposite SmoothAlgebra PresentedLocalization
attribute [local instance] DualExtension.smoothStructure

structure Code where
  arity : ℕ
  relations : ℕ
  equations : Fin relations → Free arity

abbrev Carrier (A : Code) := Presentation.Carrier A.equations
instance (A : Code) : CommRing (Carrier A) := inferInstance
instance (A : Code) : Algebra ℝ (Carrier A) := inferInstance
instance (A : Code) : Structure (Carrier A) := inferInstance

instance : Category Code where
  Hom A B := SmoothAlgebra.Hom (Carrier A) (Carrier B)
  id _ := Hom.ident
  comp f g := Hom.comp g f
  id_comp _ := Hom.comp_ident _
  comp_id _ := Hom.ident_comp _
  assoc _ _ _ := (Hom.comp_assoc _ _ _).symm

abbrev smoothMap {A B : Code} (f : A ⟶ B) : Hom (Carrier A) (Carrier B) := f

def toStage : Code ⥤ SmoothStage.Stage where
  obj A := .presented A.arity A.relations A.equations
  map f := f

def fullyFaithfulToStage : toStage.FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

def free (n : ℕ) : Code := ⟨n,0,noRelations n⟩
def dual (A : Code) : Code :=
  ⟨A.arity+1,A.relations+1,Presentation.relations A.equations (Presentation.dualEquation A.arity)⟩
def localization (A : Code) (s : Carrier A) : Code :=
  ⟨A.arity+1,A.relations+1,Presentation.relations A.equations (equation (representative A.equations s))⟩

def localizationBase (A : Code) (s : Carrier A) : A ⟶ localization A s := atBase A.equations s

def localizationMap {A B : Code} (f : A ⟶ B) (s : Carrier A) :
    localization A s ⟶ localization B ((smoothMap f).toFun s) := atMap A.equations s B.equations f

theorem localization_square {A B : Code} (f : A ⟶ B) (s : Carrier A) :
    localizationBase A s ≫ localizationMap f s = f ≫ localizationBase B ((smoothMap f).toFun s) :=
  map_base A.equations (representative A.equations s) B.equations
    (representative B.equations ((smoothMap f).toFun s)) f (by simp)

/-- The free code represents all finite tuples in every presented target. -/
def freeHomEquiv (n : ℕ) (A : Code) : (free n ⟶ A) ≃ (Fin n → Carrier A) where
  toFun h i := (smoothMap h).toFun (Presentation.projection (noRelations n) (generator i))
  invFun x := Hom.comp (evaluate x) (freeValue n)
  left_inv h := by
    apply Quotient.unique (Presentation.ideal (noRelations n))
    apply hom_ext_generators
    intro i
    exact evaluate_generator _ i
  right_inv x := funext (fun i => evaluate_generator x i)

/-- The dual code has the earlier constructed inverse smooth comparison to actual dual numbers. -/
def dualToActual (A : Code) : Hom (Carrier (dual A)) (DualNumber (Carrier A)) := Presentation.toDual A.equations

def dualFromActual (A : Code) : Hom (DualNumber (Carrier A)) (Carrier (dual A)) := Presentation.fromDual A.equations

theorem dual_comparison_inverse (A : Code) : Hom.comp (dualToActual A) (dualFromActual A)=Hom.ident :=
  Presentation.toDual_fromDual A.equations

theorem dual_comparison_inverse_rev (A : Code) : Hom.comp (dualFromActual A) (dualToActual A)=Hom.ident :=
  Presentation.fromDual_toDual A.equations


end SquareKit.SmoothPresentationSite

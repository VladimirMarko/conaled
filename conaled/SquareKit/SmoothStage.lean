import SquareKit.SmoothDualPresentation
import SquareKit.SheafFunction

/-! Experimental small coded smooth stages with bottom coverage.
Codes live in Type; every represented algebra has carrier in Type. The bundle
of such algebras lives in Type 1. Codes are not claimed to classify presentations.
-/
noncomputable section
namespace SquareKit.SmoothStage
open CategoryTheory Opposite SmoothAlgebra
open SheafRelation SheafFunction

inductive Stage
  | real
  | free (n : ℕ)
  | presented (n m : ℕ) (relations : Fin m → Free n)
  | dual (base : Stage)

structure SmoothObject where
  Carrier : Type
  [commRing : CommRing Carrier]
  [realAlgebra : Algebra ℝ Carrier]
  [smooth : Structure Carrier]
attribute [instance] SmoothObject.commRing SmoothObject.realAlgebra SmoothObject.smooth

def algebra : Stage → SmoothObject
  | .real => ⟨ℝ⟩
  | .free n => ⟨Free n⟩
  | .presented n _ r => ⟨Free n ⧸ Ideal.span (Set.range r)⟩
  | .dual A => let B := algebra A
               { Carrier := DualNumber B.Carrier, smooth := DualExtension.smoothStructure }

abbrev Carrier (A : Stage) := (algebra A).Carrier
instance (A : Stage) : CommRing (Carrier A) := (algebra A).commRing
instance (A : Stage) : _root_.Algebra ℝ (Carrier A) := (algebra A).realAlgebra
instance (A : Stage) : Structure (Carrier A) := (algebra A).smooth

instance : Category Stage where
  Hom A B := SmoothAlgebra.Hom (Carrier A) (Carrier B)
  id _ := Hom.ident
  comp f g := Hom.comp g f
  id_comp _ := Hom.comp_ident _
  comp_id _ := Hom.ident_comp _
  assoc _ _ _ := (Hom.comp_assoc _ _ _).symm

abbrev smoothMap {A B : Stage} (f : A ⟶ B) : Hom (Carrier A) (Carrier B) := f
abbrev ringMap {A B : Stage} (f : A ⟶ B) : Carrier A →+* Carrier B := (smoothMap f).toAlgHom.toRingHom
abbrev Site := Stageᵒᵖ
abbrev topology : GrothendieckTopology Site := ⊥
abbrev scalarData : Siteᵒᵖ ⥤ Type where
  obj A := Carrier A.unop.unop
  map f := ↾(ringMap f.unop.unop)
abbrev scalar : Sheaf topology Type := ⟨scalarData, Presheaf.isSheaf_bot _⟩
abbrev infinitesimalData : Siteᵒᵖ ⥤ Type where
  obj A := {d : Carrier A.unop.unop // d*d=0}
  map f := ↾fun d => ⟨ringMap f.unop.unop d, by rw [← map_mul, d.property, map_zero]⟩
abbrev infinitesimal : Sheaf topology Type := ⟨infinitesimalData, Presheaf.isSheaf_bot _⟩
def inclusion : infinitesimal ⟶ scalar := ⟨{app _ := ↾Subtype.val}⟩

/-- The finite power is the actual tuple presheaf; operations are natural by smoothness. -/
abbrev scalarPower (n : ℕ) : Sheaf topology Type :=
  ⟨{obj A := Fin n → Carrier A.unop.unop, map f := ↾fun z i => ringMap f.unop.unop (z i)},
    Presheaf.isSheaf_bot _⟩
def operation {n : ℕ} (f : Operation n) : scalarPower n ⟶ scalar :=
  ⟨{app _ := ↾fun z => act f z
    naturality _ _ g := by ext z; exact ((smoothMap g.unop.unop).map_act f z).symm}⟩
def add : product scalar scalar ⟶ scalar :=
  ⟨{app _ := ↾fun p => p.1+p.2
    naturality _ _ f := by ext p; exact (map_add (ringMap f.unop.unop) p.1 p.2).symm}⟩
def mul : product scalar scalar ⟶ scalar :=
  ⟨{app _ := ↾fun p => p.1*p.2
    naturality _ _ f := by ext p; exact (map_mul (ringMap f.unop.unop) p.1 p.2).symm}⟩
def affineBody : product infinitesimal (product scalar scalar) ⟶ scalar :=
  ⟨{app _ := ↾fun p => p.2.1+p.2.2*p.1.val
    naturality _ _ f := by
      ext p
      change _ = ringMap f.unop.unop (p.2.1+p.2.2*p.1.val)
      rw [map_add,map_mul]; rfl}⟩
def affine : product scalar scalar ⟶ exponential infinitesimal scalar := curry affineBody

theorem affine_evaluation (A : Stage) (d : Carrier A) (hd : d*d=0) (a b : Carrier A) :
    (evaluation infinitesimal scalar).hom.app (op (op A))
      (⟨d,hd⟩, affine.hom.app (op (op A)) (a,b)) = a+b*d :=
  evaluation_curry_apply affineBody (op (op A)) ⟨d,hd⟩ (a,b)

theorem inclusion_injective (A : Siteᵒᵖ) : Function.Injective (inclusion.hom.app A) :=
  Subtype.val_injective

theorem affine_parameters {X : Sheaf topology Type} (p : X ⟶ product scalar scalar) :
    curry (parameterMap infinitesimal p ≫ affineBody) = p ≫ affine := curry_parameter affineBody p

def dualLift (A B : Stage) :
    (Hom (Carrier A) (Carrier B) × {d : Carrier B // d*d=0}) ≃ Hom (Carrier (.dual A)) (Carrier B) :=
  DualExtension.homEquiv.symm

theorem dualLift_apply (A B : Stage) (f : Hom (Carrier A) (Carrier B))
    (d : {d : Carrier B // d*d=0}) (z : DualNumber (Carrier A)) :
    dualLift A B (f,d) z = f z.fst + f z.snd*d.val := rfl

theorem dualLift_natural (A B C : Stage) (f : Hom (Carrier A) (Carrier B))
    (d : {d : Carrier B // d*d=0}) (g : Hom (Carrier B) (Carrier C)) :
    Hom.comp g (dualLift A B (f,d)) =
      dualLift A C (Hom.comp g f, ⟨g d.val, by change g.toAlgHom d.val*g.toAlgHom d.val=0; rw [← map_mul,d.property,map_zero]⟩) :=
  DualExtension.lift_natural g f d.val d.property

end SquareKit.SmoothStage

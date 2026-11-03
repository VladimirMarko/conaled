import SquareKit.SheafFunction
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-! Experimental small algebraic stages for a presheaf KL construction.
Objects are finite expressions, with all ring homomorphisms between their
interpretations. This module constructs the scalar and the affine exponential
map; it does not assert that this map is an isomorphism.
-/
noncomputable section
namespace SquareKit.AlgebraicStage
open CategoryTheory Opposite
open SheafRelation SheafFunction

inductive Stage
  | integers
  | polynomial (base : Stage)
  | dual (base : Stage)

def algebra : Stage → CommRingCat
  | .integers => CommRingCat.of ℤ
  | .polynomial A => CommRingCat.of (Polynomial (algebra A))
  | .dual A => CommRingCat.of (DualNumber (algebra A))

abbrev Carrier (A : Stage) := algebra A

instance : Category Stage where
  Hom A B := Carrier A →+* Carrier B
  id A := RingHom.id (Carrier A)
  comp f g := g.comp f

abbrev ringMap {A B : Stage} (f : A ⟶ B) : Carrier A →+* Carrier B := f

abbrev Site := Stageᵒᵖ
abbrev topology : GrothendieckTopology Site := ⊥

abbrev scalarData : Siteᵒᵖ ⥤ Type where
  obj A := Carrier A.unop.unop
  map f := ↾(ringMap f.unop.unop)

abbrev scalar : Sheaf topology Type := ⟨scalarData, Presheaf.isSheaf_bot _⟩

abbrev infinitesimalData : Siteᵒᵖ ⥤ Type where
  obj A := {d : Carrier A.unop.unop // d * d = 0}
  map f := ↾fun d => ⟨(ringMap f.unop.unop) d, by rw [← map_mul, d.property, map_zero]⟩

abbrev infinitesimal : Sheaf topology Type :=
  ⟨infinitesimalData, Presheaf.isSheaf_bot _⟩

def inclusion : infinitesimal ⟶ scalar := ⟨{ app _ := ↾Subtype.val }⟩

def add : product scalar scalar ⟶ scalar :=
  ⟨{ app _ := ↾fun p => p.1 + p.2
     naturality _ _ f := by ext p; exact (map_add (ringMap f.unop.unop) p.1 p.2).symm }⟩

def mul : product scalar scalar ⟶ scalar :=
  ⟨{ app _ := ↾fun p => p.1 * p.2
     naturality _ _ f := by ext p; exact (map_mul (ringMap f.unop.unop) p.1 p.2).symm }⟩

def neg : scalar ⟶ scalar :=
  ⟨{ app _ := ↾fun a => -a
     naturality _ _ f := by ext a; exact (map_neg (ringMap f.unop.unop) a).symm }⟩

/-- Argument d precedes the pair of coefficients. -/
def affineBody : product infinitesimal (product scalar scalar) ⟶ scalar :=
  ⟨{ app _ := ↾fun p => p.2.1 + p.2.2 * p.1.val
     naturality _ _ f := by
       ext p
       change _ = (ringMap f.unop.unop) (p.2.1 + p.2.2 * p.1.val)
       rw [map_add, map_mul]
       rfl }⟩

/-- The candidate KL map targets the actual categorical exponential. -/
def affine : product scalar scalar ⟶ exponential infinitesimal scalar := curry affineBody

theorem affine_evaluation (A : Stage) (d : Carrier A) (hd : d * d = 0)
    (a b : Carrier A) :
    (evaluation infinitesimal scalar).hom.app (op (op A))
      (⟨d, hd⟩, affine.hom.app (op (op A)) (a, b)) = a + b * d :=
  evaluation_curry_apply affineBody (op (op A)) ⟨d, hd⟩ (a, b)

/-- Every parameter sheaf, not only global coefficients, can be substituted. -/
theorem affine_parameters {X : Sheaf topology Type} (p : X ⟶ product scalar scalar) :
    curry (parameterMap infinitesimal p ≫ affineBody) = p ≫ affine :=
  curry_parameter affineBody p

abbrev unit : Sheaf topology Type :=
  ⟨(Functor.const Siteᵒᵖ).obj PUnit, Presheaf.isSheaf_bot _⟩

/-- Constant integers, including zero and one, are natural scalar sections. -/
def integer (n : ℤ) : unit ⟶ scalar :=
  ⟨{ app _ := ↾fun _ => n
     naturality _ _ f := by ext; exact (map_intCast (ringMap f.unop.unop) n).symm }⟩

theorem inclusion_injective (A : Siteᵒᵖ) : Function.Injective (inclusion.hom.app A) :=
  Subtype.val_injective

/-- All stage ring maps preserve the scalar ring structure. -/
theorem scalar_ringMap (A B : Stage) (f : A ⟶ B) (a b : Carrier A) :
    ringMap f (a + b) = ringMap f a + ringMap f b ∧
    ringMap f (a * b) = ringMap f a * ringMap f b ∧
    ringMap f (-a) = -ringMap f a ∧ ringMap f 1 = 1 ∧ ringMap f 0 = 0 :=
  ⟨map_add _ _ _, map_mul _ _ _, map_neg _ _, map_one _, map_zero _⟩

/-- The stage extension needed for representable-parameter KL: ring maps
from A[epsilon] correspond to a map from A and a square-zero element. -/
def dualLift (A B : Stage) :
    ((Carrier A →+* Carrier B) × {d : Carrier B // d * d = 0}) ≃
      (Carrier (.dual A) →+* Carrier B) where
  toFun p := (DualNumber.lift (R := ℤ)
    ⟨(p.1.toIntAlgHom, p.2.val), p.2.property, fun _ => Commute.all _ _⟩).toRingHom
  invFun f := (f.comp (algebraMap (Carrier A) (DualNumber (Carrier A))),
    ⟨f DualNumber.eps, by erw [← map_mul, DualNumber.eps_mul_eps, map_zero]⟩)
  left_inv p := by
    apply Prod.ext
    · ext a
      exact congrArg (fun f : Carrier A →ₐ[ℤ] Carrier B => f a)
        (DualNumber.lift_comp_inlHom _)
    · apply Subtype.ext
      exact DualNumber.lift_apply_eps _
  right_inv f := by
    apply DualNumber.ringHom_ext
    · ext a
      exact congrArg (fun g : Carrier A →ₐ[ℤ] Carrier B => g a)
        (DualNumber.lift_comp_inlHom _)
    · exact DualNumber.lift_apply_eps _

theorem dualLift_apply (A B : Stage) (f : Carrier A →+* Carrier B)
    (d : {d : Carrier B // d * d = 0}) (z : DualNumber (Carrier A)) :
    dualLift A B (f, d) z = f z.fst + f z.snd * d.val := rfl

/-- The universal property respects every target-stage restriction. -/
theorem dualLift_natural (A B C : Stage) (f : Carrier A →+* Carrier B)
    (d : {d : Carrier B // d * d = 0}) (g : Carrier B →+* Carrier C) :
    g.comp (dualLift A B (f, d)) =
      dualLift A C (g.comp f, ⟨g d.val, by rw [← map_mul, d.property, map_zero]⟩) := by
  ext z
  change g (f z.fst + f z.snd * d.val) = g (f z.fst) + g (f z.snd) * g d.val
  rw [map_add, map_mul]

end SquareKit.AlgebraicStage

import SquareKit.SmoothGeometricInfinitesimal
import SquareKit.AlgebraicKL

/-! Experimental dual presentation universal property on the geometric site. -/
noncomputable section
namespace SquareKit.SmoothGeometricKL
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite
attribute [local instance] DualExtension.smoothStructure

abbrev atStage (A : Code) : Siteᵒᵖ := op (op A)
abbrev stageMap {A B : Code} (f : A ⟶ B) : atStage A ⟶ atStage B := f.op.op
abbrev inl (A : Code) : A ⟶ dual A := Presentation.dualInclusion A.equations
abbrev eps (A : Code) : infinitesimal.obj.obj (atStage (dual A)) :=
  ⟨Presentation.dualEps A.equations, Presentation.dualEps_square A.equations⟩

def dualLift (A B : Code)
    (f : Hom (Carrier A) (Carrier B)) (d : {d : Carrier B // d*d=0}) : dual A ⟶ B :=
  Hom.comp (DualExtension.lift f d.val d.property) (dualToActual A)

theorem dualLift_inl (A B : Code) (f : Hom (Carrier A) (Carrier B))
    (d : {d : Carrier B // d*d=0}) : inl A ≫ dualLift A B f d = f := by
  change Hom.comp (Hom.comp (DualExtension.lift f d.val d.property) (Presentation.toDual A.equations)) (Presentation.dualInclusion A.equations) = f
  rw [← Hom.comp_assoc, Presentation.toDual_inclusion]
  exact DualExtension.lift_inclusion f d.val d.property

theorem dualLift_eps (A B : Code) (f : Hom (Carrier A) (Carrier B))
    (d : {d : Carrier B // d*d=0}) : (smoothMap (dualLift A B f d)) (eps A).val = d.val := by
  change DualExtension.lift f d.val d.property (Presentation.toDual A.equations (Presentation.dualEps A.equations)) = _
  rw [Presentation.toDual_eps]
  exact DualExtension.lift_eps _ _ _

theorem dual_ext {A B : Code} (f g : dual A ⟶ B)
    (hi : inl A ≫ f = inl A ≫ g)
    (he : (smoothMap f) (eps A).val = (smoothMap g) (eps A).val) : f=g :=
  Presentation.unique _ _ _ _ hi he

abbrev dualMap {A B : Code} (f : A ⟶ B) : dual A ⟶ dual B :=
  dualLift A (dual B) (Hom.comp (inl B) f) (eps B)

theorem dualMap_inl {A B : Code} (f : A ⟶ B) :
    inl A ≫ dualMap f = f ≫ inl B := dualLift_inl _ _ _ _

theorem dualMap_eps {A B : Code} (f : A ⟶ B) :
    infinitesimal.obj.map (stageMap (dualMap f)) (eps A) = eps B :=
  Subtype.ext (dualLift_eps _ _ _ _)

theorem dualMap_actual {A B : Code} (f : A ⟶ B) (z : Carrier (dual A)) :
    dualToActual B ((smoothMap (dualMap f)) z) =
      (⟨ringMap f (dualToActual A z).fst, ringMap f (dualToActual A z).snd⟩ : DualNumber (Carrier B)) := by
  change dualToActual B ((smoothMap (inl B)) ((smoothMap f) (dualToActual A z).fst) +
    (smoothMap (inl B)) ((smoothMap f) (dualToActual A z).snd) * (eps B).val) = _
  rw [Hom.map_add, Hom.map_mul]
  have hi (a : Carrier B) : dualToActual B ((smoothMap (inl B)) a) = TrivSqZeroExt.inl a :=
    congrArg (fun h : Hom (Carrier B) (DualNumber (Carrier B)) => h a) (Presentation.toDual_inclusion B.equations)
  rw [hi, hi]
  change _ + _ * (Presentation.toDual B.equations (Presentation.dualEps B.equations)) = _
  rw [Presentation.toDual_eps]
  exact AlgebraicKL.dual_reconstruct _ _

end SquareKit.SmoothGeometricKL

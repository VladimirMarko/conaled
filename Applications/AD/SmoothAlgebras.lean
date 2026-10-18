import SquareKit.SmoothAlgebra
import Applications.AD.SmoothSquareZero
import Applications.AD.SmoothSecondStage

/-! Experimental packaging of the constructed stages; no alternative stage arithmetic. -/
noncomputable section
namespace Applications.AD.SmoothAlgebras
open SquareKit.SmoothAlgebra

instance realStructure : Structure ℝ where
  act f z := f.val z
  projection _ _ := rfl
  substitute _ _ _ := rfl
  constant _ _ _ := rfl
  addition _ := rfl
  multiplication _ := rfl

instance squareZeroStructure {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module ℝᵐᵒᵖ V] [IsCentralScalar ℝ V] : Structure (TrivSqZeroExt ℝ V) where
  act := SmoothSquareZero.act
  projection := SmoothSquareZero.act_projection
  substitute := SmoothSquareZero.act_substitute
  constant := SmoothSquareZero.act_constant
  addition := SmoothSquareZero.act_addition
  multiplication := SmoothSquareZero.act_multiplication

/-- The real dual ring is the one-dimensional member of the same family. -/
abbrev dualStructure : Structure (DualNumber ℝ) := inferInstance

theorem dual_act {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) :
    act f z = SmoothDual.act f z := SmoothSquareZero.act_real f z

instance secondStructure : Structure SecondStage.Stage where
  act := SmoothSecondStage.act
  projection := SmoothSecondStage.act_projection
  substitute := SmoothSecondStage.act_substitute
  constant := SmoothSecondStage.act_constant
  addition := SmoothSecondStage.act_addition
  multiplication := SmoothSecondStage.act_multiplication

def linear {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℝᵐᵒᵖ V] [IsCentralScalar ℝ V]
    [AddCommGroup W] [Module ℝ W] [Module ℝᵐᵒᵖ W] [IsCentralScalar ℝ W]
    (L : V →ₗ[ℝ] W) : Hom (TrivSqZeroExt ℝ V) (TrivSqZeroExt ℝ W) where
  toFun := SmoothSquareZero.map L
  map_act := SmoothSquareZero.map_act L

def project : Hom SecondStage.Stage (DualNumber ℝ) where
  toFun := SecondStage.project
  map_act f z := (SmoothSecondStage.project_act f z).trans
    (SmoothSquareZero.act_real f (fun i => SecondStage.project (z i))).symm

def reparam (a b : ℝ) : Hom SecondStage.Stage SecondStage.Stage where
  toFun := SecondStage.reparam a b
  map_act := SmoothSecondStage.reparam_act a b

end Applications.AD.SmoothAlgebras

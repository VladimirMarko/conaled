import SquareKit.Internal.PathTransport.ComparisonStructuralModel
import SquareKit.Internal.PathTransport.InterpretationMaps

/-! Both projections preserve the existing structural interpretations. The
primitive signature equations are stated separately and proved, not fields
that a comparison-model client must supply. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
universe u
variable (S : Signature.{u})

def leftProjection : Typed.StructuralMap (structuralModel S)
    (Instance.structuralModel S.base.left S.leftFiber) where
  context Γ := Γ.left
  family A := A.left
  mapTm t := ⟨t.left⟩
  substitution σ := ⟨σ.left⟩
  empty := rfl
  extend _ := rfl
  id _ := rfl
  comp _ _ := rfl
  subTy _ _ := rfl
  subTm _ _ := HEq.rfl
  weaken _ := HEq.rfl
  mapVariable _ := HEq.rfl
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl

def rightProjection : Typed.StructuralMap (structuralModel S)
    (Instance.structuralModel S.base.right S.rightFiber) where
  context Γ := Γ.right
  family A := A.right
  mapTm t := ⟨t.right⟩
  substitution σ := ⟨σ.right⟩
  empty := rfl
  extend _ := rfl
  id _ := rfl
  comp _ _ := rfl
  subTy _ _ := rfl
  subTm _ _ := HEq.rfl
  weaken _ := HEq.rfl
  mapVariable _ := HEq.rfl
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl

theorem left_base (Γ : Context.{u}) :
    (leftProjection S).family ((structuralModel S).base Γ) =
      (Instance.structuralModel S.base.left S.leftFiber).base Γ.left := rfl

theorem right_base (Γ : Context.{u}) :
    (rightProjection S).family ((structuralModel S).base Γ) =
      (Instance.structuralModel S.base.right S.rightFiber).base Γ.right := rfl

theorem left_fiber {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) :
    (leftProjection S).family ((structuralModel S).fiber x) =
      (Instance.structuralModel S.base.left S.leftFiber).fiber ⟨x.left⟩ := rfl

theorem right_fiber {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) :
    (rightProjection S).family ((structuralModel S).fiber x) =
      (Instance.structuralModel S.base.right S.rightFiber).fiber ⟨x.right⟩ := rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

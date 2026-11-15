import Examples.TwoFamilyFrozenPoint
/-! The actual model reflexivity has zero observation, whereas the selected
frozen source homotopy at assignment `1` has nonzero observation. -/
noncomputable section
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoOpenIdentityHigher Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2000
set_option linter.defProp false

theorem model_reflexivity_obj (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) (γ : Γ) :
    HEq ((((fullModel C D).reflexivity A x).down.lift.obj γ).fiber)
      (show LocallyDiscrete ((x.down.lift.obj γ).fiber ⟶ (x.down.lift.obj γ).fiber) from ⟨𝟙 _⟩) :=
  TwoFamily.closedReflexivity_obj A.data x.down γ

def selectedPath := model.subTm (model.subTm (model.subTm
  (parallel model emptyA emptyB).p
  (model.weaken (parallel model emptyA emptyB).context (parallel model emptyA emptyB).identity))
  (model.weaken (homotopyPoints model emptyA emptyB).context (qFamily model emptyA emptyB)))
  (model.weaken (qPoints model emptyA emptyB).context (uFamily model emptyA emptyB))

def selectedReflexivity := (fullModel integerContext integerContext).reflexivity _ selectedPath

def reflexivity_retained (k : ℤ) :=
  model_reflexivity_obj integerContext integerContext _ selectedPath (assignedPoint k)

def reflexivity_observation (k : ℤ) :=
  congrArg (fun t : LocallyDiscrete (Discrete (Multiplicative ℤ)) => t.as.as)
    (@eq_of_heq (LocallyDiscrete (Discrete (Multiplicative ℤ))) _ _ (reflexivity_retained k))

private theorem neq_of_observed {α : Sort*} {a b c d : α}
    (ha : c = a) (hb : d = b) (h : c ≠ d) : a ≠ b := by
  intro e
  exact h (ha.trans (e.trans hb.symm))

def selected_ne_reflexivity := neq_of_observed (observation 1).symm
  (reflexivity_observation 1).symm
  (show Multiplicative.ofAdd (1:ℤ) ≠ Multiplicative.ofAdd 0 from
    fun e => Int.one_ne_zero (congrArg Multiplicative.toAdd e))
end Examples.TwoFamilyFrozenPoint

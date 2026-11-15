import Examples.FrozenMemoSubstitutions
import Examples.FrozenMemoInput

/-! A concrete specialization of the shared client in the integer translation
model. Its dependency on the input value excludes erasing the selected value. -/
noncomputable section
namespace Examples.FrozenMemoRealizationExamples
open SquareKit.Internal.DependentJudgments
open Examples.GuardedGroupoidMemo
open Examples.FrozenMemoRealization
local notation "IM" => SquareKit.Internal.PathTransport.GroupoidModel.Instance.fullModel Integers translation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false

noncomputable def input : FrozenMemoRealization.InputRealization IM environment signature.input where
  context := realization.context
  family := SquareKit.Internal.PathTransport.GroupoidModel.constant Integers
  fiber := SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics.Groupoid.genericFiber
    Integers translation realization.context
  x := ⟨realization.x⟩
  y := ⟨realization.y⟩
  z := ⟨realization.z⟩
  p := ⟨realization.p⟩
  p' := ⟨realization.p'⟩
  h := ⟨realization.h⟩
  q := ⟨realization.q⟩
  element := ⟨realization.element⟩
  context_eval := realization.context_eval
  family_eval := realization.family_eval
  fiber_eval := realization.fiber_eval
  x_eval := realization.x_eval
  y_eval := realization.y_eval
  z_eval := realization.z_eval
  p_eval := realization.p_eval
  p'_eval := realization.p'_eval
  h_eval := realization.h_eval
  q_eval := realization.q_eval
  element_eval := realization.element_eval

theorem selected_value (p q b : Int) :
    (input.selectedValue.down.obj (assignment p q b)).as = q + (p + b) := by
  have e := generated_value p q b
  change Option.map _ (Value.termAt input.context
    ((IM).subTy input.fiber ((IM).toStructuralModel.sectionSub input.family input.z))
    ((signature.input.parameters.value signature.input.p).eval
    (Contextual.algebra IM) environment)) = _ at e
  rw [input.value_eval inputs] at e
  simpa only [Value.termAt_term, Option.map_some, Option.some.injEq] using e

theorem selected_three :
    (input.selectedValue.down.obj (assignment 1 2 0)).as = (3 : Int) := selected_value 1 2 0

theorem erasure_rejected :
    (input.selectedValue.down.obj (assignment 1 2 0)).as ≠ (0 : Int) := by
  rw [selected_three]
  exact (by decide : (3 : Int) ≠ 0)

end Examples.FrozenMemoRealizationExamples

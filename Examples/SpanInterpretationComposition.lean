import SquareKit.SpanInterpretationComposition
import Examples.SpanInterpretation

/-! Invertible modifications preserve the existing nontrivial selected-witness client. -/
noncomputable section
namespace Examples.SpanInterpretationComposition
open CategoryTheory Limits ConcreteCategory SquareKit SpanAction SpanInterpretation
open Examples.SpanInterpretation
open scoped Pseudofunctor.StrongTrans

/-- The modification, rather than a separate component proof, connects successive images
with the independently specified source payload and apex. -/
theorem selected_successive :
    (((actionIso second (span first selectedSpan)).hom.app ((Over.post first).obj values)).left)
      (second.map ((actionIso first selectedSpan).hom.app values).left sourceInput) = nativeInput := by
  have h := congr_hom
    (compositionModification_naturality first second selectedSpan values) sourceInput
  exact h.symm.trans output

theorem selected_payload :
    pullback.fst (both.map values.hom) (both.map selectedSpan.l)
      ((((actionIso second (span first selectedSpan)).hom.app ((Over.post first).obj values)).left)
      (second.map ((actionIso first selectedSpan).hom.app values).left sourceInput)) = payload := by
  rw [selected_successive]
  exact IndexedSumBaseChange.encode_value interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩

theorem selected_apex :
    pullback.snd (both.map values.hom) (both.map selectedSpan.l)
      ((((actionIso second (span first selectedSpan)).hom.app ((Over.post first).obj values)).left)
      (second.map ((actionIso first selectedSpan).hom.app values).left sourceInput)) = (3,true) := by
  rw [selected_successive]
  exact IndexedSumBaseChange.encode_base interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩

/-- A third, nonidentity forgetful interpretation removes one more slice layer. -/
abbrev outer : Over nestedBase ⥤ Over base := Over.forget nestedBase
abbrev deepBase : Over nestedBase := Over.mk (𝟙 nestedBase)
abbrev deepDisplayed : Over nestedBase := Over.mk selectedSpan.l
abbrev deepSpan : Spans deepBase deepBase :=
  ⟨deepDisplayed, Over.homMk selectedSpan.l, Over.homMk selectedSpan.l, trivial, trivial⟩
abbrev deepValues : Over deepBase := Over.mk (Over.homMk values.hom)
abbrev triple := outer ⋙ first ⋙ second
abbrev deepInterpreted := span triple deepSpan
abbrev deepInterpretedValues := (Over.post triple).obj deepValues

def deepNativeInput : (action deepInterpreted).obj deepInterpretedValues |>.left :=
  IndexedSumBaseChange.encode deepInterpreted.l deepInterpretedValues (3,true) ⟨payload,rfl⟩
def deepSourceInput : triple.obj ((action deepSpan).obj deepValues).left :=
  ((actionIso triple deepSpan).inv.app deepValues).left deepNativeInput

theorem deep_output :
    ((actionIso triple deepSpan).hom.app deepValues).left deepSourceInput = deepNativeInput :=
  congr_hom (congrArg CommaMorphism.left
    ((actionIso triple deepSpan).inv_hom_id_app deepValues)) deepNativeInput

theorem deep_source_value :
    triple.map (pullback.fst deepValues.hom deepSpan.l) deepSourceInput = payload := by
  have h := congr_hom (action_value triple deepSpan deepValues) deepSourceInput
  rw [← h]
  change pullback.fst (triple.map deepValues.hom) (triple.map deepSpan.l)
    (((actionIso triple deepSpan).hom.app deepValues).left deepSourceInput) = payload
  rw [deep_output]
  exact IndexedSumBaseChange.encode_value _ _ (3,true) ⟨payload,rfl⟩

theorem deep_source_apex :
    triple.map (pullback.snd deepValues.hom deepSpan.l) deepSourceInput = (3,true) := by
  have h := congr_hom (action_apex triple deepSpan deepValues) deepSourceInput
  rw [← h]
  change pullback.snd (triple.map deepValues.hom) (triple.map deepSpan.l)
    (((actionIso triple deepSpan).hom.app deepValues).left deepSourceInput) = (3,true)
  rw [deep_output]
  exact IndexedSumBaseChange.encode_base _ _ (3,true) ⟨payload,rfl⟩

/-- All three comparisons preserve the specified dependent payload and apex. -/
theorem deep_successive :
    ((actionIso second (span first (span outer deepSpan))).hom.app
      ((Over.post first).obj ((Over.post outer).obj deepValues))).left
      (second.map ((actionIso first (span outer deepSpan)).hom.app
        ((Over.post outer).obj deepValues)).left
        (second.map (first.map ((actionIso outer deepSpan).hom.app deepValues).left)
          deepSourceInput)) = deepNativeInput := by
  have h := congr_hom
    (compositionModification_naturality outer (first ⋙ second) deepSpan deepValues) deepSourceInput
  have k := congr_hom
    (compositionModification_naturality first second (span outer deepSpan)
      ((Over.post outer).obj deepValues))
    (second.map (first.map ((actionIso outer deepSpan).hom.app deepValues).left) deepSourceInput)
  exact k.symm.trans (h.symm.trans deep_output)

/-- Reassociation agrees on the complete selected source object, not just its base map. -/
theorem selected_reassociation :
    (((tripleComparisonLeft outer first second).hom.as.app ⟨deepBase⟩).toNatTrans.app
      ((action deepSpan).obj deepValues)).left deepSourceInput =
    (((tripleComparisonRight outer first second).hom.as.app ⟨deepBase⟩).toNatTrans.app
      ((action deepSpan).obj deepValues)).left deepSourceInput := by
  rw [composition_associativity]

example : tripleComparisonLeft outer first second = tripleComparisonRight outer first second :=
  composition_associativity outer first second
example := composition_left_unit both
example := composition_right_unit both

example : ¬ PreservesFiniteLimits second := MatesBaseChange.forget_not_leftExact
example : ¬ PreservesLimitsOfShape WalkingCospan truncation := truncation_not_preserving
end Examples.SpanInterpretationComposition

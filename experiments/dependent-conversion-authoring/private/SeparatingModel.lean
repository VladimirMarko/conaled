import Examples.ConversionTrial.Negative
import Examples.DependentFunctionSource

/-! Independent finite semantic oracle for this trial's two free-function fixture.
No normalizer, conversion decider, or service reference is imported. -/
noncomputable section
namespace Examples.ConversionTrial.SeparatingModel
open CategoryTheory Limits Opposite SquareKit
open Internal.DependentFunctions Internal.DependentFunctions.SheafSem
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies
open Examples.DependentFunctionSource (finiteModel finiteEnv finiteSection)
open Negative

def environment : Env finiteModel two where
  carrier := D
  base _ := 𝟙 D
  dep
    | .function (.function .top) => evalDep finiteModel (finiteEnv false) .point
    | .function (.function (.family (.base v))) => nomatch v
  func
    | .top => (finiteEnv true).func .top
    | .function .top => (finiteEnv false).func .top
    | .function (.function (.family (.base v))) => nomatch v

set_option maxHeartbeats 800000 in
private theorem observation (h : FuncEq newest older) :
    (finiteSection true).val (D.obj.elementsMk (op X) false) =
      (finiteSection false).val (D.obj.elementsMk (op X) false) := by
  have he := dep_sound finiteModel (DepEq.app h (.zero)) environment
  have ht := DependentFunctionSource.parameter_application finiteModel (finiteSection true) (.zero)
  have hf := DependentFunctionSource.parameter_application finiteModel (finiteSection false) (.zero)
  have hv := (heq_of_eq ht).symm.trans (he.trans (heq_of_eq hf))
  exact congrArg (fun t => t.val (D.obj.elementsMk (op X) false)) (eq_of_heq hv)

private theorem unequal_sections :
    (finiteSection true).val (D.obj.elementsMk (op X) false) ≠
      (finiteSection false).val (D.obj.elementsMk (op X) false) := by
  intro hs
  let a : SplitDependentFunctions.argument.family.obj (D.obj.elementsMk (op X) false) :=
    SplitDependentFunctions.falseArgument.val (SheafImage.terminal.obj.elementsMk (op X) ())
  have ho := congrArg (fun f =>
    (pullback.fst base (SplitSheaf.displayIso falsePoint).hom).hom.app (op X)
      (SplitFunctionDiagram.evaluate SplitDependentFunctions.argument.family
        SplitDependentFunctions.result.family (D.obj.elementsMk (op X) false) f a).val) hs
  have ht := SplitDependentFunctions.lambda_false X true a
  have hf := SplitDependentFunctions.lambda_false X false a
  exact Bool.noConfusion (ht.symm.trans (ho.trans hf))

theorem head_negative : HeadTask :=
  ⟨rfl, fun h => unequal_sections (observation h)⟩
end Examples.ConversionTrial.SeparatingModel

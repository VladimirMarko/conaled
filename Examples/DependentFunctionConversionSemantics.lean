import Examples.DependentFunctionConversion
import Examples.DependentFunctionSource

/-! Converter proofs consumed by existing interpretation and ordinary dependent
function results. The finite separating observation does not run the converter. -/
noncomputable section
namespace Examples.DependentFunctionConversionSemantics
open CategoryTheory Limits Opposite SquareKit
open Internal.DependentFunctions Internal.DependentFunctions.SheafSem
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies
open Examples.DependentFunctionConversion
open Examples.DependentFunctionSource (finiteModel finiteEnv finiteSection parameterEnv)

 theorem interpreted {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (E : Env M Γ) :
    HEq (evalDep M E generated) (evalDep M E expected) := dep_sound M service_beta E

 theorem ordinary {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (M : Model J) (E : Env M Γ) :
    HEq (ordinaryApplication M E (.lam body) (.neg (.var 0))) (evalDep M E expected) := by
  exact (heq_of_eq (ordinary_application M E (.lam body) (.neg (.var 0)))).trans (interpreted M E)

-- Both free functions are legal, with distinct existing finite interpretations.
def separatingEnv : Env finiteModel two where
  carrier := D
  base _ := 𝟙 D
  dep | .function (.function (.base v)) => nomatch v
  func
    | .top => (finiteEnv true).func .top
    | .function .top => (finiteEnv false).func .top
    | .function (.function (.base v)) => nomatch v

-- Kernel comparison unfolds the existing dependent sheaf presentations.
set_option maxHeartbeats 800000 in
private theorem heads_observation (h : FuncEq newest older) :
    (finiteSection true).val (D.obj.elementsMk (op X) false) =
      (finiteSection false).val (D.obj.elementsMk (op X) false) := by
  have he := dep_sound finiteModel (DepEq.app h (.zero)) separatingEnv
  have ht := DependentFunctionSource.parameter_application finiteModel (finiteSection true)
    (.zero)
  have hf := DependentFunctionSource.parameter_application finiteModel (finiteSection false)
    (.zero)
  have hv := (heq_of_eq ht).symm.trans (he.trans (heq_of_eq hf))
  exact congrArg (fun t => t.val (D.obj.elementsMk (op X) false)) (eq_of_heq hv)

private theorem finite_sections_separate :
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

theorem heads_separated : ¬ FuncEq newest older :=
  fun h => finite_sections_separate (heads_observation h)

end Examples.DependentFunctionConversionSemantics

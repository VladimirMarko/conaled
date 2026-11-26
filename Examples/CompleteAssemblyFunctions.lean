import Examples.InternalIteration
import SquareKit.AssemblyLiftNatComplete
import SquareKit.AssemblyCompleteClosure

/-! Concrete selection and function-object cases with constructed completeness. -/
namespace CompleteAssemblyFunctions
open Realizability Realizability.Assembly InternalIteration

/-- The formerly conditional selection now uses the constructed complete object. -/
example : (cutSelected liftedNaturals programLift_encoded_nat_cutComplete chooseParameter).toFun (17 : Nat) =
    some (17 : Nat) := parameter_selected_keeps_seventeen programLift_encoded_nat_cutComplete

example : (cutSelected liftedNaturals programLift_encoded_nat_cutComplete (snd unitAssembly (programLift natAssembly))).toFun () = none :=
  identity_selection_is_bottom programLift_encoded_nat_cutComplete

example : (cutSelected liftedNaturals programLift_encoded_nat_cutComplete chooseParameter).comp successorLiftHom.f =
    cutSelected liftedNaturals programLift_encoded_nat_cutComplete chooseNextParameter :=
  cutSelected_transport _ _ programLift_encoded_nat_cutComplete programLift_encoded_nat_cutComplete successorLiftHom _ _ parameter_intertwines

example : CutComplete (function natAssembly (programLift natAssembly)) := function_cutComplete programLift_encoded_nat_cutComplete natAssembly

/-- The isomorphism inverse really reconstructs each selected coordinate. -/
example (f : Hom iterationCuts.{0} (programLift natAssembly)) (n : Nat) :
    (((cutRestrictionIso programLift_encoded_nat_cutComplete).inv.toFun f).toFun ⟨some n⟩) = f.toFun ⟨n⟩ :=
  (curry_apply _ _ _).trans (cutExtend_value programLift_encoded_nat_cutComplete (evaluation _ _) f n)

example : (cutExtend nat_cutComplete ((fst natAssembly iterationCuts).comp successor)).toFun
    ((17 : Nat), ⟨none⟩) = (18 : Nat) := by
  have he : (fst natAssembly finalCuts).comp successor =
      cutExtend nat_cutComplete ((fst natAssembly iterationCuts).comp successor) :=
    cutExtend_unique nat_cutComplete _ _ (Hom.ext fun _ => rfl)
  exact (congrArg (fun f => f.toFun ((17 : Nat), ⟨none⟩)) he).symm

end CompleteAssemblyFunctions

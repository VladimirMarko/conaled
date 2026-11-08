import Examples.InternalIteration
import SquareKit.AssemblyLiftNatComplete
import SquareKit.AssemblyCompleteClosure

/-! Concrete selection and function-object cases with constructed completeness. -/
namespace CompleteAssemblyFunctions
open Realizability Realizability.Assembly InternalIteration

/-- The formerly conditional selection now uses the constructed complete object. -/
example : (cutSelected liftedNaturals liftNat_cutComplete chooseParameter).toFun (17 : Nat) =
    some (17 : Nat) := parameter_selected_keeps_seventeen liftNat_cutComplete

example : (cutSelected liftedNaturals liftNat_cutComplete (snd U (programLift N))).toFun () = none :=
  identity_selection_is_bottom liftNat_cutComplete

example : (cutSelected liftedNaturals liftNat_cutComplete chooseParameter).comp successorLiftHom.f =
    cutSelected liftedNaturals liftNat_cutComplete chooseNextParameter :=
  cutSelected_transport _ _ liftNat_cutComplete liftNat_cutComplete successorLiftHom _ _ parameter_intertwines

example : CutComplete (function N (programLift N)) := function_cutComplete liftNat_cutComplete N

/-- The isomorphism inverse really reconstructs each selected coordinate. -/
example (f : Hom iterationCuts.{0} (programLift N)) (n : Nat) :
    (((cutRestrictionIso liftNat_cutComplete).inv.toFun f).toFun ⟨some n⟩) = f.toFun ⟨n⟩ :=
  (curry_apply _ _ _).trans (cutExtend_value liftNat_cutComplete (evaluation _ _) f n)

example : (cutExtend nat_cutComplete ((fst N iterationCuts).comp successor)).toFun
    ((17 : Nat), ⟨none⟩) = (18 : Nat) := by
  have he : (fst N finalCuts).comp successor =
      cutExtend nat_cutComplete ((fst N iterationCuts).comp successor) :=
    cutExtend_unique nat_cutComplete _ _ (Hom.ext fun _ => rfl)
  exact (congrArg (fun f => f.toFun ((17 : Nat), ⟨none⟩)) he).symm

end CompleteAssemblyFunctions

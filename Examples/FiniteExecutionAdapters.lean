import Applications.FRP.ExecutionFusion
import Applications.Resources.FIFOExecutionFusion
import Applications.Languages.WordPathObservation
import Examples.ReactivePipeline
import Examples.DepthObservation

/-! Retained native expectations exercised through the shared adapters. -/
namespace Examples.FiniteExecutionAdapters
open FRPSpec.Frontier Progress
open ReactivePipeline

theorem native_pipeline_events :
    (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) FRPEngine.script).2 =
      [(none,none),(none,none),(none,none),(none,none),(some (2,[3,4,3]),some (1,10))] := by
  rw [Pipeline.run_factor_via_fusion]
  decide

theorem native_pipeline_state :
    (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) FRPEngine.script).1.consumer =
      (1,10) := by
  rw [Pipeline.run_factor_via_fusion]
  decide

open Sequences.AbstractFIFO Resources.FIFOContracts in
example :
    (Resources.run redundantInstrumentation.measured
      [.enqueue 4,.enqueue 7,.delete] (([2] : List Nat),99)).1.1 = [4,7] := by
  rw [redundant_run]
  rfl

/-- Forgetting silence loses positions even when emitted values agree. -/
example : ([some (3 : Nat),none].filterMap id = [none,some 3].filterMap id) ∧
    [some (3 : Nat),none] ≠ [none,some 3] := by decide

end Examples.FiniteExecutionAdapters

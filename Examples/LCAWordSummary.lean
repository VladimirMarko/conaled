import Applications.Sequences.LCA.WordSummary
import Examples.LCAPhases

set_option autoImplicit false
set_option warningAsError true

namespace Examples.LCAWordSummary
open Sequences.LCA TreeReduction PreparationBounds PackedBackend WordSummary
open LCABackend LCAPhases

-- A singleton still follows the physical log/descriptor/span/payload path.
example : (run 1 (arena singletonInput (BackendBounds.machine_arena singletonMachine)) 0 0).1.val = 0 := by
  rw [run_value singletonInput _ 0 0 (by decide)]
  decide

-- Five macro blocks use overlapping length-four dyadic intervals. The packed
-- result retains the global Euler position, rather than a local row offset.
example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (run 17 (arena deepInput h) 1 4).1.val = 38 := by
  rw [run_value deepInput h 1 4 (by decide)]
  decide

example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (run 17 (arena deepInput h) 1 4).2 = 13 := run_cost _ _ _ _

example : KeyBounds.Fits 0 34 (paddedCapacity 17)
    (BlockedRMQ.summary (state deepInput) (blocks_pos 17) 8 0) :=
  summary_fits deepInput 8 0 (by decide)

end Examples.LCAWordSummary

import Applications.Sequences.LCA.WordQuery
import Examples.LCAWordSummary

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

namespace Examples.LCAWordQuery
open Sequences.LCA PackedBackend WordQuery
open LCABackend LCAPhases

-- Initialization is independent of every later endpoint pair.
example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (answer 17 (arena deepInput h) 3 13).1.val = 3 := by
  rw [answer_spec]
  decide

-- The final short block uses upward padding, but returns an original index.
example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (answer 17 (arena deepInput h) 15 16).1.val = 16 := by
  rw [answer_spec]
  decide

-- A repeated minimum is resolved to its leftmost Euler occurrence.
example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (answer 17 (arena deepInput h) 0 16).1.val = 0 := by
  rw [answer_spec]
  decide

example {width capacity inputWords frameWords : Nat}
    (h : MachineCapacity.Eligible 17 width capacity inputWords frameWords) :
    (answer 17 (arena deepInput h) 16 15).1.val = 0 := by
  rw [answer_spec]
  decide

-- The concrete one-node machine instantiates the complete execution theorem.
example : (answer 1 (arena singletonInput
    (BackendBounds.machine_arena singletonMachine)) 0 0).1.val = 0 := by
  rw [answer_spec]
  decide

example {width capacity : Nat} (mem : Dijkstra.Store.Store capacity (WordMachine.Word width))
    (lo hi : Nat) : (answer 17 mem lo hi).2 ≤ 57 := answer_cost _ _ _ _

end Examples.LCAWordQuery

import Applications.Sequences.SharedList.IntegerUpdate

/-! Source integer edge cases, connected to the shared-cell execution theorems. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedListIntegers
open Sequences.SharedList

/-- Negative indices traverse three cells and the terminal empty root. -/
theorem negative_traversal :
    updateIntegerRun (load [1, 2, 3]).1 (load [1, 2, 3]).2 (-1) 7 = (none, 4) :=
  updateIntegerRun_negative (load_represents [1, 2, 3]) (by decide) 7

theorem very_negative_traversal :
    updateIntegerRun (load [1, 2, 3]).1 (load [1, 2, 3]).2 (-20) 7 = (none, 4) :=
  updateIntegerRun_negative (load_represents [1, 2, 3]) (by decide) 7

/-- The successful integer call reuses the original path-copy theorem in full. -/
theorem replace_second : ∃ out,
    updateIntegerRun (load [1, 2, 3]).1 (load [1, 2, 3]).2 1 7 = (some out, 2) ∧
    Durability.Extends (load [1, 2, 3]).1.heap out.1.heap ∧
    Represents out.1.heap out.2 [1, 7, 3] ∧ out.1.next = 5 ∧
    advance 2 out.1 out.2 = advance 2 (load [1, 2, 3]).1 (load [1, 2, 3]).2 :=
  updateIntegerRun_success (load_represents [1, 2, 3]) (i := 1) (by decide) 7

end Examples.SharedListIntegers

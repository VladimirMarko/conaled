import Applications.Sequences.AbstractStack

/-! Checked specializations of the operation-only stack contracts. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AbstractStack
open Sequences.AbstractStack

private def left : Stack Nat := .cons 1 (.cons 2 .nil)
private def right : Stack Nat := .cons 3 .nil

/-- Both list and custom implementations exercise the same generic algorithm. -/
theorem list_append : appendRun (lists Nat) 2 [1, 2] [3] = (some [1, 2, 3], 9) :=
  lists_appendRun [1, 2] [3] (by decide)

theorem custom_append : ∃ r, appendRun (custom Nat) 2 left right = (some r, 9) ∧
    r.toList = [1, 2, 3] :=
  custom_appendRun (by decide : left.toList.length ≤ 2)

/-- The observable client is proved by composition, not a second append proof. -/
theorem custom_append_head :
    ((appendRun (custom Nat) 2 left right).1.bind (custom Nat).head) = some 1 :=
  appendHead_correct (custom_laws Nat) (xs := [1, 2]) (ys := [3]) rfl rfl (by decide)

theorem empty_tail_fails : (custom Nat).tail .nil = none :=
  (custom_laws Nat).tail_nil _ rfl

/-- Successful empty tail is distinct from failure. -/
theorem singleton_tail_succeeds : ∃ r, (custom Nat).tail (.cons 4 .nil) = some r ∧
    r.toList = [] :=
  (custom_laws Nat).tail_cons _ 4 [] rfl

/-- Extra fuel does not change either the observation or primitive count. -/
theorem excess_fuel : appendRun (lists Nat) 8 [1, 2] [3] = (some [1, 2, 3], 9) :=
  lists_appendRun [1, 2] [3] (by decide)

/-- The empty left input needs no recursive fuel and calls only `isEmpty`. -/
theorem empty_append : appendRun (lists Nat) 0 [] [3] = (some [3], 1) :=
  lists_appendRun [] [3] (by decide)

end Examples.AbstractStack

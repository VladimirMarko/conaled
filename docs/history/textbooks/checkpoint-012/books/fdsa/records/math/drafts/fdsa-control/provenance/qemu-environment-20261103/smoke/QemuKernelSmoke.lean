import Init

namespace FdsaEnvironmentSmoke

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem successor_addition (n : Nat) : n + 1 = Nat.succ n := by
  rfl

#print axioms zero_add
#print axioms successor_addition

end FdsaEnvironmentSmoke

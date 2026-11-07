import Mathlib.Order.OmegaCompletePartialOrder

/-! Least selected solutions and their transport through strict continuous maps.
The selection is the supremum of finite approximants, not an arbitrary fixed point.
-/
namespace SelectedFixedPoint
open OmegaCompletePartialOrder

variable {α β : Type*} [OmegaCompletePartialOrder α] [OrderBot α]
  [OmegaCompletePartialOrder β] [OrderBot β]

/-- Finite approximation starting with no information. -/
def approximants (f : α →𝒄 α) : Chain α :=
  fixedPoints.iterateChain f ⊥ bot_le

/-- The selected least solution. -/
noncomputable def solution (f : α →𝒄 α) : α := ωSup (approximants f)

theorem solution_fixed (f : α →𝒄 α) : f (solution f) = solution f :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

theorem solution_le (f : α →𝒄 α) {x : α} (hx : f x ≤ x) : solution f ≤ x :=
  fixedPoints.ωSup_iterate_le_prefixedPoint f ⊥ bot_le hx bot_le

/-- Intertwining transports each finite approximation when the map preserves bottom. -/
theorem map_approximants (f : α →𝒄 α) (g : β →𝒄 β) (h : α →𝒄 β)
    (hbot : h ⊥ = ⊥) (comm : ∀ x, h (f x) = g (h x)) (n : Nat) :
    h (approximants f n) = approximants g n := by
  induction n with
  | zero => exact hbot
  | succ n ih =>
    change h (f^[n+1] ⊥) = g^[n+1] ⊥
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', comm]
    exact congrArg g ih

/-- Continuity and strictness preserve the selected least fixed point. -/
theorem map_solution (f : α →𝒄 α) (g : β →𝒄 β) (h : α →𝒄 β)
    (hbot : h ⊥ = ⊥) (comm : ∀ x, h (f x) = g (h x)) :
    h (solution f) = solution g := by
  rw [solution, h.continuous]
  congr 1
  ext n
  exact map_approximants f g h hbot comm n

end SelectedFixedPoint

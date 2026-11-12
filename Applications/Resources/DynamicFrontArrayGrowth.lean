import Applications.Resources.DynamicFrontArrayCosts

/-! Geometric growth derived from actual eager insertion, with precise spare-space hypotheses. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DynamicFrontArrays.Eager
universe u
variable {α : Type u}

theorem add_dense (x : α) {s : State α} {ys : List α} (h : Layout s ys)
    (hcap : s.slots.size ≤ 2 * ys.length + 1) :
    (add x s).1.slots.size ≤ 2 * (ys.length + 1) := by
  have hs := layout_size h
  rw [add_size]
  split <;> omega

theorem adds_dense (xs : List α) {s : State α} {ys : List α} (h : Layout s ys)
    (hcap : s.slots.size ≤ 2 * ys.length) :
    (adds xs s).1.slots.size ≤ 2 * (xs.length + ys.length) := by
  induction xs generalizing s ys with
  | nil => simpa [adds_nil, adds_cons] using hcap
  | cons x xs ih =>
      have hc := add_dense x h (by omega)
      have hr := ih (add_layout x h) (by simpa only [List.length_cons] using hc)
      simp only [List.length_cons] at hr
      simp only [adds_cons, List.length_cons]
      omega

theorem from_empty_capacity_upper (xs : List α) (hne : xs ≠ []) :
    (adds xs empty).1.slots.size ≤ 2 * xs.length := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      have hc := add_dense x empty_layout (by simp [empty])
      have hr := adds_dense xs (add_layout x empty_layout)
        (by simpa only [List.length_cons] using hc)
      simpa [adds_nil, adds_cons] using hr

/-- Count resize events, independently from their slot payloads. -/
def growths : List (Event α) → Nat
  | [] => 0
  | .allocate _ :: es => 1 + growths es
  | .copy _ _ :: es => growths es
  | .write _ _ :: es => growths es

theorem growths_append (es fs : List (Event α)) :
    growths (es ++ fs) = growths es + growths fs := by
  induction es with
  | nil => simp [growths]
  | cons e es ih => cases e <;> simp [growths, ih, Nat.add_assoc]

theorem copyInto_growths (vs : List (Option α)) (i : Nat) (dst : Array (Option α)) :
    growths (copyInto vs i dst).2 = 0 := by
  induction vs generalizing i dst with
  | nil => rfl
  | cons v vs ih => simp [copyInto, growths, ih]

theorem add_growths (x : α) (s : State α) :
    growths (add x s).2 = if s.free ≤ 1 then 1 else 0 := by
  by_cases h : s.free ≤ 1 <;>
    simp [add, h, growths_append, grow, growths, copyInto_growths, writeFront]

/-- Exact accounting behind the eager geometric schedule, with the boundary
convention and the resize count left explicit. -/
theorem add_balance (x : α) {s : State α} {xs : List α}
    (h : Layout s xs) (hfree : 0 < s.free) :
    work (add x s).2 + growths (add x s).2 + s.slots.size =
      1 + (add x s).1.slots.size := by
  rw [add_work, add_growths, add_size]
  have hp := h.1
  split <;> omega

theorem adds_balance (xs : List α) {s : State α} {ys : List α}
    (h : Layout s ys) (hfree : 0 < s.free) :
    work (adds xs s).2 + growths (adds xs s).2 + s.slots.size =
      xs.length + (adds xs s).1.slots.size := by
  induction xs generalizing s ys with
  | nil => simp [adds_nil, work, growths]
  | cons x xs ih =>
      have ha := add_balance x h hfree
      have hr := ih (add_layout x h) (add_spare x h hfree)
      simp only [adds_cons, work_append, growths_append, List.length_cons]
      omega

theorem add_capacity_growth (x : α) (s : State α) :
    (add x s).1.slots.size = 2 ^ growths (add x s).2 * s.slots.size := by
  rw [add_size, add_growths]
  split <;> simp

theorem adds_capacity_growth (xs : List α) (s : State α) :
    (adds xs s).1.slots.size = 2 ^ growths (adds xs s).2 * s.slots.size := by
  induction xs generalizing s with
  | nil => simp [adds_nil, growths]
  | cons x xs ih =>
      simp only [adds_cons, growths_append, Nat.pow_add, ih, add_capacity_growth]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]

theorem from_empty_balance (xs : List α) :
    work (adds xs empty).2 + growths (adds xs empty).2 + 1 =
      xs.length + 2 ^ growths (adds xs empty).2 := by
  have h := adds_balance xs empty_layout (by simp [empty])
  simpa [adds_capacity_growth, empty] using h

theorem from_empty_capacity_lower (xs : List α) :
    xs.length < (adds xs empty).1.slots.size := by
  have h := layout_size (adds_layout xs empty_layout)
  have hp := adds_spare xs empty_layout (by simp [empty])
  simp only [List.append_nil, List.length_reverse] at h
  omega

/-- A finite sum of the extra charges 2^k-1, for k from 1 through p. -/
def geometricExtras : Nat → Nat
  | 0 => 0
  | p + 1 => geometricExtras p + (2 ^ (p + 1) - 1)

theorem geometricExtras_exact (p : Nat) : geometricExtras p + p + 2 = 2 ^ (p + 1) := by
  induction p with
  | zero => decide
  | succ p ih =>
      have hp : 0 < 2 ^ (p + 1) := Nat.pow_pos (by decide)
      rw [geometricExtras, Nat.pow_succ]
      omega

/-- Exact all-input form of the eager schedule, under this explicit eager
boundary convention. The exponent is characterized by its power interval. -/
theorem total_work_power_interval (xs : List α) (hne : xs ≠ []) :
    ∃ p, 2 ^ p ≤ xs.length ∧ xs.length < 2 ^ (p + 1) ∧
      work (adds xs empty).2 = xs.length + geometricExtras p := by
  let r := growths (adds xs empty).2
  have hcap : (adds xs empty).1.slots.size = 2 ^ r := by
    simpa only [empty, r, Array.size_replicate, Nat.mul_one] using
      adds_capacity_growth xs (empty : State α)
  have hlo := from_empty_capacity_lower xs
  have hhi := from_empty_capacity_upper xs hne
  have hn : 0 < xs.length := List.length_pos_iff.mpr hne
  rw [hcap] at hlo hhi
  have hr : 0 < r := by
    by_cases hzero : r = 0
    · simp only [hzero, Nat.pow_zero] at hlo
      omega
    · omega
  have he : r = (r - 1) + 1 := by omega
  have hb := from_empty_balance xs
  change work (adds xs empty).2 + r + 1 = xs.length + 2 ^ r at hb
  have hg := geometricExtras_exact (r - 1)
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := congrArg (fun n => 2 ^ n) he
      _ = 2 * 2 ^ (r - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨r - 1, ?_, ?_, ?_⟩
  · rw [hpow] at hhi
    omega
  · simpa only [← he] using hlo
  · rw [← he] at hg
    omega


end Resources.DynamicFrontArrays.Eager

namespace Resources.DynamicFrontArrays
universe u
variable {α : Type u}

theorem add_growths (x : α) (s : State α) :
    Eager.growths (add x s).2 = if s.free = 0 then 1 else 0 := by
  by_cases h : s.free = 0 <;>
    simp [add,h,Eager.growths_append,grow,Eager.growths,Eager.copyInto_growths,writeFront]

theorem add_capacity_growth (x : α) (s : State α) :
    (add x s).1.slots.size = 2 ^ Eager.growths (add x s).2 * s.slots.size := by
  rw [add_size,add_growths]
  split <;> simp

theorem adds_capacity_growth (xs : List α) (s : State α) :
    (adds xs s).1.slots.size = 2 ^ Eager.growths (adds xs s).2 * s.slots.size := by
  induction xs generalizing s with
  | nil => simp [adds_nil,Eager.growths]
  | cons x xs ih =>
    simp only [adds_cons,Eager.growths_append,Nat.pow_add,ih,add_capacity_growth]
    simp only [Nat.mul_assoc,Nat.mul_left_comm]

end Resources.DynamicFrontArrays

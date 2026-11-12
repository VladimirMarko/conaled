import Applications.Resources.DynamicFrontArrays

/-! Repricing and potential accounting on the same raw executions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DynamicFrontArrays
universe u
variable {α : Type u}

def priceHom (price : List (Event α) → Nat) (hzero : price [] = 0)
    (happend : ∀ es fs, price (es ++ fs) = price es + price fs) :
    Additive (FreeMonoid (Event α)) →+ Nat where
  toFun xs := price xs.toMul.toList
  map_zero' := hzero
  map_add' x y := happend x.toMul.toList y.toMul.toList

theorem execute_metered (step : α → State α → State α × List (Event α))
    (price : List (Event α) → Nat) (hzero : price [] = 0)
    (happend : ∀ es fs, price (es ++ fs) = price es + price fs)
    (xs : List α) (s : State α) :
    ((execute step xs s).1,price (execute step xs s).2) =
      Resources.run (fun x t => ((step x t).1,price (step x t).2)) xs s :=
  reweight_run (priceHom price hzero happend) _ xs s

def grouped (step : α → State α → State α × List (Event α)) (xs : List α) (s : State α) :
    State α × List (List (Event α)) :=
  let r := Resources.run (fun x t => let a := step x t
    (a.1,Additive.ofMul (FreeMonoid.of a.2))) xs s
  (r.1,r.2.toMul.toList)

def flattenBlocks : Additive (FreeMonoid (List (Event α))) →+ Additive (FreeMonoid (Event α)) where
  toFun bs := Additive.ofMul (FreeMonoid.ofList bs.toMul.toList.flatten)
  map_zero' := rfl
  map_add' _a _b := List.flatten_append

theorem grouped_flatten (step : α → State α → State α × List (Event α))
    (xs : List α) (s : State α) :
    ((grouped step xs s).1,(grouped step xs s).2.flatten) = execute step xs s := by
  have h := reweight_run (flattenBlocks (α := α))
    (fun x t => let a := step x t; (a.1,Additive.ofMul (FreeMonoid.of a.2))) xs s
  have he : (fun x t => reweight (flattenBlocks (α := α))
      (let a := step x t; (a.1,Additive.ofMul (FreeMonoid.of a.2)))) =
      (fun x t => ((step x t).1,Additive.ofMul (FreeMonoid.ofList (step x t).2))) := by
    funext x t
    apply Prod.ext
    · rfl
    · change Additive.ofMul (FreeMonoid.ofList ((step x t).2 ++ [])) = _
      rw [List.append_nil]
  rw [he] at h
  exact congrArg (fun r => (r.1,r.2.toMul.toList)) h

def bills (step : α → State α → State α × List (Event α))
    (price : List (Event α) → Nat) (xs : List α) (s : State α) : List Nat :=
  (grouped step xs s).2.map price

theorem bills_sum (step : α → State α → State α × List (Event α))
    (price : List (Event α) → Nat) (hzero : price [] = 0)
    (happend : ∀ es fs, price (es ++ fs) = price es + price fs)
    (xs : List α) (s : State α) : (bills step price xs s).sum = price (execute step xs s).2 := by
  have hf := congrArg Prod.snd (grouped_flatten step xs s)
  rw [← hf]
  unfold bills
  generalize (grouped step xs s).2 = bs
  induction bs with
  | nil => exact hzero.symm
  | cons b bs ih => simp only [List.map_cons,List.sum_cons,List.flatten_cons,happend,ih]

/-- Truncated nonnegative potential, also defined on arbitrary raw states. -/
def potential (s : State α) : Nat := s.slots.size - 2 * s.free

theorem empty_potential : potential (empty : State α) = 0 := by simp [potential, empty]

theorem add_potential (x : α) (s : State α) :
    work (add x s).2 + potential (add x s).1 ≤ potential s + 3 := by
  rw [add_work]
  by_cases h : s.free = 0
  · simp only [h, ite_true, add, potential, writeFront,
      Array.size_setIfInBounds, grow_size, grow_free]
    omega
  · simp only [h, ite_false, add, potential, writeFront,
      Array.size_setIfInBounds]
    omega

theorem add_allocation_potential (x : α) (s : State α) :
    allocation (add x s).2 + 2 * potential (add x s).1 ≤ 2 * potential s + 4 := by
  rw [add_allocation]
  by_cases h : s.free = 0
  · simp only [h, ite_true, add, potential, writeFront,
      Array.size_setIfInBounds, grow_size, grow_free]
    omega
  · simp only [h, ite_false, add, potential, writeFront,
      Array.size_setIfInBounds]
    omega

theorem adds_metered (price : List (Event α) → Nat) (hzero : price [] = 0)
    (happend : ∀ es fs, price (es ++ fs) = price es + price fs)
    (xs : List α) (s : State α) :
    ((adds xs s).1, price (adds xs s).2) =
      Resources.run (fun x t => ((add x t).1, price (add x t).2)) xs s :=
  execute_metered add price hzero happend xs s

theorem adds_potential (xs : List α) (s : State α) :
    work (adds xs s).2 + potential (adds xs s).1 ≤ potential s + 3 * xs.length := by
  have h := Resources.run_constant_charge
    (fun x t => ((add x t).1, work (add x t).2)) potential 3 add_potential xs s
  rw [← adds_metered work rfl work_append] at h
  exact h

theorem adds_allocation_potential (xs : List α) (s : State α) :
    allocation (adds xs s).2 + 2 * potential (adds xs s).1 ≤
      2 * potential s + 4 * xs.length := by
  have h := Resources.run_constant_charge
    (fun x t => ((add x t).1, allocation (add x t).2)) (fun t => 2 * potential t)
    4 add_allocation_potential xs s
  rw [← adds_metered allocation rfl allocation_append] at h
  exact h

theorem from_empty_work (xs : List α) : work (adds xs empty).2 ≤ 3 * xs.length := by
  have h := adds_potential xs empty
  rw [empty_potential] at h
  omega

theorem from_empty_allocation (xs : List α) : allocation (adds xs empty).2 ≤ 4 * xs.length := by
  have h := adds_allocation_potential xs empty
  rw [empty_potential] at h
  omega

/-- Charging a fixed amount per allocated slot preserves constant amortized cost.
The single slot of the initial state is included explicitly as setup cost. -/
theorem from_empty_priced (allocationPrice : Nat) (xs : List α) :
    allocationPrice + work (adds xs empty).2 + allocationPrice * allocation (adds xs empty).2 ≤
      allocationPrice + (3 + 4 * allocationPrice) * xs.length := by
  have hw := from_empty_work xs
  have ha := Nat.mul_le_mul_left allocationPrice (from_empty_allocation xs)
  rw [Nat.mul_left_comm allocationPrice 4] at ha
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

namespace Eager
theorem add_potential (x : α) (s : State α) :
    work (add x s).2 + potential (add x s).1 ≤ potential s + 3 := by
  rw [add_work]
  by_cases h : s.free ≤ 1
  · simp only [h, ite_true, add, potential, writeFront,
      Array.size_setIfInBounds, grow_size, grow_free]
    omega
  · simp only [h, ite_false, add, potential, writeFront, Array.size_setIfInBounds]
    omega

theorem add_allocation_potential (x : α) (s : State α) :
    allocation (add x s).2 + 2 * potential (add x s).1 ≤ 2 * potential s + 4 := by
  rw [add_allocation]
  by_cases h : s.free ≤ 1
  · simp only [h, ite_true, add, potential, writeFront,
      Array.size_setIfInBounds, grow_size, grow_free]
    omega
  · simp only [h, ite_false, add, potential, writeFront, Array.size_setIfInBounds]
    omega

theorem adds_metered (price : List (Event α) → Nat) (hzero : price [] = 0)
    (happend : ∀ es fs, price (es ++ fs) = price es + price fs)
    (xs : List α) (s : State α) :
    ((adds xs s).1, price (adds xs s).2) =
      Resources.run (fun x t => ((add x t).1, price (add x t).2)) xs s :=
  execute_metered add price hzero happend xs s

theorem adds_potential (xs : List α) (s : State α) :
    work (adds xs s).2 + potential (adds xs s).1 ≤ potential s + 3 * xs.length := by
  have h := Resources.run_constant_charge
    (fun x t => ((add x t).1, work (add x t).2)) potential 3 add_potential xs s
  rw [← adds_metered work rfl work_append] at h
  exact h

theorem adds_allocation_potential (xs : List α) (s : State α) :
    allocation (adds xs s).2 + 2 * potential (adds xs s).1 ≤
      2 * potential s + 4 * xs.length := by
  have h := Resources.run_constant_charge
    (fun x t => ((add x t).1, allocation (add x t).2)) (fun t => 2 * potential t)
    4 add_allocation_potential xs s
  rw [← adds_metered allocation rfl allocation_append] at h
  exact h

theorem from_empty_work (xs : List α) : work (adds xs empty).2 ≤ 3 * xs.length := by
  have h := adds_potential xs empty
  rw [empty_potential] at h
  omega

theorem from_empty_allocation (xs : List α) : allocation (adds xs empty).2 ≤ 4 * xs.length := by
  have h := adds_allocation_potential xs empty
  rw [empty_potential] at h
  omega

theorem from_empty_priced (allocationPrice : Nat) (xs : List α) :
    allocationPrice + work (adds xs empty).2 + allocationPrice * allocation (adds xs empty).2 ≤
      allocationPrice + (3 + 4 * allocationPrice) * xs.length := by
  have hw := from_empty_work xs
  have ha := Nat.mul_le_mul_left allocationPrice (from_empty_allocation xs)
  rw [Nat.mul_left_comm allocationPrice 4] at ha
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega


end Eager
end Resources.DynamicFrontArrays

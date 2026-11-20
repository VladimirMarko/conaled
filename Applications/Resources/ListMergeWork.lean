import Applications.Resources.ListMerge

/-!
# Ordinary merge with a measured comparator and declared source work

Each invocation costs one, including the terminal invocation. A nonempty step
executes the supplied comparator once, follows its actual Boolean, binds the
selected recursive result and constructs one cons at cost one. Returning the
remaining suffix, projections, pairing and observation arithmetic are uncharged.
This extends the shared ordinary merge's comparison/entry observations; it is
not a bound on compiled runtime, arbitrary-comparator bit work or allocation.
The complete sorting client and tariff are described in
`docs/research/fdsa-measured-rectangle-scan.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListMergeWork

universe u
variable {α : Type u}

/-- One actual measured comparison determines which recursive merge executes. -/
def run (cmpRun : α → α → Measured Bool Nat) :
    List α → List α → Measured (List α) Nat
  | [], ys => (ys, 1)
  | xs, [] => (xs, 1)
  | x :: xs, y :: ys =>
      CallCount.tick (Resources.bind (cmpRun x y) fun takeLeft =>
        if takeLeft then
          Resources.bind (run cmpRun xs (y :: ys)) (fun zs => (x :: zs, 1))
        else
          Resources.bind (run cmpRun (x :: xs) ys) (fun zs => (y :: zs, 1)))
termination_by xs ys => xs.length + ys.length

theorem run_nil_left (cmpRun : α → α → Measured Bool Nat) (ys : List α) :
    run cmpRun [] ys = (ys, 1) := by
  simp only [run]

theorem run_nil_right (cmpRun : α → α → Measured Bool Nat) (xs : List α) :
    run cmpRun xs [] = (xs, 1) := by
  cases xs <;> simp only [run]

theorem run_cons_cons (cmpRun : α → α → Measured Bool Nat)
    (x y : α) (xs ys : List α) :
    run cmpRun (x :: xs) (y :: ys) =
      CallCount.tick (Resources.bind (cmpRun x y) fun takeLeft =>
        if takeLeft then
          Resources.bind (run cmpRun xs (y :: ys)) (fun zs => (x :: zs, 1))
        else
          Resources.bind (run cmpRun (x :: xs) ys) (fun zs => (y :: zs, 1))) := by
  simp only [run]

/-- Raw erasure uses the returned Boolean; it assumes no comparator laws. -/
theorem run_value (cmpRun : α → α → Measured Bool Nat) (xs ys : List α) :
    (run cmpRun xs ys).1 = List.merge xs ys (fun x y => (cmpRun x y).1) := by
  induction xs generalizing ys with
  | nil => simp only [run_nil_left, List.nil_merge]
  | cons x xs ihx =>
      induction ys with
      | nil => simp only [run_nil_right, List.merge_right]
      | cons y ys ihy =>
          cases h : (cmpRun x y).1 with
          | false => simp [run_cons_cons, h, Resources.bind, CallCount.tick, ihy]
          | true => simp [run_cons_cons, h, Resources.bind, CallCount.tick, ihx]

theorem run_perm (cmpRun : α → α → Measured Bool Nat) (xs ys : List α) :
    (run cmpRun xs ys).1.Perm (xs ++ ys) := by
  rw [run_value]
  exact List.merge_perm_append _

theorem run_length (cmpRun : α → α → Measured Bool Nat) (xs ys : List α) :
    (run cmpRun xs ys).1.length = xs.length + ys.length := by
  simpa only [List.length_append] using (run_perm cmpRun xs ys).length_eq

/-- Only the actual callback and selected child contribute to this step. -/
theorem run_cost_cons_cons (cmpRun : α → α → Measured Bool Nat)
    (x y : α) (xs ys : List α) :
    (run cmpRun (x :: xs) (y :: ys)).2 =
      (cmpRun x y).2 +
        (if (cmpRun x y).1 then (run cmpRun xs (y :: ys)).2
         else (run cmpRun (x :: xs) ys).2) + 2 := by
  cases h : (cmpRun x y).1 <;>
    simp [run_cons_cons, h, Resources.bind, CallCount.tick, Nat.add_assoc]

/-- A uniform callback bound prices the comparisons that actually execute. -/
theorem run_cost_le_comparisons (cmpRun : α → α → Measured Bool Nat)
    (xs ys : List α) (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C) :
    (run cmpRun xs ys).2 ≤
      (C + 2) * ListMerge.comparisons (fun x y => (cmpRun x y).1) xs ys + 1 := by
  induction xs generalizing ys with
  | nil => simp [run_nil_left, ListMerge.comparisons_nil_left]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [run_nil_right, ListMerge.comparisons_nil_right]
      | cons y ys ihy =>
          have hc := hC x y
          cases h : (cmpRun x y).1 with
          | false =>
              simp only [run_cost_cons_cons, ListMerge.comparisons_cons_cons, h,
                Bool.false_eq_true, ↓reduceIte, Nat.mul_add, Nat.mul_one]
              omega
          | true =>
              have ih := ihx (y :: ys)
              simp only [run_cost_cons_cons, ListMerge.comparisons_cons_cons, h,
                ↓reduceIte, Nat.mul_add, Nat.mul_one]
              omega

/-- Empty sides retain the terminal entry; sortedness is not needed. -/
theorem run_cost_le (cmpRun : α → α → Measured Bool Nat)
    (xs ys : List α) (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C) :
    (run cmpRun xs ys).2 ≤ (C + 2) * (xs.length + ys.length) + 1 :=
  (run_cost_le_comparisons cmpRun xs ys C hC).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (ListMerge.comparisons_le _ xs ys)) 1)

/-- Constant comparator observations yield the exact ordinary comparison tariff. -/
theorem run_cost_of_constant (cmpRun : α → α → Measured Bool Nat)
    (xs ys : List α) (C : Nat) (hC : ∀ x y, (cmpRun x y).2 = C) :
    (run cmpRun xs ys).2 =
      (C + 2) * ListMerge.comparisons (fun x y => (cmpRun x y).1) xs ys + 1 := by
  induction xs generalizing ys with
  | nil => simp [run_nil_left, ListMerge.comparisons_nil_left]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [run_nil_right, ListMerge.comparisons_nil_right]
      | cons y ys ihy =>
          cases h : (cmpRun x y).1 with
          | false =>
              simp [run_cost_cons_cons, ListMerge.comparisons_cons_cons, h, hC,
                ihy, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
          | true =>
              simp [run_cost_cons_cons, ListMerge.comparisons_cons_cons, h, hC,
                ihx, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]

end Resources.ListMergeWork

import Applications.Sorting.SourceMerge
import Applications.Resources.CallCount

/-!
# Ordinary merge with comparison and invocation observations

One execution follows the actual Boolean comparator and records
`(head comparisons, recursive merge invocations)`. Empty-side calls return the
remaining list without a comparison and count one invocation. Only the selected
recursive branch is executed, and its returned list supplies the output tail.
The comparison projection is the handwritten FDSA `C_merge` recurrence; the
entry projection is a separately declared invocation model. Neither is a claim
about the compiled standard-library implementation or a comparator's own work.

Source attribution, the applicable license and remaining chapter obligations:
`docs/research/fdsa-list-merge.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListMerge

universe u v
variable {α : Type u} {β : Type v}

/-- Execute ordinary merge once, observing comparisons and invocations together. -/
def run (cmp : α → α → Bool) : List α → List α → Measured (List α) (Nat × Nat)
  | [], ys => (ys, (0, 1))
  | xs, [] => (xs, (0, 1))
  | x :: xs, y :: ys =>
      if cmp x y then
        Resources.bind (run cmp xs (y :: ys)) (fun zs => (x :: zs, (1, 1)))
      else
        Resources.bind (run cmp (x :: xs) ys) (fun zs => (y :: zs, (1, 1)))
termination_by xs ys => xs.length + ys.length

/-- Number of comparisons in the actual run; no second scalar execution. -/
abbrev comparisons (cmp : α → α → Bool) (xs ys : List α) : Nat :=
  (run cmp xs ys).2.1

/-- Number of invocations, including the initial and terminal calls. -/
abbrev entries (cmp : α → α → Bool) (xs ys : List α) : Nat :=
  (run cmp xs ys).2.2

theorem run_nil_left (cmp : α → α → Bool) (ys : List α) :
    run cmp [] ys = (ys, (0, 1)) := by
  simp only [run]

theorem run_nil_right (cmp : α → α → Bool) (xs : List α) :
    run cmp xs [] = (xs, (0, 1)) := by
  cases xs <;> simp only [run]

/-- The selected recursive execution supplies both the value and observations. -/
theorem run_cons_cons (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    run cmp (x :: xs) (y :: ys) =
      if cmp x y then
        Resources.bind (run cmp xs (y :: ys)) (fun zs => (x :: zs, (1, 1)))
      else
        Resources.bind (run cmp (x :: xs) ys) (fun zs => (y :: zs, (1, 1))) := by
  simp only [run]

/-- Value erasure holds for arbitrary comparators and arbitrary input lists. -/
theorem run_value (cmp : α → α → Bool) (xs ys : List α) :
    (run cmp xs ys).1 = List.merge xs ys cmp := by
  induction xs generalizing ys with
  | nil => simp only [run_nil_left, List.nil_merge]
  | cons x xs ihx =>
      induction ys with
      | nil => simp only [run_nil_right, List.merge_right]
      | cons y ys ihy =>
          cases h : cmp x y with
          | false => simp [run_cons_cons, List.cons_merge_cons, h, Resources.bind, ihy]
          | true => simp [run_cons_cons, List.cons_merge_cons, h, Resources.bind, ihx]

theorem comparisons_nil_left (cmp : α → α → Bool) (ys : List α) :
    comparisons cmp [] ys = 0 := by
  simp only [comparisons, run_nil_left]

theorem comparisons_nil_right (cmp : α → α → Bool) (xs : List α) :
    comparisons cmp xs [] = 0 := by
  simp only [comparisons, run_nil_right]

/-- Exactly one head comparison precedes the chosen recursive comparison count. -/
theorem comparisons_cons_cons (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    comparisons cmp (x :: xs) (y :: ys) =
      1 + (if cmp x y then comparisons cmp xs (y :: ys)
           else comparisons cmp (x :: xs) ys) := by
  cases h : cmp x y <;>
    simp [comparisons, run_cons_cons, h, Resources.bind, Nat.add_comm]

theorem entries_nil_left (cmp : α → α → Bool) (ys : List α) :
    entries cmp [] ys = 1 := by
  simp only [entries, run_nil_left]

theorem entries_nil_right (cmp : α → α → Bool) (xs : List α) :
    entries cmp xs [] = 1 := by
  simp only [entries, run_nil_right]

/-- The current invocation contributes one in addition to the selected child. -/
theorem entries_cons_cons (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    entries cmp (x :: xs) (y :: ys) =
      1 + (if cmp x y then entries cmp xs (y :: ys)
           else entries cmp (x :: xs) ys) := by
  cases h : cmp x y <;>
    simp [entries, run_cons_cons, h, Resources.bind, Nat.add_comm]

/-- Projection to the existing call convention retains the actual selected
child computation and its returned list, followed by an uncharged cons. -/
theorem run_entries_cons_cons (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    Resources.reweight Prod.snd (run cmp (x :: xs) (y :: ys)) =
      CallCount.tick
        (if cmp x y then
          Resources.bind (Resources.reweight Prod.snd (run cmp xs (y :: ys)))
            (fun zs => Resources.pure (x :: zs))
         else
          Resources.bind (Resources.reweight Prod.snd (run cmp (x :: xs) ys))
            (fun zs => Resources.pure (y :: zs))) := by
  cases h : cmp x y <;>
    simp [run_cons_cons, h, Resources.reweight, Resources.bind, Resources.pure,
      CallCount.tick]

/-- A single merge has exactly one terminal invocation without a comparison. -/
theorem entries_eq_comparisons_add_one (cmp : α → α → Bool) (xs ys : List α) :
    entries cmp xs ys = comparisons cmp xs ys + 1 := by
  induction xs generalizing ys with
  | nil => simp only [entries_nil_left, comparisons_nil_left]
  | cons x xs ihx =>
      induction ys with
      | nil => simp only [entries_nil_right, comparisons_nil_right]
      | cons y ys ihy =>
          cases h : cmp x y with
          | false =>
              simp [entries_cons_cons, comparisons_cons_cons, h, ihy, Nat.add_assoc]
          | true =>
              simp [entries_cons_cons, comparisons_cons_cons, h, ihx, Nat.add_assoc]

/-- The comparison bound requires neither sortedness nor comparator laws. -/
theorem comparisons_le (cmp : α → α → Bool) (xs ys : List α) :
    comparisons cmp xs ys ≤ xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [comparisons_nil_left]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [comparisons_nil_right]
      | cons y ys ihy =>
          rw [comparisons_cons_cons]
          split
          · have h := ihx (y :: ys)
            simp only [List.length_cons] at h ⊢
            omega
          · have h := ihy
            simp only [List.length_cons] at h ⊢
            omega

/-- The terminal invocation remains in the length bound, also for empty inputs. -/
theorem entries_le (cmp : α → α → Bool) (xs ys : List α) :
    entries cmp xs ys ≤ xs.length + ys.length + 1 := by
  rw [entries_eq_comparisons_add_one]
  exact Nat.add_le_add_right (comparisons_le cmp xs ys) 1

/-- Two nonempty inputs necessarily cause a first comparison. -/
theorem comparisons_cons_pos (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    1 ≤ comparisons cmp (x :: xs) (y :: ys) := by
  rw [comparisons_cons_cons]
  omega

/-- Input-local comparison agreement transports the entire measured result.
The map need not be injective, and its codomain may live in another universe.
This is a correspondence of the two declared merge executions, not a charge
for computing the mapped inputs or mapping an output in a caller. -/
theorem run_map (cmp : α → α → Bool) (cmp' : β → β → Bool) (f : α → β)
    (xs ys : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ ys, cmp a b = cmp' (f a) (f b)) :
    run cmp' (xs.map f) (ys.map f) =
      ((run cmp xs ys).1.map f, (run cmp xs ys).2) := by
  revert hc
  induction xs generalizing ys with
  | nil =>
      intro _
      simp only [List.map_nil, run_nil_left]
  | cons x xs ihx =>
      induction ys with
      | nil =>
          intro _
          simp only [List.map_nil, run_nil_right]
      | cons y ys ihy =>
          intro hc
          have hxy : cmp x y = cmp' (f x) (f y) :=
            hc x (by simp) y (by simp)
          have hcLeft : ∀ a ∈ xs, ∀ b ∈ y :: ys, cmp a b = cmp' (f a) (f b) :=
            fun a ha b hb => hc a (by simp [ha]) b hb
          have hcRight : ∀ a ∈ x :: xs, ∀ b ∈ ys, cmp a b = cmp' (f a) (f b) :=
            fun a ha b hb => hc a ha b (by simp [hb])
          have hleft := ihx (y :: ys) hcLeft
          have hright := ihy hcRight
          cases h : cmp x y with
          | false => simp [run_cons_cons, ← hxy, h, Resources.bind, hright]
          | true => simp [run_cons_cons, ← hxy, h, Resources.bind, hleft]

end Resources.ListMerge

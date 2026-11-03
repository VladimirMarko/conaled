import Applications.Sequences.SharedList.Observation

/-!
# Integer indices for the source list update

The source decrements an integer index on every tail traversal. A negative
index therefore traverses the whole list and fails at its empty tail. It is
not replaced by an early negative-index check. Nonnegative executions refine
the existing natural-index implementation, including its visit count and
shared-cell result, so its allocation and retained-root theorems are reusable.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList
variable {α : Type}

/-- Independent direct list interpretation of the source's integer recurrence. -/
def updateIntegerValue : List α → Int → α → Option (List α)
  | [], _, _ => none
  | x :: xs, i, y =>
      if i = 0 then some (y :: xs)
      else (updateIntegerValue xs (i - 1) y).map (List.cons x)

theorem updateIntegerValue_ofNat (xs : List α) (i : Nat) (y : α) :
    updateIntegerValue xs (i : Int) y = updateValue xs i y := by
  induction xs generalizing i with
  | nil => simp [updateIntegerValue, updateValue]
  | cons x xs ih =>
      cases i with
      | zero => simp [updateIntegerValue, updateValue]
      | succ i =>
          have nz : (i : Int) + 1 ≠ 0 := by omega
          simp only [updateIntegerValue, Int.natCast_succ, ite_eq_right nz,
            Int.add_sub_cancel, ih, updateValue, List.length_cons,
            Nat.succ_lt_succ_iff, List.set_cons_succ]
          split <;> rfl

theorem updateIntegerValue_negative (xs : List α) {i : Int} (negative : i < 0)
    (y : α) : updateIntegerValue xs i y = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      simp [updateIntegerValue, ne_of_lt negative, ih (i := i - 1) (by omega)]

def updateIntegerRunFuel : Nat → Store α → Root → Int → α →
    Resources.Measured (Option (Store α × Root)) Nat
  | _, _, none, _, _ => (none, 1)
  | 0, _, some _, _, _ => (none, 0)
  | fuel + 1, s, some a, i, y =>
      match s.heap a with
      | none => (none, 1)
      | some (x, r) =>
          if i = 0 then (some (allocate s y r), 1)
          else
            let rest := updateIntegerRunFuel fuel s r (i - 1) y
            (rest.1.map (fun out => allocate out.1 x out.2), rest.2 + 1)

/-- This is execution equality, including malformed roots and insufficient fuel. -/
theorem updateIntegerRunFuel_ofNat (fuel : Nat) (s : Store α) (r : Root)
    (i : Nat) (y : α) :
    updateIntegerRunFuel fuel s r (i : Int) y = updateRunFuel fuel s r i y := by
  induction fuel generalizing r i with
  | zero => cases r <;> rfl
  | succ fuel ih =>
      cases r with
      | none => rfl
      | some a =>
          cases lookup : s.heap a with
          | none => simp [updateIntegerRunFuel, updateRunFuel, lookup]
          | some cell =>
              obtain ⟨x, q⟩ := cell
              cases i with
              | zero => simp [updateIntegerRunFuel, updateRunFuel, lookup]
              | succ i =>
                  have nz : (i : Int) + 1 ≠ 0 := by omega
                  simp [updateIntegerRunFuel, updateRunFuel, lookup, nz, ih]

theorem updateIntegerRunFuel_negative {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {fuel : Nat} (enough : xs.length ≤ fuel)
    {i : Int} (negative : i < 0) (y : α) :
    updateIntegerRunFuel fuel s r i y = (none, xs.length + 1) := by
  induction h generalizing fuel i with
  | nil => simp [updateIntegerRunFuel]
  | @cons a x r xs lookup _ _ ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp [updateIntegerRunFuel, lookup, ne_of_lt negative,
            ih (by simpa using enough) (i := i - 1) (by omega)]

def updateIntegerRun (s : Store α) (r : Root) (i : Int) (y : α) :
    Resources.Measured (Option (Store α × Root)) Nat :=
  updateIntegerRunFuel s.next s r i y

theorem updateIntegerRun_ofNat (s : Store α) (r : Root) (i : Nat) (y : α) :
    updateIntegerRun s r (i : Int) y = updateRun s r i y :=
  updateIntegerRunFuel_ofNat s.next s r i y

theorem updateIntegerRun_negative {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {i : Int} (negative : i < 0) (y : α) :
    updateIntegerRun s r i y = (none, xs.length + 1) :=
  updateIntegerRunFuel_negative h h.length_le_next negative y

/-- Existing path-copy correctness applies unchanged to nonnegative source indices. -/
theorem updateIntegerRun_success {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {i : Nat} (inside : i < xs.length) (y : α) :
    ∃ out, updateIntegerRun s r (i : Int) y = (some out, i + 1) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (xs.set i y) ∧
      out.1.next = s.next + (i + 1) ∧
      advance (i + 1) out.1 out.2 = advance (i + 1) s r := by
  rw [updateIntegerRun_ofNat]
  exact updateRun_success h inside y

theorem updateIntegerRun_correct {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) (i : Int) (y : α) :
    (optionalRepresentation α).Rel (updateIntegerRun s r i y).1
      (updateIntegerValue xs i y) := by
  dsimp only [optionalRepresentation]
  cases i with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast]
      rw [updateIntegerRun_ofNat s r n y, updateIntegerValue_ofNat xs n y]
      exact (updateSquare n y).preserves (r := (s, r)) (s := xs) h
  | negSucc n =>
      have negative : Int.negSucc n < 0 := by omega
      rw [updateIntegerRun_negative h negative y, updateIntegerValue_negative xs negative y]
      trivial

def updateIntegerSquare (i : Int) (y : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) where
  impl state := (updateIntegerRun state.1 state.2 i y).1
  spec xs := updateIntegerValue xs i y
  preserves := fun h => updateIntegerRun_correct h i y

end Sequences.SharedList

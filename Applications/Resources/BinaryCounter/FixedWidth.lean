import Applications.Resources.BinaryCounter

/-!
# Measured fixed-width binary predecessor

The bit list is little-endian and may contain redundant high zero bits.
The program never computes its mathematical `value` or normalizes its width.
The true-head branch reuses its untouched tail; borrowing rebuilds only the
visited prefix. Unlike `decBits`, a one-bit one returns a one-bit zero.

The declared structural observation charges one entry/dispatch, one per new
list cons, and one per returned Option constructor. Tuple packaging, constants,
projections, reuse and addition of observations are free. This is a source-event
tariff, not a claim about compiled machine time. See the maintained rotation
certificate correspondence for the enclosing verifier and remaining obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinaryCounter

/-- Execute a width-preserving predecessor, failing exactly at zero. -/
def decFixedRun : Bits → Measured (Option Bits) Nat
  | [] => (none, 2)
  | true :: bs => (some (false :: bs), 3)
  | false :: bs =>
      bind (decFixedRun bs) fun result =>
        match result with
        | none => (none, 2)
        | some ys => (some (true :: ys), 3)

@[simp] theorem decFixedRun_nil : decFixedRun [] = (none, 2) := rfl

@[simp] theorem decFixedRun_true (bs : Bits) :
    decFixedRun (true :: bs) = (some (false :: bs), 3) := rfl

theorem decFixedRun_false (bs : Bits) :
    decFixedRun (false :: bs) =
      bind (decFixedRun bs) (fun result =>
        match result with
        | none => (none, 2)
        | some ys => (some (true :: ys), 3)) := rfl

theorem decFixedRun_none_iff (bs : Bits) :
    (decFixedRun bs).1 = none ↔ value bs = 0 := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
      cases b with
      | true => simp [value]
      | false =>
          cases result : (decFixedRun bs).1 with
          | none =>
              have zero := ih.mp result
              simp [decFixedRun_false, bind, result, value, zero]
          | some ys =>
              have nonzero : value bs ≠ 0 := by
                intro zero
                have impossible := ih.mpr zero
                simp [result] at impossible
              simp only [decFixedRun_false, bind, result, value, reduceCtorEq, false_iff]
              omega

/-- The actual returned word has the same width and exactly the predecessor value. -/
theorem decFixedRun_some_spec {bs ys : Bits}
    (run : (decFixedRun bs).1 = some ys) :
    ys.length = bs.length ∧ value bs = value ys + 1 := by
  induction bs generalizing ys with
  | nil => simp at run
  | cons b bs ih =>
      cases b with
      | true =>
          simp only [decFixedRun_true, Option.some.injEq] at run
          subst ys
          constructor
          · rfl
          · simp only [value]
            omega
      | false =>
          cases result : (decFixedRun bs).1 with
          | none => simp [decFixedRun_false, bind, result] at run
          | some zs =>
              have spec := ih result
              simp only [decFixedRun_false, bind, result, Option.some.injEq] at run
              subst ys
              constructor
              · simpa only [List.length_cons] using congrArg (· + 1) spec.1
              · simp only [value]
                omega

theorem decFixedRun_some_length {bs ys : Bits}
    (run : (decFixedRun bs).1 = some ys) : ys.length = bs.length :=
  (decFixedRun_some_spec run).1

theorem decFixedRun_some_value {bs ys : Bits}
    (run : (decFixedRun bs).1 = some ys) : value bs = value ys + 1 :=
  (decFixedRun_some_spec run).2

theorem decFixedRun_exists_of_pos {bs : Bits} (positive : 0 < value bs) :
    ∃ ys, (decFixedRun bs).1 = some ys := by
  cases result : (decFixedRun bs).1 with
  | none =>
      have zero := (decFixedRun_none_iff bs).mp result
      omega
  | some ys => exact ⟨ys, rfl⟩

theorem decFixedRun_exists_iff (bs : Bits) :
    (∃ ys, (decFixedRun bs).1 = some ys) ↔ 0 < value bs := by
  constructor
  · rintro ⟨ys, run⟩
    have arithmetic := decFixedRun_some_value run
    omega
  · exact decFixedRun_exists_of_pos

/-- All bit words, including zero and noncanonical high-zero extensions. -/
theorem decFixedRun_cost_le (bs : Bits) :
    (decFixedRun bs).2 ≤ 3 * bs.length + 2 := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      cases b with
      | true =>
          simp only [decFixedRun_true, List.length_cons]
          omega
      | false =>
          cases result : (decFixedRun bs).1 <;>
            simp only [decFixedRun_false, bind, result, List.length_cons] <;> omega

/-- Zero scans every supplied bit; the final nil failure is also charged. -/
theorem decFixedRun_replicate_false (width : Nat) :
    decFixedRun (List.replicate width false) = (none, 2 * width + 2) := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [List.replicate_succ, decFixedRun_false, bind, ih]
      congr 1

/-- Borrowing stops at the first one, retaining every higher bit unchanged. -/
theorem decFixedRun_first_true (zeros : Nat) (tail : Bits) :
    decFixedRun (List.replicate zeros false ++ true :: tail) =
      (some (List.replicate zeros true ++ false :: tail), 3 * (zeros + 1)) := by
  induction zeros with
  | zero => rfl
  | succ zeros ih =>
      simp only [List.replicate_succ, List.cons_append, decFixedRun_false, bind, ih]
      congr 1

end Resources.BinaryCounter

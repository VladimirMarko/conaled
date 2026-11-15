import Applications.Resources.Measured
import Applications.Sequences.Steepness

/-!
# Steepness: short-circuit work and shared tuple demand

Each observed list constructor, integer addition, and integer comparison costs
one unit. The executions return values as well as counts. Tuple demand shares
each prepared suffix sum and does not demand the unused outermost sum. These
are explicit local source-equation rules, not costs of Lean or GHC execution.
Provenance, checked consumers and statement review: `docs/research/adwh-steepness-costs.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Steepness
open Sequences.Steepness

/-- Sum observes one constructor per call and performs one addition per cons. -/
def sumRun : List Int → Measured Int Nat
  | [] => (0, 1)
  | x :: xs =>
      let r := sumRun xs
      (x + r.1, 2 + r.2)

theorem sumRun_value (xs : List Int) : (sumRun xs).1 = xs.sum := by
  induction xs <;> simp_all [sumRun]

theorem sumRun_work (xs : List Int) : (sumRun xs).2 = 2 * xs.length + 1 := by
  induction xs <;> simp_all [sumRun, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

/-- The suffix Boolean is demanded only after a successful comparison. -/
def naive : List Int → Measured Bool Nat
  | [] => (true, 1)
  | x :: xs =>
      let s := sumRun xs
      if s.1 < x then
        let r := naive xs
        (r.1, 2 + s.2 + r.2)
      else (false, 2 + s.2)

theorem naive_value (xs : List Int) : (naive xs).1 = steep xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [naive, sumRun_value, steep]
      by_cases h : xs.sum < x <;> simp [h, ih]

theorem naive_correct (xs : List Int) : (naive xs).1 = true ↔ Steep xs := by
  rw [naive_value, steep_correct]

theorem naive_work_le (xs : List Int) :
    (naive xs).2 ≤ (xs.length + 1) * (xs.length + 1) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
      simp only [naive, sumRun_value, sumRun_work, List.length_cons]
      by_cases h : xs.sum < x
      · simp only [h, ↓reduceIte]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
        omega
      · simp only [h, ↓reduceIte]
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
        omega

theorem naive_work_eq_of_steep (xs : List Int) (h : Steep xs) :
    (naive xs).2 = (xs.length + 1) * (xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hs := (steep_cons_iff x xs).mp h
      have ht := ih hs.2
      simp only [naive, sumRun_value, sumRun_work, hs.1, ↓reduceIte, List.length_cons]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ht ⊢
      omega

/-- First failure omits all later Boolean work, even if the suffix is not steep. -/
theorem naive_cons_failure (x : Int) (xs : List Int) (h : x ≤ xs.sum) :
    naive (x :: xs) = (false, 2 * xs.length + 3) := by
  simp only [naive, sumRun_value, sumRun_work, not_lt.mpr h, ↓reduceIte]
  congr 1
  omega

/-- A demanded sum, with a delayed Boolean sharing that sum. -/
private structure Prepared where
  total : Int
  observe : Unit → Measured Bool Nat
  prepareWork : Nat

private def observeCons (x : Int) (tail : Prepared) : Measured Bool Nat :=
  if tail.total < x then
    let r := tail.observe ()
    (r.1, 1 + r.2)
  else (false, 1)

/-- Preparing the sum does not demand any suffix Boolean. -/
private def prepare : List Int → Prepared
  | [] => ⟨0, fun _ => (true, 0), 1⟩
  | x :: xs =>
      let tail := prepare xs
      ⟨x + tail.total, fun _ => observeCons x tail, 2 + tail.prepareWork⟩

private theorem prepare_total (xs : List Int) : (prepare xs).total = xs.sum := by
  induction xs <;> simp_all [prepare]

private theorem prepare_work (xs : List Int) :
    (prepare xs).prepareWork = 2 * xs.length + 1 := by
  induction xs <;> simp_all [prepare, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

private theorem prepare_observe_value (xs : List Int) :
    ((prepare xs).observe ()).1 = steep xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [prepare, observeCons, prepare_total, steep]
      by_cases h : xs.sum < x <;> simp [h, ih]

private theorem prepare_observe_work_le (xs : List Int) :
    ((prepare xs).observe ()).2 ≤ xs.length := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
      simp only [prepare, observeCons, prepare_total, List.length_cons]
      by_cases h : xs.sum < x
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; omega

private theorem prepare_observe_work_eq_of_steep (xs : List Int) (h : Steep xs) :
    ((prepare xs).observe ()).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hs := (steep_cons_iff x xs).mp h
      simp [prepare, observeCons, prepare_total, hs.1, ih hs.2, Nat.add_comm]

/-- Public Boolean demand: the unused outermost sum is not computed or charged. -/
def tupled : List Int → Measured Bool Nat
  | [] => (true, 1)
  | x :: xs =>
      let tail := prepare xs
      let r := observeCons x tail
      (r.1, 1 + tail.prepareWork + r.2)

theorem tupled_value (xs : List Int) : (tupled xs).1 = steepFast xs := by
  rw [steepFast_eq_steep]
  cases xs with
  | nil => rfl
  | cons x xs => exact prepare_observe_value (x :: xs)

theorem tupled_correct (xs : List Int) : (tupled xs).1 = true ↔ Steep xs := by
  rw [tupled_value, steepFast_correct]

theorem tupled_eq_naive_value (xs : List Int) : (tupled xs).1 = (naive xs).1 := by
  rw [tupled_value, steepFast_eq_steep, naive_value]

theorem tupled_work_cons_le (x : Int) (xs : List Int) :
    (tupled (x :: xs)).2 ≤ 3 * (x :: xs).length := by
  have h := prepare_observe_work_le (x :: xs)
  change (observeCons x (prepare xs)).2 ≤ (x :: xs).length at h
  simp only [tupled, prepare_work, List.length_cons, Nat.mul_add, Nat.mul_one]
  simp only [List.length_cons] at h
  omega

theorem tupled_work_le (xs : List Int) : (tupled xs).2 ≤ 3 * xs.length + 1 := by
  cases xs with
  | nil => decide
  | cons x xs => have h := tupled_work_cons_le x xs; omega

theorem tupled_work_eq_of_steep (x : Int) (xs : List Int) (h : Steep (x :: xs)) :
    (tupled (x :: xs)).2 = 3 * (x :: xs).length := by
  have hw := prepare_observe_work_eq_of_steep (x :: xs) h
  change (observeCons x (prepare xs)).2 = (x :: xs).length at hw
  simp only [tupled, prepare_work, hw, List.length_cons, Nat.mul_add, Nat.mul_one]
  omega

theorem tupled_cons_failure (x : Int) (xs : List Int) (h : x ≤ xs.sum) :
    tupled (x :: xs) = (false, 2 * xs.length + 3) := by
  simp only [tupled, observeCons, prepare_total, prepare_work, not_lt.mpr h, ↓reduceIte]
  congr 1
  omega

/-- A compact family on which every comparison succeeds. -/
def worstInput : Nat → List Int
  | 0 => []
  | n + 1 => let xs := worstInput n; (xs.sum + 1) :: xs

theorem worstInput_length (n : Nat) : (worstInput n).length = n := by
  induction n <;> simp_all [worstInput]

theorem worstInput_steep (n : Nat) : Steep (worstInput n) := by
  induction n with
  | zero => exact steep_nil
  | succ n ih =>
      apply (steep_cons_iff _ _).mpr
      exact ⟨by omega, ih⟩

theorem naive_worstInput_work (n : Nat) :
    (naive (worstInput n)).2 = (n + 1) * (n + 1) := by
  simpa [worstInput_length] using
    naive_work_eq_of_steep (worstInput n) (worstInput_steep n)

theorem tupled_worstInput_work (n : Nat) :
    (tupled (worstInput (n + 1))).2 = 3 * (n + 1) := by
  have h := tupled_work_eq_of_steep ((worstInput n).sum + 1) (worstInput n)
    (worstInput_steep (n + 1))
  simpa [worstInput, worstInput_length] using h

theorem naive_quadratic_witness (n : Nat) :
    ∃ xs : List Int, xs.length = n ∧ n * n ≤ (naive xs).2 := by
  refine ⟨worstInput n, worstInput_length n, ?_⟩
  rw [naive_worstInput_work]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

def naiveSquare : Squares.Square ⟨List Int, List Int, id⟩
    ⟨Measured Bool Nat, Bool, Prod.fst⟩ :=
  erasureSquare naive steep naive_value

def tupledSquare : Squares.Square ⟨List Int, List Int, id⟩
    ⟨Measured Bool Nat, Bool, Prod.fst⟩ :=
  erasureSquare tupled steep (fun xs => (tupled_value xs).trans (steepFast_eq_steep xs))

end Resources.Steepness

import Applications.Resources.ListFusion

/-! Sharp fixed-length takeWhile extrema and an executed prefix-fold consumer.
The existing executors and their declared work model remain unchanged.
See docs/research/takewhile-extrema.md for source dispositions and limits. -/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TakeWhileExtrema

open ListFusion
universe u v
variable {α : Type u} {β : Type v}

theorem empty_run (p : α → Bool) : takeWhile 1 1 1 p [] = ([], 1) := rfl

/-- The upper bound charges every source cell; a failed test stops before
producing that cell, so it cannot exceed the exhausted all-passing bill. -/
theorem full_upper (p : α → Bool) (xs : List α) :
    (takeWhile 1 1 1 p xs).2 ≤ 3 * xs.length + 1 := by
  have hlen := congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := xs))
  simp only [List.length_append] at hlen
  rw [takeWhile_work]
  split_ifs with h
  · have hz : (xs.dropWhile p).length = 0 := by rw [h]; rfl
    omega
  · have hp : 0 < (xs.dropWhile p).length := List.length_pos_iff.mpr h
    omega

theorem nonempty_lower (p : α → Bool) (x : α) (xs : List α) :
    2 ≤ (takeWhile 1 1 1 p (x :: xs)).2 := by
  cases hp : p x <;> simp [takeWhile, hp]

theorem positive_bounds (p : α → Bool) (xs : List α) (h : 0 < xs.length) :
    2 ≤ (takeWhile 1 1 1 p xs).2 ∧ (takeWhile 1 1 1 p xs).2 ≤ 4 * xs.length := by
  have hu := full_upper p xs
  cases xs with
  | nil => simp at h
  | cons x xs =>
    have hl := nonempty_lower p x xs
    simp only [List.length_cons] at *
    omega

def bestInput (n : Nat) : List Bool := List.replicate n false
def worstInput (n : Nat) : List Bool := List.replicate n true

theorem witness_lengths (n : Nat) : (bestInput n).length = n ∧ (worstInput n).length = n := by
  simp [bestInput, worstInput]

theorem best_run (n : Nat) :
    takeWhile 1 1 1 id (bestInput n) = ([], if n = 0 then 1 else 2) := by
  cases n <;> simp [bestInput, List.replicate_succ, takeWhile]

theorem worst_run (n : Nat) :
    takeWhile 1 1 1 id (worstInput n) = (worstInput n, 3 * n + 1) := by
  apply Prod.ext
  · simp [takeWhile_value, worstInput]
  · simp [takeWhile_work, worstInput]

/-- Both extrema concern the same fixed Bool identity predicate. -/
theorem best_minimum (n : Nat) (xs : List Bool) (hsize : xs.length = n) :
    (takeWhile 1 1 1 id (bestInput n)).2 ≤ (takeWhile 1 1 1 id xs).2 := by
  rw [best_run]
  cases xs with
  | nil => simp_all [takeWhile]
  | cons x xs =>
    have h := nonempty_lower id x xs
    have hn : n ≠ 0 := by simp only [List.length_cons] at hsize; omega
    simpa [hn] using h

theorem worst_maximum (n : Nat) (xs : List Bool) (hsize : xs.length = n) :
    (takeWhile 1 1 1 id xs).2 ≤ (takeWhile 1 1 1 id (worstInput n)).2 := by
  rw [worst_run]
  simpa [hsize] using full_upper id xs

theorem best_positive (n : Nat) (hn : 0 < n) :
    (takeWhile 1 1 1 id (bestInput n)).2 = 2 := by
  rw [best_run]
  simp [show n ≠ 0 by omega]

/-- Constants and threshold are independent of n and of all input values. -/
theorem worst_positive_bounds (n : Nat) (hn : 0 < n) :
    3 * n ≤ (takeWhile 1 1 1 id (worstInput n)).2 ∧
      (takeWhile 1 1 1 id (worstInput n)).2 ≤ 4 * n := by
  rw [worst_run]
  simp only
  omega

/-- Refutes an eventual uniform linear lower bound, at every proposed threshold. -/
theorem best_eventual_lower_obstruction (C N : Nat) :
    ∃ n, N ≤ n ∧ C * (takeWhile 1 1 1 id (bestInput n)).2 < n := by
  let n := max N (2 * C + 1)
  have hp : 0 < n := by dsimp [n]; omega
  refine ⟨n, Nat.le_max_left _ _, ?_⟩
  rw [best_positive n hp]
  dsimp [n]
  omega

/-- Actual producer followed by a full fold of the produced prefix. -/
def foldPrefix (c : Nat) (p : α → Bool) (f : α → β → β) (e : β)
    (xs : List α) : Measured β Nat :=
  bind (takeWhile 1 1 1 p xs) (ListExecution.foldr c f e)

theorem foldPrefix_value (c : Nat) (p : α → Bool) (f : α → β → β) (e : β)
    (xs : List α) :
    (foldPrefix c p f e xs).1 = (xs.takeWhile p).foldr f e := by
  simp [foldPrefix, bind, ListExecution.foldr_value, takeWhile_value]

theorem foldPrefix_work (c : Nat) (p : α → Bool) (f : α → β → β) (e : β)
    (xs : List α) :
    (foldPrefix c p f e xs).2 = (4 + c) * (xs.takeWhile p).length + 2 +
      (if xs.dropWhile p = [] then 0 else 1) := by
  simp only [foldPrefix, bind, ListExecution.foldr_work, takeWhile_value, takeWhile_work]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Full measured-pair independence, with an actual first failed element. -/
theorem foldPrefix_suffix_independent (c : Nat) (p : α → Bool) (f : α → β → β)
    (e : β) (pre : List α) (bad : α) (left right : List α)
    (all : ∀ x ∈ pre, p x = true) (failed : p bad = false) :
    foldPrefix c p f e (pre ++ bad :: left) = foldPrefix c p f e (pre ++ bad :: right) := by
  unfold foldPrefix
  rw [takeWhile_suffix_independent 1 1 1 p pre bad left right all failed]

theorem foldPrefix_failure (c : Nat) (p : α → Bool) (f : α → β → β) (e : β)
    (pre : List α) (bad : α) (rest : List α)
    (all : ∀ x ∈ pre, p x = true) (failed : p bad = false) :
    foldPrefix c p f e (pre ++ bad :: rest) = (pre.foldr f e, (4 + c) * pre.length + 3) := by
  unfold foldPrefix
  rw [takeWhile_failure 1 1 1 p pre bad rest all failed]
  apply Prod.ext
  · simp [bind, ListExecution.foldr_value]
  · simp [bind, ListExecution.foldr_work, Nat.add_mul]
    omega

theorem foldPrefix_best (c : Nat) (f : Bool → β → β) (e : β) (n : Nat) :
    foldPrefix c id f e (bestInput n) = (e, if n = 0 then 2 else 3) := by
  unfold foldPrefix
  rw [best_run]
  cases n <;> simp [bind, ListExecution.foldr]

theorem foldPrefix_worst (c : Nat) (f : Bool → β → β) (e : β) (n : Nat) :
    foldPrefix c id f e (worstInput n) = ((worstInput n).foldr f e, (4 + c) * n + 2) := by
  apply Prod.ext
  · simp [foldPrefix_value, worstInput]
  · simp [foldPrefix_work, worstInput]

/-- Bounds on the all-true pipeline witness, without a new pipeline-maximality claim. -/
theorem foldPrefix_worst_bounds (f : Bool → β → β) (e : β) (n : Nat) (hn : 0 < n) :
    5 * n ≤ (foldPrefix 1 id f e (worstInput n)).2 ∧
      (foldPrefix 1 id f e (worstInput n)).2 ≤ 7 * n := by
  rw [foldPrefix_worst]
  simp only
  omega

theorem foldPrefix_empty (c : Nat) (p : α → Bool) (f : α → β → β) (e : β) :
    foldPrefix c p f e [] = (e, 2) := rfl

end Resources.TakeWhileExtrema

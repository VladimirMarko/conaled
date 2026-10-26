import Applications.EditAlignment.Semantics

/-! Global optimality over all aligning scripts and equal-head exchange. -/
set_option autoImplicit false
set_option warningAsError true

namespace EditAlignment
universe u
variable {α : Type u}

/-- Actual source recurrence. `best a (best b c)` is its right-fold minimum
on the three candidates in Replace/Copy, Delete, Insert order. -/
def mce [DecidableEq α] : List α → List α → Script α
  | xs, [] => xs.map Op.delete
  | [], ys => ys.map Op.insert
  | x :: xs, y :: ys =>
      best (pick x y :: mce xs ys)
        (best (.delete x :: mce xs (y :: ys)) (.insert y :: mce (x :: xs) ys))
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem mce_nil_right [DecidableEq α] (xs : List α) : mce xs [] = xs.map Op.delete := by
  simp [mce]

theorem mce_nil_left [DecidableEq α] (ys : List α) : mce [] ys = ys.map Op.insert := by
  cases ys <;> simp [mce]

theorem mce_aligns [DecidableEq α] (xs ys : List α) : Aligns (mce xs ys) xs ys := by
  induction xs generalizing ys with
  | nil => rw [mce_nil_left]; exact aligns_inserts ys
  | cons x xs ihx =>
    induction ys with
    | nil => rw [mce_nil_right]; exact aligns_deletes _
    | cons y ys ihy =>
      rw [mce]
      exact aligns_best (aligns_pick x y (ihx ys))
        (aligns_best (.delete x (ihx (y :: ys))) (.insert y ihy))

theorem mce_reconstruct [DecidableEq α] (xs ys : List α) :
    reconstruct (mce xs ys) = (xs, ys) := (mce_aligns xs ys).reconstruct

theorem mce_cost_diagonal [DecidableEq α] (x y : α) (xs ys : List α) :
    costE (mce (x :: xs) (y :: ys)) ≤ ecost (pick x y) + costE (mce xs ys) := by
  rw [mce]
  simpa only [costE_cons] using
    costE_best_le_left (pick x y :: mce xs ys)
      (best (.delete x :: mce xs (y :: ys)) (.insert y :: mce (x :: xs) ys))

theorem mce_cost_delete [DecidableEq α] (x : α) (xs ys : List α) :
    costE (mce (x :: xs) ys) ≤ 2 + costE (mce xs ys) := by
  cases ys with
  | nil => simp [mce_nil_right, costE_cons, ecost]
  | cons y ys =>
    rw [mce]
    simpa only [costE_cons, ecost] using
      Nat.le_trans
        (costE_best_le_right (pick x y :: mce xs ys)
          (best (.delete x :: mce xs (y :: ys)) (.insert y :: mce (x :: xs) ys)))
        (costE_best_le_left (.delete x :: mce xs (y :: ys))
          (.insert y :: mce (x :: xs) ys))

theorem mce_cost_insert [DecidableEq α] (y : α) (xs ys : List α) :
    costE (mce xs (y :: ys)) ≤ 2 + costE (mce xs ys) := by
  cases xs with
  | nil => simp [mce_nil_left, costE_cons, ecost]
  | cons x xs =>
    rw [mce]
    simpa only [costE_cons, ecost] using
      Nat.le_trans
        (costE_best_le_right (pick x y :: mce xs ys)
          (best (.delete x :: mce xs (y :: ys)) (.insert y :: mce (x :: xs) ys)))
        (costE_best_le_right (.delete x :: mce xs (y :: ys))
          (.insert y :: mce (x :: xs) ys))

/-- Global minimum over all scripts satisfying the independent alignment semantics. -/
theorem mce_optimal_of_aligns [DecidableEq α] {es : Script α} {xs ys : List α}
    (h : Aligns es xs ys) : costE (mce xs ys) ≤ costE es := by
  induction h with
  | nil => simp [mce, costE]
  | @copy x es xs ys h ih =>
    have hd := mce_cost_diagonal x x xs ys
    simp [pick, ecost] at hd
    simpa [costE_cons, ecost] using Nat.le_trans hd ih
  | @replace x y es xs ys h ih =>
    have hd := mce_cost_diagonal x y xs ys
    have hp := ecost_pick_le_three x y
    simp only [costE_cons, ecost]
    omega
  | @delete x es xs ys h ih =>
    have hd := mce_cost_delete x xs ys
    simp only [costE_cons, ecost]
    omega
  | @insert y es xs ys h ih =>
    have hd := mce_cost_insert y xs ys
    simp only [costE_cons, ecost]
    omega

theorem mce_optimal [DecidableEq α] (xs ys : List α) (es : Script α)
    (h : reconstruct es = (xs, ys)) : costE (mce xs ys) ≤ costE es :=
  mce_optimal_of_aligns ((aligns_iff_reconstruct es xs ys).mpr h)

theorem mce_spec [DecidableEq α] (xs ys : List α) : MinimumEdit (mce xs ys) xs ys :=
  ⟨mce_aligns xs ys, fun _ h => mce_optimal_of_aligns h⟩

/-- Removing the first output symbol costs at most one deletion. -/
theorem strip_target {es : Script α} {xs : List α} {y : α} {ys : List α}
    (h : Aligns es xs (y :: ys)) :
    ∃ es', Aligns es' xs ys ∧ costE es' ≤ costE es + 2 := by
  induction es generalizing xs y ys with
  | nil => cases h
  | cons op es ih =>
    cases h with
    | copy z h =>
      exact ⟨.delete y :: es, .delete y h, by simp [costE_cons, ecost, Nat.add_comm]⟩
    | replace z y h =>
      refine ⟨.delete z :: es, .delete z h, ?_⟩
      simp only [costE_cons, ecost]
      omega
    | delete z h =>
      obtain ⟨es', he', hc'⟩ := ih h
      refine ⟨.delete z :: es', .delete z he', ?_⟩
      simp only [costE_cons, ecost]
      omega
    | insert y h =>
      refine ⟨es, h, ?_⟩
      simp only [costE_cons, ecost]
      omega

/-- Removing the first input symbol costs at most one insertion. -/
theorem strip_source {es : Script α} {x : α} {xs ys : List α}
    (h : Aligns es (x :: xs) ys) :
    ∃ es', Aligns es' xs ys ∧ costE es' ≤ costE es + 2 := by
  induction es generalizing x xs ys with
  | nil => cases h
  | cons op es ih =>
    cases h with
    | copy z h =>
      exact ⟨.insert x :: es, .insert x h, by simp [costE_cons, ecost, Nat.add_comm]⟩
    | replace x z h =>
      refine ⟨.insert z :: es, .insert z h, ?_⟩
      simp only [costE_cons, ecost]
      omega
    | delete x h =>
      refine ⟨es, h, ?_⟩
      simp only [costE_cons, ecost]
      omega
    | insert z h =>
      obtain ⟨es', he', hc'⟩ := ih h
      refine ⟨.insert z :: es', .insert z he', ?_⟩
      simp only [costE_cons, ecost]
      omega

/-- Fixed-cost exchange argument for the equal-head shortcut. -/
theorem cancel_equal_heads {es : Script α} {x : α} {xs ys : List α}
    (h : Aligns es (x :: xs) (x :: ys)) :
    ∃ es', Aligns es' xs ys ∧ costE es' ≤ costE es := by
  cases h with
  | copy x h => exact ⟨_, h, by simp [costE_cons, ecost]⟩
  | replace x y h =>
    refine ⟨_, h, ?_⟩
    simp only [costE_cons, ecost]
    omega
  | delete x h =>
    obtain ⟨es', he', hc'⟩ := strip_target h
    refine ⟨es', he', ?_⟩
    simp only [costE_cons, ecost]
    omega
  | insert x h =>
    obtain ⟨es', he', hc'⟩ := strip_source h
    refine ⟨es', he', ?_⟩
    simp only [costE_cons, ecost]
    omega

theorem mce_cost_cancel_equal_heads [DecidableEq α] (x : α) (xs ys : List α)
    (es : Script α) (h : Aligns es (x :: xs) (x :: ys)) :
    costE (mce xs ys) ≤ costE es := by
  obtain ⟨es', he', hc'⟩ := cancel_equal_heads h
  exact Nat.le_trans (mce_optimal_of_aligns he') hc'

/-- Exact witness equality: Copy is the first candidate and wins any tie. -/
theorem mce_equal_heads [DecidableEq α] (x : α) (xs ys : List α) :
    mce (x :: xs) (x :: ys) = .copy x :: mce xs ys := by
  have hd := mce_cost_cancel_equal_heads x xs ys
    (.delete x :: mce xs (x :: ys)) (.delete x (mce_aligns xs (x :: ys)))
  have hi := mce_cost_cancel_equal_heads x xs ys
    (.insert x :: mce (x :: xs) ys) (.insert x (mce_aligns (x :: xs) ys))
  have hb : costE (.copy x :: mce xs ys) ≤
      costE (best (.delete x :: mce xs (x :: ys)) (.insert x :: mce (x :: xs) ys)) := by
    simp only [costE_cons, ecost, Nat.zero_add]
    rw [best_eq]
    split <;> assumption
  rw [mce]
  simp only [pick, ↓reduceIte]
  rw [best_eq]
  exact ite_eq_left hb


end EditAlignment

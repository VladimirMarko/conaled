import Applications.Search.OrderedTree.Candidate

/-!
# Valid skew trees witness the comparison bounds

Increasing right spines are ordered trees of arbitrary depth. An absent key
beyond their largest label uses exactly twice the depth in baseline search.
Candidate search and combined insertion use depth plus one comparisons on
nonempty members of the same family. These are modeled primitive counts, not
machine-time assertions or logarithmic balance assumptions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree

def rightSpine (start : Nat) : Nat → BinaryTree Nat
  | 0 => .nil
  | n + 1 => .node start .nil (rightSpine (start + 1) n)

theorem all_rightSpine (P : Nat → Prop) (start n : Nat)
    (bound : ∀ x, start ≤ x → x < start + n → P x) : All P (rightSpine start n) := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih =>
      refine ⟨bound start (Nat.le_refl _) (by omega), trivial, ?_⟩
      exact ih (start + 1) (fun x hx hy => bound x (by omega) (by omega))

theorem rightSpine_ordered (start n : Nat) : Ordered (rightSpine start n) := by
  induction n generalizing start with
  | zero => exact ordered_nil
  | succ n ih =>
      refine ⟨ordered_nil, ih (start + 1), trivial, ?_⟩
      apply all_rightSpine
      intro x hx _
      change start < x
      omega

theorem rightSpine_height (start n : Nat) : (rightSpine start n).height = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [rightSpine, ih]

theorem rightSpine_numNodes (start n : Nat) : (rightSpine start n).numNodes = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [rightSpine, ih]

theorem rightSpine_above_absent {start n x : Nat} (above : start + n ≤ x) :
    ¬ Contains x (rightSpine start n) := by
  have lower := all_rightSpine (fun y => y < start + n) start n (fun _ _ h => h)
  exact fun present => Nat.not_lt_of_ge above (lower.of_contains present)

theorem memberRun_rightSpine {start n x : Nat} (above : start + n ≤ x) :
    (memberRun x (rightSpine start n)).2 = 2 * n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      have xs : ¬ x < start := by omega
      have sx : start < x := by omega
      simp only [rightSpine, memberRun, ite_eq_right xs, ite_eq_left sx]
      have bound := ih (start := start + 1) (by omega)
      omega

theorem memberCandidateRun_rightSpine_present {start n x c : Nat}
    (above : start + n ≤ x) :
    (memberCandidateRun x (some c) (rightSpine start n)).2 = n + 1 := by
  induction n generalizing start c with
  | zero => rfl
  | succ n ih =>
      have xs : ¬ x < start := by omega
      simp only [rightSpine, memberCandidateRun, ite_eq_right xs]
      have bound := ih (start := start + 1) (c := start) (by omega)
      omega

theorem memberCandidateRun_rightSpine {start n x : Nat} (above : start + (n + 1) ≤ x) :
    (memberCandidateRun x none (rightSpine start (n + 1))).2 = (n + 1) + 1 := by
  have xs : ¬ x < start := by omega
  simp only [rightSpine, memberCandidateRun, ite_eq_right xs]
  have count := memberCandidateRun_rightSpine_present
    (start := start + 1) (n := n) (x := x) (c := start) (by omega)
  omega

/-- One valid family with arbitrarily large height attains both bounds. -/
theorem comparison_bounds_attained (d : Nat) :
    Ordered (rightSpine 0 (d + 1)) ∧
      (rightSpine 0 (d + 1)).height = d + 1 ∧
      (memberRun (d + 1) (rightSpine 0 (d + 1))).2 = 2 * (d + 1) ∧
      (memberCandidateRun (d + 1) none (rightSpine 0 (d + 1))).2 = (d + 1) + 1 ∧
      (insertCandidateRun (d + 1) none (rightSpine 0 (d + 1))).2 = (d + 1) + 1 := by
  refine ⟨rightSpine_ordered 0 (d + 1), rightSpine_height 0 (d + 1),
    memberRun_rightSpine (by omega), memberCandidateRun_rightSpine (by omega), ?_⟩
  rw [insertCandidateRun_comparisons]
  exact memberCandidateRun_rightSpine (by omega)

end Search.OrderedTree

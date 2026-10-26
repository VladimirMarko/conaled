import Applications.Resources.TreeFlattening.Cached
import Applications.Resources.RandomAccess.Families
import Applications.Resources.Growth

/-! Exact perfect-rank costs, and growth of the actual perfect-tree executions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.TreeFlattening
open RandomAccess RandomAccessCosts
universe u
variable {α : Type u}

theorem nodes_perfect {p : Nat} {t : RandomAccess.Tree α} (h : Perfect p t) :
    nodes (erase t) + 1 = 2 * 2 ^ p := by
  have hn := structuralSizeRun_work (erase t)
  rw [← Bracketing.fringeSpec_length, ← fromT_eq_fringe, fromT_length h] at hn
  exact hn

theorem copies_perfect {p : Nat} {t : RandomAccess.Tree α} (h : Perfect p t) :
    2 * copies (erase t) = p * 2 ^ p := by
  induction h with
  | leaf x => rfl
  | node p l r hl hr ihl ihr =>
    simp only [erase, copies, ← fromT_eq_fringe, fromT_length hl, Nat.pow_succ]
    grind

theorem fromTWithCost_perfect_exact {p : Nat} {t : RandomAccess.Tree α} (h : Perfect p t) :
    2 * (fromTWithCost (erase t)).2 + 2 = (p + 4) * 2 ^ p := by
  rw [fromTWithCost_count]
  have hn := nodes_perfect h
  have hc := copies_perfect h
  simp only [Nat.add_mul] at *
  omega

theorem fromTsWithCost_perfect_exact {p : Nat} {t : RandomAccess.Tree α} (h : Perfect p t) :
    (fromTsWithCost [erase t]).2 = 2 * 2 ^ p := by
  simp only [fromTsWithCost_exact, pending, Nat.add_zero]
  exact nodes_perfect h

theorem fromTWithCost_perfect_bounds {p : Nat} {t : RandomAccess.Tree α}
    (h : Perfect p t) (hp : 1 ≤ p) :
    p * 2 ^ p ≤ 2 * (fromTWithCost (erase t)).2 ∧
      (fromTWithCost (erase t)).2 ≤ 3 * (p * 2 ^ p) := by
  have he := fromTWithCost_perfect_exact h
  have hb : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
  have hm := Nat.mul_le_mul_right (2 ^ p) (show p + 4 ≤ 6 * p by omega)
  simp only [Nat.add_mul, Nat.mul_assoc] at he hm
  omega

theorem recursive_flatten_theta (x : α) :
    Asymptotics.IsTheta Filter.atTop
      (fun p => ((cachedFromTWithCost (perfectTree x p)).2 : ℝ))
      (fun p => ((p * 2 ^ p : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ 3 1
    intro p hp
    rw [cachedFromTWithCost_erasure]
    exact (fromTWithCost_perfect_bounds (perfectTree_valid x p) hp).2
  · apply isBigO_of_nat_bound _ _ 2 1
    intro p hp
    rw [cachedFromTWithCost_erasure]
    exact (fromTWithCost_perfect_bounds (perfectTree_valid x p) hp).1

theorem stack_flatten_theta (x : α) :
    Asymptotics.IsTheta Filter.atTop
      (fun p => ((cachedFromTsWithCost [perfectTree x p]).2 : ℝ))
      (fun p => ((2 ^ p : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ 2 0
    intro p _
    rw [cachedFromTsWithCost_erasure]
    exact Nat.le_of_eq (fromTsWithCost_perfect_exact (perfectTree_valid x p))
  · apply isBigO_of_nat_bound _ _ 1 0
    intro p _
    rw [cachedFromTsWithCost_erasure]
    simp only [List.map_cons, List.map_nil, fromTsWithCost_perfect_exact (perfectTree_valid x p)]
    omega

end Resources.TreeFlattening

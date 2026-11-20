import Applications.Resources.IntervalTree
import Applications.Trees.HeightBalance.HeightBound
import Applications.Resources.Growth

/-!
# Logarithmic measured interval queries

Actual input-shape balance and global projection/comparison cost bounds suffice.
The callbacks may return arbitrary values, and the stored summaries may be
malformed. Semantic erasure and query completeness remain separate contracts.
The size parameter counts original nodes, with no distinct-key interpretation.
Correspondence: `docs/research/fdsa-measured-rectangle-scan.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.IntervalTree

universe u v
variable {α : Type u} {κ : Type v} [LE α] [Bot α]

theorem searchRun_cost_le_clog (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : Search.IntervalKey α) (d P E : Nat)
    (hP : ∀ a, (ivRun a).2 ≤ P)
    (hE : ∀ x y, (leRun x y).2 ≤ E)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (searchRun ivRun leRun t query).2 ≤
      (P + 3 * E + 2) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  exact (searchRun_cost_le ivRun leRun t query P E hP hE).trans
    (by simpa only [Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left (P + 3 * E + 2) height) 1)

/-- Arbitrary exact-size balanced tree and query families, at fixed callback
tariffs, have ordinary real logarithmic query work. -/
theorem searchRun_isBigO (ivRun : κ → Measured (Search.IntervalKey α) Nat)
    (leRun : α → α → Measured Bool Nat) (d : Nat)
    (queries : Nat → Search.IntervalKey α)
    (family : Nat → BinaryTree (κ × (Nat × α))) (P E : Nat)
    (hP : ∀ a, (ivRun a).2 ≤ P)
    (hE : ∀ x y, (leRun x y).2 ≤ E)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((searchRun ivRun leRun (family n) (queries n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Resources.isBigO_logb_succ_of_clog_bound _ ((P + 3 * E + 2) * (d + 1)) 1 0
  intro n _
  simpa only [sizes n] using
    searchRun_cost_le_clog ivRun leRun (family n) (queries n) d P E hP hE (balanced n)

end Resources.IntervalTree

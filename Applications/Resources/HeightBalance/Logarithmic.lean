import Applications.Resources.HeightBalance.Updates
import Applications.Trees.HeightBalance.HeightBound
import Applications.Resources.Growth

/-!
# Logarithmic measured height-balanced updates

Actual input-shape balance converts the existing structural work bounds to
integer logarithmic bounds. Global callback costs cover newly constructed
summaries; no callback-value, cache-validity or ordering premise is imposed for
these cost results. Family consequences fix callbacks, tolerance and tariffs,
and index arbitrary inputs by their actual node counts. Distinct-key cardinality
and stored height are not substituted for those measures.
Correspondence: `docs/research/fdsa-height-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HeightBalance

universe u v
variable {α : Type u} {σ : Type v}

theorem insertRun_cost_le_clog (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (insertRun empty heightRun combineRun ltRun d x t).2 ≤
      (1 + 2 * C + (18 + 4 * H + 3 * K)) * (d + 1) *
        Nat.clog 2 (t.numNodes + 1) + K + 4 := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  have bound := insertRun_cost_le empty heightRun combineRun ltRun d x t H K C hH hK hC
  exact bound.trans (by
    simpa only [Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left (1 + 2 * C + (18 + 4 * H + 3 * K)) height) K) 4)

/-- A nonempty extraction omits the empty-input additive charge. -/
theorem splitMaxRun_cost_le_clog_of_ne_nil
    (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (t : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t))
    (hne : t ≠ .nil) :
    (splitMaxRun empty heightRun combineRun d t).2 ≤
      (18 + 4 * H + 3 * K + 1) * (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  exact (splitMaxRun_cost_le_of_ne_nil empty heightRun combineRun d t H K hH hK hne).trans
    (by simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left (18 + 4 * H + 3 * K + 1) height)

theorem splitMaxRun_cost_le_clog (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (t : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (splitMaxRun empty heightRun combineRun d t).2 ≤
      (18 + 4 * H + 3 * K + 1) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  exact (splitMaxRun_cost_le empty heightRun combineRun d t H K hH hK).trans
    (by simpa only [Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left (18 + 4 * H + 3 * K + 1) height) 1)

theorem deleteRun_cost_le_clog (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (deleteRun empty heightRun combineRun ltRun d x t).2 ≤
      (1 + 2 * C + (18 + 4 * H + 3 * K)) * (d + 1) *
        Nat.clog 2 (t.numNodes + 1) + 1 := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  exact (deleteRun_cost_le empty heightRun combineRun ltRun d x t H K C hH hK hC).trans
    (by simpa only [Nat.mul_assoc] using
      (Nat.add_le_add_right
        (Nat.mul_le_mul_left (1 + 2 * C + (18 + 4 * H + 3 * K)) height) 1))

/-- Fixed callbacks and uniform costs give ordinary logarithmic insertion work
for every exact-size balanced input family and every sequence of inserted keys. -/
theorem insertRun_isBigO (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (keys : Nat → α) (family : Nat → BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((insertRun empty heightRun combineRun ltRun d (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Resources.isBigO_logb_succ_of_clog_bound _
    ((1 + 2 * C + (18 + 4 * H + 3 * K)) * (d + 1)) (K + 4) 0
  intro n _
  simpa only [sizes n, Nat.add_assoc] using
    insertRun_cost_le_clog empty heightRun combineRun ltRun d (keys n) (family n)
      H K C hH hK hC (balanced n)

theorem splitMaxRun_isBigO (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (family : Nat → BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((splitMaxRun empty heightRun combineRun d (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Resources.isBigO_logb_succ_of_clog_bound _
    ((18 + 4 * H + 3 * K + 1) * (d + 1)) 1 0
  intro n _
  simpa only [sizes n] using
    splitMaxRun_cost_le_clog empty heightRun combineRun d (family n) H K hH hK (balanced n)

theorem deleteRun_isBigO (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (keys : Nat → α) (family : Nat → BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((deleteRun empty heightRun combineRun ltRun d (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Resources.isBigO_logb_succ_of_clog_bound _
    ((1 + 2 * C + (18 + 4 * H + 3 * K)) * (d + 1)) 1 0
  intro n _
  simpa only [sizes n] using
    deleteRun_cost_le_clog empty heightRun combineRun ltRun d (keys n) (family n)
      H K C hH hK hC (balanced n)

end Resources.HeightBalance

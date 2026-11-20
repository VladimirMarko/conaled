import Applications.Resources.SearchTree
import Applications.Search.OrderedMap.Membership
import Applications.Trees.HeightBalance.HeightBound

/-!
# Measured comparison-path membership in annotated trees

One actual generic lookup supplies both its returned annotation and its reached
node/comparator observations. The scalar tariff charges one per visited node,
the actual executed comparisons, and one terminal nil only on failure. It does
not read stored heights or execute erasure. The Boolean wrapper observes the
same returned Option at the same cost. Projections and observation arithmetic
are free in this declared source model, not assertions about machine execution.
Correspondence: docs/research/fdsa-avl-continuation.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

def lookupRun (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) : Measured (Option σ) Nat :=
  let actual := SearchTree.lookupWithRun ltRun q t
  (actual.1, actual.2.1 + actual.2.2 + if actual.1.isNone then 1 else 0)

def memberRun (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) : Measured Bool Nat :=
  let actual := lookupRun ltRun q t
  (actual.1.isSome, actual.2)

@[simp] theorem lookupRun_nil (ltRun : α → α → Measured Bool Nat) (q : α) :
    lookupRun (σ := σ) ltRun q .nil = (none, 1) := rfl

@[simp] theorem memberRun_nil (ltRun : α → α → Measured Bool Nat) (q : α) :
    memberRun (σ := σ) ltRun q .nil = (false, 1) := rfl

/-- Exact source-order recurrence, including only the reached child. -/
theorem lookupRun_node (ltRun : α → α → Measured Bool Nat) (q : α)
    (b : α × σ) (l r : BinaryTree (α × σ)) :
    lookupRun ltRun q (.node b l r) =
      if (ltRun q b.1).1 then
        ((lookupRun ltRun q l).1, 1 + (ltRun q b.1).2 + (lookupRun ltRun q l).2)
      else if (ltRun b.1 q).1 then
        ((lookupRun ltRun q r).1,
          1 + (ltRun q b.1).2 + (ltRun b.1 q).2 + (lookupRun ltRun q r).2)
      else (some b.2, 1 + (ltRun q b.1).2 + (ltRun b.1 q).2) := by
  simp only [lookupRun, SearchTree.lookupWithRun_node]
  split
  · apply Prod.ext
    · rfl
    · dsimp; omega
  · split
    · apply Prod.ext
      · rfl
      · dsimp; omega
    · apply Prod.ext
      · rfl
      · dsimp; omega

theorem memberRun_node (ltRun : α → α → Measured Bool Nat) (q : α)
    (b : α × σ) (l r : BinaryTree (α × σ)) :
    memberRun ltRun q (.node b l r) =
      if (ltRun q b.1).1 then
        ((memberRun ltRun q l).1, 1 + (ltRun q b.1).2 + (memberRun ltRun q l).2)
      else if (ltRun b.1 q).1 then
        ((memberRun ltRun q r).1,
          1 + (ltRun q b.1).2 + (ltRun b.1 q).2 + (memberRun ltRun q r).2)
      else (true, 1 + (ltRun q b.1).2 + (ltRun b.1 q).2) := by
  simp only [memberRun, lookupRun_node]
  split
  · rfl
  · split <;> rfl

@[simp] theorem memberRun_cost (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) : (memberRun ltRun q t).2 = (lookupRun ltRun q t).2 := rfl

/-- The weaker finite-input callback premise suffices for raw value erasure. -/
theorem lookupRun_value [LT α] [DecidableLT α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (local_value : Search.OrderedTree.All (fun b =>
      (ltRun q b.1).1 = decide (q < b.1) ∧
      (ltRun b.1 q).1 = decide (b.1 < q)) t) :
    (lookupRun ltRun q t).1 = Search.OrderedMap.lookup q t :=
  SearchTree.lookupWithRun_value ltRun q t local_value

theorem lookupRun_value_of_global [LT α] [DecidableLT α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (values : ∀ a b, (ltRun a b).1 = decide (a < b)) :
    (lookupRun ltRun q t).1 = Search.OrderedMap.lookup q t :=
  lookupRun_value ltRun q t ((Search.OrderedTree.all_iff _ _).2
    (fun b _ => ⟨values q b.1, values b.1 q⟩))

theorem memberRun_value [LT α] [DecidableLT α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (values : ∀ a b, (ltRun a b).1 = decide (a < b)) :
    (memberRun ltRun q t).1 = Search.OrderedMap.containsKey q t := by
  change (lookupRun ltRun q t).1.isSome = (Search.OrderedMap.lookup q t).isSome
  rw [lookupRun_value_of_global ltRun q t values]

/-- Strict search ordering, independently of cached heights, supplies semantics. -/
theorem memberRun_correct [LinearOrder α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (values : ∀ a b, (ltRun a b).1 = decide (a < b))
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) :
    (memberRun ltRun q t).1 = true ↔ q ∈ Trees.setTree (Trees.Cached.erase t) := by
  rw [memberRun_value ltRun q t values]
  exact (Search.OrderedMap.containsKey_eq_true_iff_of_inorder_pairwise strict q).trans
    (Trees.mem_inorder_iff_mem_setTree q (Trees.Cached.erase t))

theorem lookupRun_cost_le_of_local (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (C : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ C ∧ (ltRun b.1 q).2 ≤ C) t) :
    (lookupRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 := by
  have bound := SearchTree.lookupWithRun_weighted_bound ltRun q t C 1 local_bound
  simp only [Nat.one_mul] at bound
  change (SearchTree.lookupWithRun ltRun q t).2.1 +
    (SearchTree.lookupWithRun ltRun q t).2.2 +
    (if (SearchTree.lookupWithRun ltRun q t).1.isNone then 1 else 0) ≤ _
  split <;> omega

theorem memberRun_cost_le_of_local (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (C : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ C ∧ (ltRun b.1 q).2 ≤ C) t) :
    (memberRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 :=
  lookupRun_cost_le_of_local ltRun q t C local_bound

theorem lookupRun_cost_le (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (C : Nat) (hC : ∀ a b, (ltRun a b).2 ≤ C) :
    (lookupRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 :=
  lookupRun_cost_le_of_local ltRun q t C ((Search.OrderedTree.all_iff _ _).2
    (fun b _ => ⟨hC q b.1, hC b.1 q⟩))

theorem memberRun_cost_le (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (C : Nat) (hC : ∀ a b, (ltRun a b).2 ≤ C) :
    (memberRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 :=
  lookupRun_cost_le ltRun q t C hC

theorem lookupRun_cost_le_clog (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (d C : Nat) (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (lookupRun ltRun q t).2 ≤
      (1 + 2 * C) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 := by
  have height : t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
    simpa only [Trees.Cached.height_erase, Trees.Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d (Trees.Cached.erase t) balanced
  exact (lookupRun_cost_le ltRun q t C hC).trans (by
    simpa only [Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left (1 + 2 * C) height) 1)

theorem memberRun_cost_le_clog (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (d C : Nat) (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (balanced : Trees.HeightBalance.BalancedD d (Trees.Cached.erase t)) :
    (memberRun ltRun q t).2 ≤
      (1 + 2 * C) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 :=
  lookupRun_cost_le_clog ltRun q t d C hC balanced

theorem lookupRun_isBigO (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (queries : Nat → α) (family : Nat → BinaryTree (α × σ)) (C : Nat)
    (hC : ∀ a b, (ltRun a b).2 ≤ C) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((lookupRun ltRun (queries n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Resources.isBigO_logb_succ_of_clog_bound _ ((1 + 2 * C) * (d + 1)) 1 0
  intro n _
  simpa only [sizes n] using lookupRun_cost_le_clog ltRun (queries n) (family n) d C hC (balanced n)

theorem memberRun_isBigO (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (queries : Nat → α) (family : Nat → BinaryTree (α × σ)) (C : Nat)
    (hC : ∀ a b, (ltRun a b).2 ≤ C) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((memberRun ltRun (queries n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  lookupRun_isBigO ltRun d queries family C hC sizes balanced

end Resources.HeightBalance

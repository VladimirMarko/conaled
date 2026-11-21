import Applications.Resources.HeightBalance.Rebalance
import Applications.Trees.HeightBalance.Updates

/-!
# Measured complete-annotation height-balanced updates

Each update or extraction invocation costs one. Strict-key callbacks select
the actual branch; repair consumes the actual recursive result. Equal-key
insertion reconstructs the original raw node for one constructor event, retaining
its original complete summary. Extraction stops at a node with an empty right
child, without a recursive call on that empty child. Matched-root deletion
executes extraction even when its left child is empty.

Costs are source-event observations, separate from callback-value correctness,
cache validity, ordering, balance, runtime, allocation and bit complexity.
Correspondence and the remaining concrete interval-query composition are in
`docs/research/fdsa-height-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HeightBalance

universe u v
variable {α : Type u} {σ : Type v}

/-- Execute comparisons, one changed child, and the correctly oriented repair. -/
def insertRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α) :
    BinaryTree (α × σ) → Measured (BinaryTree (α × σ)) Nat
  | .nil => CallCount.tick (TreeCache.nodeRun empty combineRun .nil x .nil)
  | .node (a, s) l r =>
      CallCount.tick (bind (ltRun x a) (fun first =>
        if first then
          bind (insertRun empty heightRun combineRun ltRun d x l) (fun left =>
            balLRun empty heightRun combineRun d left a r)
        else bind (ltRun a x) (fun second =>
          if second then
            bind (insertRun empty heightRun combineRun ltRun d x r) (fun right =>
              balRRun empty heightRun combineRun d l a right)
          else (.node (a, s) l r, 1))))

/-- Execute rightmost extraction; the returned tree precedes the payload. -/
def splitMaxRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat) :
    BinaryTree (α × σ) → Measured (Option (BinaryTree (α × σ) × α)) Nat
  | .nil => (none, 1)
  | .node (a, _) l .nil => (some (l, a), 1)
  | .node (a, _) l (.node b rl rr) =>
      CallCount.tick (bind (splitMaxRun empty heightRun combineRun d (.node b rl rr))
        (fun result => match result with
          | none => pure none
          | some (right, m) =>
              bind (balLRun empty heightRun combineRun d l a right) (fun changed =>
                pure (some (changed, m)))))

/-- Execute predecessor deletion with one or two actual strict comparisons. -/
def deleteRun (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α) :
    BinaryTree (α × σ) → Measured (BinaryTree (α × σ)) Nat
  | .nil => (.nil, 1)
  | .node (a, _) l r =>
      CallCount.tick (bind (ltRun x a) (fun first =>
        if first then
          bind (deleteRun empty heightRun combineRun ltRun d x l) (fun left =>
            balRRun empty heightRun combineRun d left a r)
        else bind (ltRun a x) (fun second =>
          if second then
            bind (deleteRun empty heightRun combineRun ltRun d x r) (fun right =>
              balLRun empty heightRun combineRun d l a right)
          else bind (splitMaxRun empty heightRun combineRun d l) (fun result =>
            match result with
            | none => pure r
            | some (left, m) => balRRun empty heightRun combineRun d left m r))))

@[simp] theorem insertRun_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α) :
    insertRun empty heightRun combineRun ltRun d x .nil =
      CallCount.tick (TreeCache.nodeRun empty combineRun .nil x .nil) := rfl

theorem insertRun_node (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    insertRun empty heightRun combineRun ltRun d x (.node (a, s) l r) =
      CallCount.tick (bind (ltRun x a) (fun first =>
        if first then
          bind (insertRun empty heightRun combineRun ltRun d x l) (fun left =>
            balLRun empty heightRun combineRun d left a r)
        else bind (ltRun a x) (fun second =>
          if second then
            bind (insertRun empty heightRun combineRun ltRun d x r) (fun right =>
              balRRun empty heightRun combineRun d l a right)
          else (.node (a, s) l r, 1)))) := rfl

@[simp] theorem splitMaxRun_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat) :
    splitMaxRun empty heightRun combineRun d .nil = (none, 1) := rfl

@[simp] theorem splitMaxRun_node_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat) (a : α) (s : σ)
    (l : BinaryTree (α × σ)) :
    splitMaxRun empty heightRun combineRun d (.node (a, s) l .nil) =
      (some (l, a), 1) := rfl

theorem splitMaxRun_node_of_ne_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat) (a : α) (s : σ)
    (l r : BinaryTree (α × σ)) (hr : r ≠ .nil) :
    splitMaxRun empty heightRun combineRun d (.node (a, s) l r) =
      CallCount.tick (bind (splitMaxRun empty heightRun combineRun d r)
        (fun result => match result with
          | none => pure none
          | some (right, m) =>
              bind (balLRun empty heightRun combineRun d l a right) (fun changed =>
                pure (some (changed, m))))) := by
  cases r with
  | nil => exact (hr rfl).elim
  | node b rl rr => rfl

@[simp] theorem deleteRun_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α) :
    deleteRun empty heightRun combineRun ltRun d x .nil = (.nil, 1) := rfl

theorem deleteRun_node (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    deleteRun empty heightRun combineRun ltRun d x (.node (a, s) l r) =
      CallCount.tick (bind (ltRun x a) (fun first =>
        if first then
          bind (deleteRun empty heightRun combineRun ltRun d x l) (fun left =>
            balRRun empty heightRun combineRun d left a r)
        else bind (ltRun a x) (fun second =>
          if second then
            bind (deleteRun empty heightRun combineRun ltRun d x r) (fun right =>
              balLRun empty heightRun combineRun d l a right)
          else bind (splitMaxRun empty heightRun combineRun d l) (fun result =>
            match result with
            | none => pure r
            | some (left, m) => balRRun empty heightRun combineRun d left m r)))) := rfl

/-- Raw insertion erasure does not assume trichotomy or a valid cached tree. -/
theorem insertRun_value [LT α] [DecidableLT α]
    (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s)
    (hcombine : ∀ s a r, (combineRun s a r).1 = ann.combine s a r)
    (hlt : ∀ a b, (ltRun a b).1 = decide (a < b)) :
    (insertRun ann.empty heightRun combineRun ltRun d x t).1 =
      Trees.HeightBalance.insert ann d x t := by
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :=
    balLRun_value ann heightRun combineRun d l a r hheight hcombine
  have hR (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :=
    balRRun_value ann heightRun combineRun d l a r hheight hcombine
  induction t with
  | nil =>
      exact TreeCache.nodeRun_value ann.empty ann.combine combineRun .nil x .nil
        (hcombine _ _ _)
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      rw [insertRun_node, Trees.HeightBalance.insert_node]
      simp only [CallCount.tick_value, bind_value, hlt, decide_eq_true_eq]
      split
      · simp only [bind_value, hL, ihl]
      · simp only [bind_value, hlt, decide_eq_true_eq]
        split
        · simp only [bind_value, hR, ihr]
        · rfl

/-- Raw extraction erasure requires neither an order nor an inhabited payload. -/
theorem splitMaxRun_value (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (t : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s)
    (hcombine : ∀ s a r, (combineRun s a r).1 = ann.combine s a r) :
    (splitMaxRun ann.empty heightRun combineRun d t).1 =
      Trees.HeightBalance.splitMaxOption ann d t := by
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :=
    balLRun_value ann heightRun combineRun d l a r hheight hcombine
  induction t with
  | nil => rfl
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      by_cases hr : r = .nil
      · subst r
        rfl
      · rw [splitMaxRun_node_of_ne_nil _ _ _ _ _ _ _ _ hr,
          Trees.HeightBalance.splitMaxOption_node_of_ne_nil _ _ _ _ _ _ hr, ← ihr]
        simp only [CallCount.tick_value, bind_value]
        cases he : (splitMaxRun ann.empty heightRun combineRun d r).1 with
        | none => rfl
        | some p =>
            rcases p with ⟨right, m⟩
            simp only [bind_value, pure, hL, Option.map_some]

/-- Raw deletion follows the actual extracted predecessor and remaining tree. -/
theorem deleteRun_value [LT α] [DecidableLT α]
    (ann : Trees.HeightBalance.HeightAnnotation α σ)
    (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hheight : ∀ s, (heightRun s).1 = ann.height s)
    (hcombine : ∀ s a r, (combineRun s a r).1 = ann.combine s a r)
    (hlt : ∀ a b, (ltRun a b).1 = decide (a < b)) :
    (deleteRun ann.empty heightRun combineRun ltRun d x t).1 =
      Trees.HeightBalance.delete ann d x t := by
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :=
    balLRun_value ann heightRun combineRun d l a r hheight hcombine
  have hR (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :=
    balRRun_value ann heightRun combineRun d l a r hheight hcombine
  induction t with
  | nil => rfl
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      rw [deleteRun_node, Trees.HeightBalance.delete_node]
      simp only [CallCount.tick_value, bind_value, hlt, decide_eq_true_eq]
      split
      · simp only [bind_value, hR, ihl]
      · simp only [bind_value, hlt, decide_eq_true_eq]
        split
        · simp only [bind_value, hL, ihr]
        · simp only [bind_value]
          rw [← splitMaxRun_value ann heightRun combineRun d l hheight hcombine]
          cases he : (splitMaxRun ann.empty heightRun combineRun d l).1 with
          | none => rfl
          | some p =>
              rcases p with ⟨left, m⟩
              exact hR left m r

/-- Global bounds include the callback arguments reached after every repair.
The tree may be malformed and the callbacks may return arbitrary values. -/
theorem insertRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C) :
    (insertRun empty heightRun combineRun ltRun d x t).2 ≤
      (1 + 2 * C + (18 + 4 * H + 3 * K)) * t.height + K + 4 := by
  let B := 18 + 4 * H + 3 * K
  let A := 1 + 2 * C + B
  change (insertRun empty heightRun combineRun ltRun d x t).2 ≤ A * t.height + K + 4
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
      (balLRun empty heightRun combineRun d l a r).2 ≤ B :=
    balLRun_cost_le empty heightRun combineRun d l a r H K hH hK
  have hR (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
      (balRRun empty heightRun combineRun d l a r).2 ≤ B :=
    balRRun_cost_le empty heightRun combineRun d l a r H K hH hK
  induction t with
  | nil =>
      have hn := TreeCache.nodeRun_le empty combineRun (.nil : BinaryTree (α × σ))
        x .nil K (hK _ _ _)
      simp only [insertRun_nil, CallCount.tick_cost, BinaryTree.height, Nat.mul_zero]
      omega
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      have hl := Nat.mul_le_mul_left A (Nat.le_max_left l.height r.height)
      have hr := Nat.mul_le_mul_left A (Nat.le_max_right l.height r.height)
      have hc1 := hC x a
      have hc2 := hC a x
      rw [insertRun_node]
      simp only [CallCount.tick_cost, bind, BinaryTree.height, Nat.mul_add, Nat.mul_one]
      split
      · have hb := hL (insertRun empty heightRun combineRun ltRun d x l).1 a r
        dsimp only [A] at *
        omega
      · split
        · have hb := hR l a (insertRun empty heightRun combineRun ltRun d x r).1
          dsimp only [A] at *
          omega
        · dsimp only [A] at *
          omega

/-- A nonempty extraction stops before calling the empty right child. -/
theorem splitMaxRun_cost_le_of_ne_nil (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (t : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K) (hne : t ≠ .nil) :
    (splitMaxRun empty heightRun combineRun d t).2 ≤
      (18 + 4 * H + 3 * K + 1) * t.height := by
  let B := 18 + 4 * H + 3 * K
  change (splitMaxRun empty heightRun combineRun d t).2 ≤ (B + 1) * t.height
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
      (balLRun empty heightRun combineRun d l a r).2 ≤ B :=
    balLRun_cost_le empty heightRun combineRun d l a r H K hH hK
  induction t with
  | nil => exact (hne rfl).elim
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      by_cases hr : r = .nil
      · subst r
        simp only [splitMaxRun_node_nil, BinaryTree.height, Nat.max_zero,
          Nat.mul_add, Nat.mul_one]
        omega
      · have hi := ihr hr
        have hm := Nat.mul_le_mul_left (B + 1) (Nat.le_max_right l.height r.height)
        rw [splitMaxRun_node_of_ne_nil _ _ _ _ _ _ _ _ hr]
        simp only [CallCount.tick_cost, bind, BinaryTree.height, Nat.mul_add, Nat.mul_one]
        cases he : (splitMaxRun empty heightRun combineRun d r).1 with
        | none =>
            simp only [pure]
            omega
        | some p =>
            rcases p with ⟨right, m⟩
            have hb := hL l a right
            simp only [pure]
            omega

theorem splitMaxRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat) (d : Nat)
    (t : BinaryTree (α × σ)) (H K : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K) :
    (splitMaxRun empty heightRun combineRun d t).2 ≤
      (18 + 4 * H + 3 * K + 1) * t.height + 1 := by
  by_cases he : t = .nil
  · subst t
    simp only [splitMaxRun_nil, BinaryTree.height, Nat.mul_zero, Nat.zero_add, le_refl]
  · exact (splitMaxRun_cost_le_of_ne_nil empty heightRun combineRun d t H K hH hK he).trans
      (Nat.le_add_right _ 1)

/-- Search-prefix work and actual predecessor extraction fit the same input
height bound; deletion does not charge an unsuccessful second search. -/
theorem deleteRun_cost_le (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ s a r, (combineRun s a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C) :
    (deleteRun empty heightRun combineRun ltRun d x t).2 ≤
      (1 + 2 * C + (18 + 4 * H + 3 * K)) * t.height + 1 := by
  let B := 18 + 4 * H + 3 * K
  let A := 1 + 2 * C + B
  change (deleteRun empty heightRun combineRun ltRun d x t).2 ≤ A * t.height + 1
  have hL (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
      (balLRun empty heightRun combineRun d l a r).2 ≤ B :=
    balLRun_cost_le empty heightRun combineRun d l a r H K hH hK
  have hR (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
      (balRRun empty heightRun combineRun d l a r).2 ≤ B :=
    balRRun_cost_le empty heightRun combineRun d l a r H K hH hK
  induction t with
  | nil => rfl
  | node p l r ihl ihr =>
      rcases p with ⟨a, s⟩
      have hl := Nat.mul_le_mul_left A (Nat.le_max_left l.height r.height)
      have hr := Nat.mul_le_mul_left A (Nat.le_max_right l.height r.height)
      have hc1 := hC x a
      have hc2 := hC a x
      rw [deleteRun_node]
      simp only [CallCount.tick_cost, bind, BinaryTree.height, Nat.mul_add, Nat.mul_one]
      split
      · have hb := hR (deleteRun empty heightRun combineRun ltRun d x l).1 a r
        dsimp only [A] at *
        omega
      · split
        · have hb := hL l a (deleteRun empty heightRun combineRun ltRun d x r).1
          dsimp only [A] at *
          omega
        · have hs : (splitMaxRun empty heightRun combineRun d l).2 ≤
              (B + 1) * l.height + 1 :=
            splitMaxRun_cost_le empty heightRun combineRun d l H K hH hK
          have hBA : B + 1 ≤ A := by dsimp only [A]; omega
          have hm := Nat.mul_le_mul_right l.height hBA
          cases he : (splitMaxRun empty heightRun combineRun d l).1 with
          | none =>
              simp only [pure]
              dsimp only [A] at *
              omega
          | some p =>
              rcases p with ⟨left, m⟩
              have hb := hR left m r
              dsimp only [A] at *
              omega

end Resources.HeightBalance

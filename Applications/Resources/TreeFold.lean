import Applications.Trees.Observations
import Applications.Resources.CallCount
import Mathlib.Tactic.Ring

/-! Actual measured tree folds, as a specialization of the ordinary fold.
The generic operation preserves observation order and grouping under `Add`.
Natural-number cost laws separately collect structural entry charges and
the work performed by the actual callback. Source and statement assessment:
`docs/research/fdsa-tree-fold-resource.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeFold
universe u v w x y
variable {α : Type u} {β : Type v} {C : Type w} {D : Type x} {γ : Type y}

/-- Sequence the left result, right result and actual combining callback,
then post the structural entry observation. Nil has only that entry charge.
This is one ordinary fold, with no separate recursive cost evaluator. -/
def run [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (t : BinaryTree α) : Measured β C :=
  Trees.fold (empty, entry) (fun left a right =>
    let body := bind left (fun l => bind right (fun r => combineRun l a r))
    (body.1, body.2 + entry)) t

@[simp] theorem run_nil [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) :
    run entry empty combineRun .nil = (empty, entry) := rfl

/-- These parentheses are part of the contract under mere `Add`. -/
theorem run_node [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (a : α) (l r : BinaryTree α) :
    run entry empty combineRun (.node a l r) =
      ((combineRun (run entry empty combineRun l).1 a
          (run entry empty combineRun r).1).1,
        ((run entry empty combineRun l).2 +
          ((run entry empty combineRun r).2 +
            (combineRun (run entry empty combineRun l).1 a
              (run entry empty combineRun r).1).2)) + entry) := rfl

theorem run_node_cost [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (a : α) (l r : BinaryTree α) :
    (run entry empty combineRun (.node a l r)).2 =
      ((run entry empty combineRun l).2 +
        ((run entry empty combineRun r).2 +
          (combineRun (run entry empty combineRun l).1 a
            (run entry empty combineRun r).1).2)) + entry := rfl

/-- Entry one uses the existing post-body call-count operation exactly. -/
theorem run_node_tick (empty : β) (combineRun : β → α → β → Measured β Nat)
    (a : α) (l r : BinaryTree α) :
    run 1 empty combineRun (.node a l r) =
      CallCount.tick (bind (run 1 empty combineRun l) (fun left =>
        bind (run 1 empty combineRun r) (fun right => combineRun left a right))) := rfl

/-- Transport on given input trees does not charge for computing the map. -/
theorem run_map [Add C] (entry : C) (empty : β)
    (combineRun : β → γ → β → Measured β C) (label : α → γ) (t : BinaryTree α) :
    run entry empty combineRun (t.map label) =
      run entry empty (fun l a r => combineRun l (label a) r) t := by
  unfold run
  exact Trees.fold_map _ _ label t

/-- Value erasure is unconditional and requires no observation laws. -/
theorem run_value [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (t : BinaryTree α) :
    (run entry empty combineRun t).1 =
      Trees.fold empty (fun l a r => (combineRun l a r).1) t := by
  unfold run
  exact Trees.fold_fusion (empty, entry) _ empty
    (fun l a r => (combineRun l a r).1) Prod.fst rfl (fun _ _ _ => rfl) t

/-- Only the entry observation changes; the callback and empty value stay fixed. -/
theorem run_value_entry [Add C] (entry entry' : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (t : BinaryTree α) :
    (run entry empty combineRun t).1 = (run entry' empty combineRun t).1 := by
  rw [run_value, run_value]

/-- A pointwise callback law is sufficient to refine an independent algebra. -/
theorem run_value_of [Add C] (entry : C) (empty : β)
    (combineRun : β → α → β → Measured β C) (combine : β → α → β → β)
    (hvalue : ∀ l a r, (combineRun l a r).1 = combine l a r) (t : BinaryTree α) :
    (run entry empty combineRun t).1 = Trees.fold empty combine t := by
  rw [run_value]
  have hc : (fun l a r => (combineRun l a r).1) = combine := by
    funext l a r
    exact hvalue l a r
  rw [hc]

/-- Additive observation transport preserves the same execution and values.
The monoid assumptions come from the existing hom interface; no commutativity
is required. -/
theorem reweight_run [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (entry : C) (empty : β) (combineRun : β → α → β → Measured β C)
    (t : BinaryTree α) :
    reweight h (run entry empty combineRun t) =
      run (h entry) empty (fun l a r => reweight h (combineRun l a r)) t := by
  unfold run
  refine Trees.fold_fusion _ _ _ _ (reweight h) rfl ?_ t
  intro left a right
  have hb : reweight h (bind left (fun l => bind right (fun r => combineRun l a r))) =
      bind (reweight h left) (fun l =>
        bind (reweight h right) (fun r => reweight h (combineRun l a r))) := by
    simp only [reweight_bind]
  simpa only [reweight, map_add] using
    congrArg (fun body : Measured β D => (body.1, body.2 + h entry)) hb

/-- The callback-only term is an actual zero-entry run of the same operation.
Value erasure establishes equal reached callback arguments before collecting
the natural structural charges. -/
theorem run_cost_entry (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (t : BinaryTree α) :
    (run entry empty combineRun t).2 =
      (run 0 empty combineRun t).2 + entry * (2 * t.numNodes + 1) := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      rw [run_node_cost, run_node_cost, ihl, ihr,
        run_value_entry entry 0 empty combineRun l,
        run_value_entry entry 0 empty combineRun r]
      simp only [BinaryTree.numNodes]
      ring

theorem structural_le_cost (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (t : BinaryTree α) :
    entry * (2 * t.numNodes + 1) ≤ (run entry empty combineRun t).2 := by
  rw [run_cost_entry]
  exact Nat.le_add_left _ _

/-- The premise covers summaries returned on arbitrary finite child trees,
at these fixed parameters. It need not hold on every possible summary value. -/
theorem run_cost_const (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (k : Nat)
    (hcost : ∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
      (combineRun (run entry empty combineRun l).1 a
        (run entry empty combineRun r).1).2 = k) (t : BinaryTree α) :
    (run entry empty combineRun t).2 =
      entry * (2 * t.numNodes + 1) + k * t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      rw [run_node_cost, hcost l a r, ihl, ihr]
      simp only [BinaryTree.numNodes]
      ring

/-- One fixed bound must hold on all reached child summaries in the family.
A size-dependent choice of `K` alone does not give a uniform linear bound. -/
theorem run_cost_le (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (K : Nat)
    (hcost : ∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
      (combineRun (run entry empty combineRun l).1 a
        (run entry empty combineRun r).1).2 ≤ K) (t : BinaryTree α) :
    (run entry empty combineRun t).2 ≤
      entry * (2 * t.numNodes + 1) + K * t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      calc
        (run entry empty combineRun (.node a l r)).2 =
            ((run entry empty combineRun l).2 +
              ((run entry empty combineRun r).2 +
                (combineRun (run entry empty combineRun l).1 a
                  (run entry empty combineRun r).1).2)) + entry :=
          run_node_cost entry empty combineRun a l r
        _ ≤ (entry * (2 * l.numNodes + 1) + K * l.numNodes) +
            ((entry * (2 * r.numNodes + 1) + K * r.numNodes) + K) + entry :=
          Nat.add_le_add_right (Nat.add_le_add ihl
            (Nat.add_le_add ihr (hcost l a r))) entry
        _ = entry * (2 * (.node a l r).numNodes + 1) +
            K * (.node a l r).numNodes := by
          simp only [BinaryTree.numNodes]
          ring

end Resources.TreeFold

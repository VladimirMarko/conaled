import Applications.Trees.CompletenessCache
import Applications.Resources.TreeCache
import Examples.TreeBasicObservations

/-! Connected Boolean completeness and cached-summary clients.
Valid annotations reflect the independent shape predicate. A locally correct
root can still depend on a forged descendant. The measured node application
declares a callback tariff separately from its three local access charges;
it makes no machine-time claim about natural arithmetic or comparison.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeCompleteness
open Trees Trees.CompletenessCache
universe u
variable {α : Type u}

theorem empty_label_summary :
    Completeness.summary (.nil : BinaryTree Empty) = (true, 0) :=
  Completeness.summary_nil

theorem empty_label_check : Completeness.check (.nil : BinaryTree Empty) = true :=
  (Completeness.check_correct _).mpr complete_nil

theorem complete_sample_checked :
    Completeness.check TreeBasicObservationsExamples.sample = true :=
  (Completeness.check_correct _).mpr TreeBasicObservationsExamples.sample_complete

theorem complete_sample_summary :
    Completeness.summary TreeBasicObservationsExamples.sample = (true, 2) := by
  apply Prod.ext
  · exact complete_sample_checked
  · exact (Completeness.summary_height _).trans rfl

/-- Almost completeness does not suffice for the perfect-tree checker. -/
theorem incomplete_sample_checked :
    Completeness.check TreeBasicObservationsExamples.almostEnvelope = false := by
  cases h : Completeness.check TreeBasicObservationsExamples.almostEnvelope with
  | false => rfl
  | true =>
      exact False.elim (TreeBasicObservationsExamples.almostEnvelope_not_complete
        ((Completeness.check_correct _).mp h))

def sampleCached : BinaryTree (Nat × (Bool × Nat)) :=
  annotate TreeBasicObservationsExamples.sample

theorem sampleCached_valid : invarCh sampleCached :=
  annotate_valid TreeBasicObservationsExamples.sample

theorem sampleCached_erases : Cached.erase sampleCached = TreeBasicObservationsExamples.sample :=
  erase_annotate TreeBasicObservationsExamples.sample

theorem sampleCached_reads : ch sampleCached = (true, 2) :=
  (ch_annotate TreeBasicObservationsExamples.sample).trans complete_sample_summary

theorem sampleCached_shape_contract :
    ((ch sampleCached).1 = true ↔ Complete (Cached.erase sampleCached)) ∧
      (ch sampleCached).2 = (Cached.erase sampleCached).height :=
  ⟨ch_complete sampleCached sampleCached_valid, ch_height sampleCached sampleCached_valid⟩

/-- The height is correct here, but the forged root flag is false. -/
def forgedRoot : BinaryTree (Nat × (Bool × Nat)) := .node (4, (false, 1)) .nil .nil

theorem forged_root_complete : Complete (Cached.erase forgedRoot) :=
  ⟨rfl, complete_nil, complete_nil⟩

theorem forged_root_invalid : ¬ invarCh forgedRoot := by
  intro h
  have hflag := (ch_complete forgedRoot h).mpr forged_root_complete
  change false = true at hflag
  cases hflag

theorem forged_root_boundary :
    ch forgedRoot = (false, 1) ∧ Complete (Cached.erase forgedRoot) ∧ ¬ invarCh forgedRoot :=
  ⟨rfl, forged_root_complete, forged_root_invalid⟩

/-- This child's completeness flag is correct, but its stored height is not. -/
def forgedLeaf : BinaryTree (Nat × (Bool × Nat)) := .node (7, (true, 0)) .nil .nil

theorem forged_leaf_invalid : ¬ invarCh forgedLeaf := by
  intro h
  have hheight := ch_height forgedLeaf h
  change (0 : Nat) = 1 at hheight
  cases hheight

def forgedParent : BinaryTree (Nat × (Bool × Nat)) := nodeCh forgedLeaf 9 .nil

/-- The new root satisfies its local equation even with an invalid child. -/
theorem forged_parent_local_root :
    ch forgedParent = Completeness.combine (ch forgedLeaf) 9
      (ch (.nil : BinaryTree (Nat × (Bool × Nat)))) :=
  ch_nodeCh forgedLeaf 9 .nil

theorem forged_parent_invalid : ¬ invarCh forgedParent := by
  intro h
  exact forged_leaf_invalid ((nodeCh_valid_iff forgedLeaf 9 .nil).mp h).1

theorem forged_parent_incomplete : ¬ Complete (Cached.erase forgedParent) := by
  intro h
  have hheight : (1 : Nat) = 0 := h.1
  cases hheight

/-- A correct root computation cannot repair the forged descendant it reads. -/
theorem forged_descendant_boundary :
    (ch forgedParent).1 = true ∧ ¬ Complete (Cached.erase forgedParent) ∧
      (ch forgedParent).2 ≠ (Cached.erase forgedParent).height ∧ ¬ invarCh forgedParent :=
  ⟨rfl, forged_parent_incomplete, by decide, forged_parent_invalid⟩

theorem reader_needs_validity :
    ¬ ((ch forgedParent).1 = true ↔ Complete (Cached.erase forgedParent)) := by
  intro h
  exact forged_parent_incomplete (h.mp rfl)

/-- A declared source-model callback charge, separate from local read overhead. -/
def combineRun (charge : Nat) (left : Bool × Nat) (a : α) (right : Bool × Nat) :
    Resources.Measured (Bool × Nat) Nat :=
  (Completeness.combine left a right, charge)

def localNodeRun (charge : Nat) (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    Resources.Measured (BinaryTree (α × (Bool × Nat))) Nat :=
  Resources.TreeCache.nodeRun Completeness.empty (combineRun charge) l a r

theorem local_node_value (charge : Nat) (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    (localNodeRun charge l a r).1 = nodeCh l a r :=
  Resources.TreeCache.nodeRun_value Completeness.empty Completeness.combine
    (combineRun charge) l a r rfl

theorem local_node_cost (charge : Nat) (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    (localNodeRun charge l a r).2 = charge + 3 :=
  Resources.TreeCache.nodeRun_cost Completeness.empty (combineRun charge) l a r

theorem local_node_valid (charge : Nat) (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) (hl : invarCh l) (hr : invarCh r) :
    invarCh (localNodeRun charge l a r).1 :=
  Resources.TreeCache.nodeRun_valid Completeness.empty Completeness.combine
    (combineRun charge) l a r hl hr rfl

theorem measured_sample :
    (localNodeRun 1 (nodeCh .nil 3 .nil) 9 (nodeCh .nil 7 .nil)).1 = sampleCached ∧
      (localNodeRun 1 (nodeCh .nil 3 .nil) 9 (nodeCh .nil 7 .nil)).2 = 4 ∧
      invarCh (localNodeRun 1 (nodeCh .nil 3 .nil) 9 (nodeCh .nil 7 .nil)).1 :=
  ⟨(local_node_value 1 _ _ _).trans rfl, local_node_cost 1 _ _ _,
    local_node_valid 1 _ _ _ (nodeCh_valid .nil 3 .nil invarCh_nil invarCh_nil)
      (nodeCh_valid .nil 7 .nil invarCh_nil invarCh_nil)⟩

end Examples.TreeCompleteness

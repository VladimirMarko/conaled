import Applications.Trees.Completeness
import Applications.Trees.Cached

/-! FDSA Exercise 4.10 as a specialization of the existing cached fold.
The source names ch/nodeCh/invarCh respectively mean the local reader,
local smart constructor and all-node invariant. A full annotation pass is
separate. Boolean reflection and structural height concern erased keys.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.CompletenessCache
universe u
variable {α : Type u}

def ch (t : BinaryTree (α × (Bool × Nat))) : Bool × Nat :=
  Cached.read Completeness.empty t

def nodeCh (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) : BinaryTree (α × (Bool × Nat)) :=
  Cached.smartNode Completeness.empty Completeness.combine l a r

def Valid (t : BinaryTree (α × (Bool × Nat))) : Prop :=
  Cached.Valid Completeness.empty Completeness.combine t

@[simp] theorem ch_nil : ch (.nil : BinaryTree (α × (Bool × Nat))) = Completeness.empty :=
  rfl

@[simp] theorem valid_nil : Valid (.nil : BinaryTree (α × (Bool × Nat))) :=
  Cached.valid_nil Completeness.empty Completeness.combine

theorem ch_nodeCh (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    ch (nodeCh l a r) = Completeness.combine (ch l) a (ch r) :=
  Cached.read_smartNode Completeness.empty Completeness.combine l a r

theorem erase_nodeCh (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    Cached.erase (nodeCh l a r) = .node a (Cached.erase l) (Cached.erase r) :=
  Cached.erase_smartNode Completeness.empty Completeness.combine l a r

/-- Local reconstruction repairs the root only; both children must be valid. -/
theorem nodeCh_valid_iff (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) :
    Valid (nodeCh l a r) ↔ Valid l ∧ Valid r :=
  Cached.smartNode_valid_iff Completeness.empty Completeness.combine l a r

theorem nodeCh_valid (l : BinaryTree (α × (Bool × Nat))) (a : α)
    (r : BinaryTree (α × (Bool × Nat))) (hl : Valid l) (hr : Valid r) :
    Valid (nodeCh l a r) := (nodeCh_valid_iff l a r).mpr ⟨hl, hr⟩

theorem ch_eq_summary (t : BinaryTree (α × (Bool × Nat))) (ht : Valid t) :
    ch t = Completeness.summary (Cached.erase t) :=
  Cached.read_eq_fold Completeness.empty Completeness.combine t ht

theorem ch_height (t : BinaryTree (α × (Bool × Nat))) (ht : Valid t) :
    (ch t).2 = (Cached.erase t).height :=
  (congrArg Prod.snd (ch_eq_summary t ht)).trans (Completeness.summary_height _)

theorem ch_complete (t : BinaryTree (α × (Bool × Nat))) (ht : Valid t) :
    (ch t).1 = true ↔ Trees.Complete (Cached.erase t) := by
  rw [ch_eq_summary t ht]
  exact Completeness.summary_complete _

/-- Erasing annotations preserves structural height. -/
theorem ch_height_tree (t : BinaryTree (α × (Bool × Nat))) (ht : Valid t) :
    (ch t).2 = t.height := (ch_height t ht).trans (Cached.height_erase t)

/-- Completeness depends on shape, so annotation erasure preserves it too. -/
theorem ch_complete_tree (t : BinaryTree (α × (Bool × Nat))) (ht : Valid t) :
    (ch t).1 = true ↔ Trees.Complete t :=
  (ch_complete t ht).trans (Trees.complete_map Prod.fst t)

def annotate (t : BinaryTree α) : BinaryTree (α × (Bool × Nat)) :=
  Cached.annotate Completeness.empty Completeness.combine t

theorem annotate_valid (t : BinaryTree α) : Valid (annotate t) :=
  Cached.annotate_valid Completeness.empty Completeness.combine t

theorem erase_annotate (t : BinaryTree α) : Cached.erase (annotate t) = t :=
  Cached.erase_annotate Completeness.empty Completeness.combine t

theorem ch_annotate (t : BinaryTree α) : ch (annotate t) = Completeness.summary t :=
  Cached.read_annotate Completeness.empty Completeness.combine t

end Trees.CompletenessCache

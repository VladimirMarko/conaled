import Applications.Search.OrderedTree.Observations
import Examples.OrderedTree

/-! Connected clients of canonical tree observations and ordered-set laws.
The same set specification supports mixed insertion implementations. Strict
key order, raw observations, validity and comparison work remain separate.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeSearchObservationExamples
open Search Search.OrderedTree
universe u v
variable {α : Type u} {β : Type v}

/-- Compose the existing insertion squares, using baseline then candidate. -/
def mixedInsertSquare [LinearOrder α] (x y : α) :
    Relational.RelSquare (AbstractSet.representation (Trees.setTree (α := α)) Ordered)
      (AbstractSet.representation (Trees.setTree (α := α)) Ordered) :=
  Relational.compose (candidateSetLaws.insertSquare y) (baselineSetLaws.insertSquare x)

theorem mixed_insert_contract [LinearOrder α] (x y : α) {t : BinaryTree α}
    (ordered : Ordered t) :
    Ordered (insertCandidate y (insert x t)) ∧
      ∀ z, z ∈ Trees.setTree (insertCandidate y (insert x t)) ↔
        z = y ∨ z = x ∨ z ∈ Trees.setTree t :=
  (mixedInsertSquare x y).preserves ⟨ordered, fun _ => Iff.rfl⟩

/-- Both actual insertion words have the same set, including repeated keys. -/
theorem insertion_words_same_set [LinearOrder α] (xs : List α) :
    Trees.setTree (AbstractSet.insertMany baselineOps xs baselineOps.empty) =
      Trees.setTree (AbstractSet.insertMany candidateOps xs candidateOps.empty) := by
  rw [baselineSetLaws.insertMany_observe xs baselineSetLaws.empty_valid,
    candidateSetLaws.insertMany_observe xs candidateSetLaws.empty_valid]
  rfl

theorem repeated_word_membership (x : Nat) :
    (baselineOps : AbstractSet.Ops Nat (BinaryTree Nat)).member x
        (AbstractSet.insertMany baselineOps [3, 1, 3, 2] baselineOps.empty) = true ↔
      (candidateOps : AbstractSet.Ops Nat (BinaryTree Nat)).member x
        (AbstractSet.insertMany candidateOps [3, 1, 3, 2] candidateOps.empty) = true :=
  (baselineSetLaws.member_from_empty [3, 1, 3, 2] x).trans
    (candidateSetLaws.member_from_empty [3, 1, 3, 2] x).symm

theorem repeated_word_contains_two :
    2 ∈ Trees.setTree
      (AbstractSet.insertMany candidateOps [3, 1, 3, 2] candidateOps.empty) := by
  have valid := candidateSetLaws.insertMany_valid [3, 1, 3, 2] candidateSetLaws.empty_valid
  apply (candidateSetLaws.member 2 _ valid).mp
  exact (candidateSetLaws.member_from_empty [3, 1, 3, 2] 2).mpr (by simp)

theorem mixed_duplicate_contract :
    Ordered (insertCandidate 1 (insert 4 Examples.OrderedTree.sample)) ∧
      ∀ z, z ∈ Trees.setTree (insertCandidate 1 (insert 4 Examples.OrderedTree.sample)) ↔
        z = 1 ∨ z = 4 ∨ z ∈ Trees.setTree Examples.OrderedTree.sample :=
  mixed_insert_contract 4 1 Examples.OrderedTree.sample_ordered

/-- Empty labels need no inhabitant, order or equality decision. -/
theorem empty_label_observations :
    entries (.nil : BinaryTree Empty) = [] ∧
      Trees.setTree (.nil : BinaryTree Empty) = ∅ ∧
      All (fun _ : Empty => False) .nil :=
  ⟨entries_nil, Trees.setTree_nil, trivial⟩

/-- The existing bad descendant violates order, but raw membership still agrees. -/
theorem unordered_raw_observations :
    ¬ Ordered Examples.OrderedTree.badDescendant ∧
      (Contains 12 Examples.OrderedTree.badDescendant ↔
        12 ∈ Trees.setTree Examples.OrderedTree.badDescendant) ∧
      12 ∈ Trees.setTree Examples.OrderedTree.badDescendant := by
  refine ⟨Examples.OrderedTree.bad_descendant_not_ordered,
    contains_iff_mem_setTree _ _, ?_⟩
  apply (contains_iff_mem_setTree _ _).mp
  simp [Examples.OrderedTree.badDescendant, Contains]

theorem unordered_all_observation :
    ∀ x, x ∈ Trees.setTree Examples.OrderedTree.badDescendant → x ≤ 12 := by
  apply (all_iff_mem_setTree (fun x => x ≤ 12) _).mp
  simp [Examples.OrderedTree.badDescendant, All]

/-- This connects semantic agreement to the already checked unequal tariffs. -/
theorem same_members_different_work :
    (memberCandidate 4 Examples.OrderedTree.sample = true ↔
      member 4 Examples.OrderedTree.sample = true) ∧
      (memberRun 4 Examples.OrderedTree.sample).2 = 4 ∧
      (memberCandidateRun 4 none Examples.OrderedTree.sample).2 = 3 :=
  ⟨Examples.OrderedTree.sample_members_agree 4,
    Examples.OrderedTree.absent_comparison_counts⟩

/-- No order or equality decision on the payload type is requested. -/
def keyedTree (a b c : β) : BinaryTree (Nat × β) :=
  .node (2, b) (.node (1, a) .nil .nil) (.node (3, c) .nil .nil)

theorem keyed_tree_ordered (a b c : β) : OrderedBy Prod.fst (keyedTree a b c) := by
  apply (orderedBy_iff_inorder_pairwise Prod.fst _).mpr
  simp [keyedTree, Trees.inorder_node, Trees.inorder_nil]

theorem function_payloads_ordered :
    OrderedBy Prod.fst (keyedTree (fun n : Nat => n) (fun n => n + 1) (fun n => n * n)) :=
  keyed_tree_ordered _ _ _

def repeatedKeyTree (a b : β) : BinaryTree (Nat × β) :=
  .node (2, b) (.node (2, a) .nil .nil) .nil

/-- Nondecreasing keys permit a duplicate that the strict BST contract rejects. -/
theorem repeated_keys_not_strict (a b : β) :
    (Trees.inorder (repeatedKeyTree a b)).Pairwise (fun x y => x.1 ≤ y.1) ∧
      ¬ OrderedBy Prod.fst (repeatedKeyTree a b) := by
  rw [orderedBy_iff_inorder_pairwise]
  simp [repeatedKeyTree, Trees.inorder_node, Trees.inorder_nil]

namespace Nontransitive

inductive Label where
  | low | middle | high

def Step : Label → Label → Prop
  | .low, .middle => True
  | .middle, .high => True
  | _, _ => False

instance : LT Label := ⟨Step⟩

def tree : BinaryTree Label :=
  .node .middle (.node .low .nil .nil) (.node .high .nil .nil)

/-- Root/descendant checks do not compare the left child with the right child.
Transitivity is needed to infer that cross-subtree comparison. -/
theorem forward_requires_transitivity :
    Ordered tree ∧ ¬ (Trees.inorder tree).Pairwise (· < ·) := by
  change Ordered tree ∧ ¬ (Trees.inorder tree).Pairwise Step
  simp [tree, Ordered, OrderedBy, All, Trees.inorder_node, Trees.inorder_nil, Step,
    show (fun x y : Label => x < y) = Step from rfl]

end Nontransitive

namespace ValidOnly

/-- Some false and Some true are the empty and occupied singleton set states. -/
def ops : AbstractSet.Ops Unit (Option Bool) where
  empty := some false
  insert _ _ := some true
  member _ s := s.getD false

def Valid : Option Bool → Prop
  | none => False
  | some _ => True

def Observe (s : Option Bool) (_ : Unit) : Prop := s = some true

/-- On invalid None this observer deliberately differs from the original. -/
def Observe' (s : Option Bool) (_ : Unit) : Prop := s ≠ some false

theorem laws : AbstractSet.Laws ops Observe Valid where
  empty_valid := trivial
  empty _ := by simp [ops, Observe]
  insert_valid _ _ _ := trivial
  insert x s _ y := by
    cases x
    cases y
    simp [ops, Observe, AbstractSet.add]
  member x s valid := by
    cases s with
    | none => exact False.elim valid
    | some b => cases b <;> simp [ops, Observe]

theorem agree_on_valid (s : Option Bool) (valid : Valid s) (x : Unit) :
    Observe s x ↔ Observe' s x := by
  cases s with
  | none => exact False.elim valid
  | some b => cases b <;> simp [Observe, Observe']

theorem transported_laws : AbstractSet.Laws ops Observe' Valid :=
  laws.congr_observe agree_on_valid

theorem observers_differ_at_invalid :
    ¬ Valid none ∧ ¬ Observe none () ∧ Observe' none () := by
  simp [Valid, Observe, Observe']

/-- The transported member contract cannot silently discard its validity premise. -/
theorem invalid_member_contract_fails :
    ¬ (ops.member () none = true ↔ Observe' none ()) := by
  simp [ops, Observe']

theorem repeated_insertion_member :
    ops.member () (AbstractSet.insertMany ops [(), ()] ops.empty) = true :=
  (transported_laws.member_from_empty [(), ()] ()).mpr (by simp)

end ValidOnly
end TreeSearchObservationExamples

import Applications.Search.OrderedTree.Interface
import Applications.Search.OrderedTree.Contents
import Applications.Search.OrderedTree.Comparison

/-!
# Checked ordered-set clients and comparison distinctions

The tree with root2 and children1,3 is a finite instance of every public set
law. Searching for absent4 uses four baseline comparisons and three candidate
comparisons. Duplicate insertion aborts before rebuilding values; a separate
cell-graph realization is responsible for the stronger allocation conclusion.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.OrderedTree
open Search.OrderedTree

def sample : BinaryTree Nat := .node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)

theorem sample_ordered : Ordered sample := by
  simp [sample, Ordered, OrderedBy, All]

theorem sample_contains_one : Contains 1 sample := by simp [sample, Contains]

theorem sample_finite_contents :
    ∃ xs : List Nat, xs.Nodup ∧ xs.length = 3 ∧ ∀ x, Contains x sample ↔ x ∈ xs :=
  finite_contents sample_ordered

theorem sample_member_one : member 1 sample = true :=
  (member_correct sample_ordered 1).mpr sample_contains_one

theorem sample_candidate_member_one : memberCandidate 1 sample = true :=
  (memberCandidate_correct sample_ordered 1).mpr sample_contains_one

theorem empty_member_and_comparisons :
    memberCandidate 7 (.nil : BinaryTree Nat) = false ∧
      (memberCandidateRun 7 none (.nil : BinaryTree Nat)).2 = 0 := by
  constructor <;> rfl

theorem first_candidate_insertion :
    insertCandidate 7 (.nil : BinaryTree Nat) = .node 7 .nil .nil := by
  rw [insertCandidate_eq_insert ordered_nil]
  rfl

theorem sample_members_agree (x : Nat) :
    memberCandidate x sample = true ↔ member x sample = true :=
  (memberCandidate_correct sample_ordered x).trans (member_correct sample_ordered x).symm

theorem insert_four_retains_one : Contains 1 (insert 4 sample) :=
  (contains_insert 4 1 sample).mpr (Or.inr sample_contains_one)

theorem insert_four_present : Contains 4 (insert 4 sample) :=
  (contains_insert 4 4 sample).mpr (Or.inl rfl)

theorem insert_four_ordered : Ordered (insert 4 sample) := ordered_insert sample_ordered 4

theorem duplicate_abort : (insertAbortRun 1 sample).1 = none :=
  (insertAbortRun_none_iff 1 sample).mpr sample_member_one

theorem duplicate_outer_handler : insertAbort 1 sample = sample := by
  rw [insertAbort_eq_insert, insert_of_member sample_member_one]

theorem duplicate_candidate_abort : (insertCandidateRun 1 none sample).1 = none :=
  (insertCandidateRun_none_iff sample_ordered (show LowerBound none sample from trivial) 1).mpr
    (Or.inl sample_contains_one)

theorem duplicate_candidate_outer_handler : insertCandidate 1 sample = sample := by
  rw [insertCandidate_eq_insert sample_ordered, insert_of_member sample_member_one]

theorem absent_comparison_counts :
    (memberRun 4 sample).2 = 4 ∧ (memberCandidateRun 4 none sample).2 = 3 := by
  constructor <;> rfl

theorem candidate_bound_instantiated : (memberCandidateRun 4 none sample).2 ≤ 3 := by
  exact memberCandidateRun_bound 4 none sample

theorem combined_insert_four :
    insertCandidate 4 sample =
      .node 2 (.node 1 .nil .nil) (.node 3 .nil (.node 4 .nil .nil)) := by
  rw [insertCandidate_eq_insert sample_ordered]
  rfl

theorem combined_insert_four_contract :
    Ordered (insertCandidate 4 sample) ∧
      (∀ z, Contains z (insertCandidate 4 sample) ↔ z = 4 ∨ Contains z sample) ∧
      (insertCandidateRun 4 none sample).2 ≤ 3 :=
  insertCandidate_correct sample_ordered 4

/-- A locally plausible child root does not suffice:12 lies in10's left subtree. -/
def badDescendant : BinaryTree Nat :=
  .node 10 (.node 5 .nil (.node 12 .nil .nil)) .nil

theorem bad_descendant_not_ordered : ¬ Ordered badDescendant := by
  intro ordered
  have bad : 12 < 10 := ordered.2.2.1.of_contains
    (show Contains 12 (.node 5 .nil (.node 12 .nil .nil)) from
      Or.inr (Or.inr (Or.inl rfl)))
  omega

/-- A client uses the generic set laws, including repeated insertion. -/
theorem insertion_word_membership (x : Nat) :
    (candidateOps : Search.AbstractSet.Ops Nat (BinaryTree Nat)).member x
      (Search.AbstractSet.insertMany candidateOps [3, 1, 3, 2] candidateOps.empty) = true ↔
        x ∈ [3, 1, 3, 2] :=
  Search.AbstractSet.Laws.member_from_empty candidateLaws [3, 1, 3, 2] x

theorem insertion_word_contains_two :
    (candidateOps : Search.AbstractSet.Ops Nat (BinaryTree Nat)).member 2
      (Search.AbstractSet.insertMany candidateOps [3, 1, 3, 2] candidateOps.empty) = true :=
  (insertion_word_membership 2).mpr (by simp)

/-- The comparison bound is sharp on ordered inputs, not only malformed trees. -/
theorem five_deep_bounds :
    Ordered (rightSpine 0 5) ∧ (rightSpine 0 5).height = 5 ∧
      (memberRun 5 (rightSpine 0 5)).2 = 10 ∧
      (memberCandidateRun 5 none (rightSpine 0 5)).2 = 6 ∧
      (insertCandidateRun 5 none (rightSpine 0 5)).2 = 6 :=
  comparison_bounds_attained 4

theorem five_deep_query_absent : ¬ Contains 5 (rightSpine 0 5) :=
  rightSpine_above_absent (by decide)

theorem five_deep_size : (rightSpine 0 5).numNodes = 5 := rightSpine_numNodes 0 5

end Examples.OrderedTree

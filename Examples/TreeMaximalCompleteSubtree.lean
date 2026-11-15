import Applications.Trees.MaximalCompleteSubtree

/-! Connected clients of the single-fold maximal-complete-subtree selector.
The expected outcomes are a whole height-two perfect tree, the strictly taller
right candidate of an incomplete input, nil at Empty, and the label-2 singleton
in an observable left tie against a distinct label-3 singleton. Correctness
and height bounds below consume the public selection and maximality laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeMaximalCompleteSubtreeExamples
open Trees Trees.MaximalCompleteSubtree

def completeInput : BinaryTree Nat :=
  .node 4 (.node 2 .nil .nil) (.node 6 .nil .nil)

theorem completeInput_complete : Complete completeInput := by
  simp [completeInput, complete_node, BinaryTree.height]

theorem completeInput_height : completeInput.height = 2 := rfl

/-- The whole complete input is returned, rather than a smaller descendant. -/
theorem complete_selected : select completeInput = completeInput :=
  select_of_complete completeInput completeInput_complete

theorem complete_selection_correct :
    Subtree completeInput completeInput ∧ Complete completeInput ∧
      ∀ s, Subtree s completeInput → Complete s → s.height ≤ 2 := by
  simpa only [complete_selected, completeInput_height] using correct completeInput

/-- Its best complete descendant is the singleton rooted at 2. -/
def tieLeft : BinaryTree Nat := .node 1 (.node 2 .nil .nil) .nil

theorem tieLeft_incomplete : ¬ Complete tieLeft := by
  simp [tieLeft, complete_node, BinaryTree.height]

theorem tieLeft_selected : select tieLeft = .node 2 .nil .nil := by
  have hs : Complete (BinaryTree.node 2 .nil .nil) := by simp [complete_node]
  change select (.node 1 (.node 2 .nil .nil) .nil) = _
  rw [select_node_of_not_complete 1 _ _ tieLeft_incomplete,
    select_nil, select_of_complete _ hs]
  rfl

def rightWinnerInput : BinaryTree Nat := .node 0 tieLeft completeInput

theorem rightWinnerInput_incomplete : ¬ Complete rightWinnerInput := by
  intro h
  exact tieLeft_incomplete ((complete_node 0 tieLeft completeInput).mp h).2.1

theorem right_candidate_taller :
    (select tieLeft).height < (select completeInput).height := by
  rw [tieLeft_selected, complete_selected, completeInput_height]
  decide

/-- The incomplete input selects the height-two right candidate over height one. -/
theorem right_winner_selected : select rightWinnerInput = completeInput := by
  change select (.node 0 tieLeft completeInput) = _
  rw [select_node_of_not_complete 0 _ _ rightWinnerInput_incomplete,
    tieLeft_selected, complete_selected, completeInput_height]
  rfl

theorem right_winner_correct :
    Subtree completeInput rightWinnerInput ∧ Complete completeInput ∧
      ∀ s, Subtree s rightWinnerInput → Complete s → s.height ≤ 2 := by
  simpa only [right_winner_selected, completeInput_height] using correct rightWinnerInput

def tieInput : BinaryTree Nat := .node 0 tieLeft (.node 3 .nil .nil)

theorem tieInput_incomplete : ¬ Complete tieInput := by
  intro h
  exact tieLeft_incomplete ((complete_node 0 tieLeft (.node 3 .nil .nil)).mp h).2.1

theorem tie_candidates_same_height :
    (select tieLeft).height = (select (.node 3 .nil .nil)).height := by
  have hs : Complete (BinaryTree.node 3 .nil .nil) := by simp [complete_node]
  rw [tieLeft_selected, select_of_complete _ hs]
  rfl

/-- Distinct Nat labels make the deterministic left tie visible in the result. -/
theorem tie_selects_two : select tieInput = .node 2 .nil .nil := by
  have hs : Complete (BinaryTree.node 3 .nil .nil) := by simp [complete_node]
  change select (.node 0 tieLeft (.node 3 .nil .nil)) = _
  rw [select_node_of_not_complete 0 _ _ tieInput_incomplete,
    tieLeft_selected, select_of_complete _ hs]
  rfl

theorem tie_does_not_select_three : select tieInput ≠ .node 3 .nil .nil := by
  rw [tie_selects_two]
  decide

theorem tie_selection_correct :
    Subtree (.node 2 .nil .nil) tieInput ∧ Complete (BinaryTree.node 2 .nil .nil) ∧
      ∀ s, Subtree s tieInput → Complete s → s.height ≤ 1 := by
  simpa only [tie_selects_two, BinaryTree.height, max_self, Nat.zero_add] using correct tieInput

/-- The empty label domain has a valid selected result without an inhabitant. -/
theorem empty_nil :
    select (.nil : BinaryTree Empty) = .nil ∧
      Subtree (.nil : BinaryTree Empty) .nil ∧ Complete (.nil : BinaryTree Empty) ∧
      ∀ s : BinaryTree Empty, Subtree s .nil → Complete s → s.height ≤ 0 := by
  refine ⟨select_nil, ?_⟩
  simpa only [select_nil, BinaryTree.height] using correct (.nil : BinaryTree Empty)

end TreeMaximalCompleteSubtreeExamples

import Applications.Search.SharedTree.OptimizedObservation
import Examples.OrderedTree

/-!
# Physical duplicate abort and retained branches

Three initial cells represent the ordered set1,2,3. Duplicate insertion of1
returns precisely that store and root with zero allocation. Inserting4 uses
three fresh cells and preserves the old left-child address0 and the old tree.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTreeOptimized
open Search.SharedTree

def leftCell : Store Nat × Root := allocate empty 1 none none
def rightCell : Store Nat × Root := allocate leftCell.1 3 none none
def initial : Store Nat × Root := allocate rightCell.1 2 leftCell.2 rightCell.2

theorem leftCell_represents :
    Represents leftCell.1.heap leftCell.2 (.node 1 .nil .nil) :=
  allocate_represents .nil .nil 1

theorem rightCell_represents :
    Represents rightCell.1.heap rightCell.2 (.node 3 .nil .nil) :=
  allocate_represents .nil .nil 3

theorem initial_represents : Represents initial.1.heap initial.2 OrderedTree.sample :=
  allocate_represents
    (leftCell_represents.mono (allocate_extends leftCell.1 3 none none))
    rightCell_represents 2

theorem duplicate_aborts_without_allocating :
    insertAbortRun initial.1 initial.2 1 = (some initial, (3, 2, 0)) :=
  insertAbortRun_duplicate initial_represents OrderedTree.sample_ordered
    OrderedTree.sample_contains_one

/-- The combined search reaches nil after the remembered match, yet allocates
no cells and invokes only the outer duplicate handler. -/
theorem combined_duplicate_preserves_exact_root :
    insertCandidateRun initial.1 initial.2 1 = (some initial, (3, 3, 0)) :=
  insertCandidateRun_duplicate initial_represents OrderedTree.sample_ordered
    OrderedTree.sample_contains_one

/-- Invalid input remains a failure rather than being mistaken for a duplicate. -/
theorem invalid_root_fails :
    insertCandidateRun (empty : Store Nat) (some 0) 1 = (none, (0, 0, 0)) := rfl

theorem initial_left_address : follow initial.1.heap [.left] initial.2 = some (some 0) := rfl

theorem insert_four_retains_old_tree_and_left_address :
    ∃ out, insertCandidateRun initial.1 initial.2 4 = (some out, (3, 3, 3)) ∧
      Represents out.1.heap initial.2 OrderedTree.sample ∧
      Represents out.1.heap out.2 (Search.OrderedTree.insert 4 OrderedTree.sample) ∧
      out.1.next = 6 ∧ follow out.1.heap [.left] out.2 = some (some 0) := by
  obtain ⟨out, run, extension, rep, kept, count, offPath, _⟩ :=
    insertCandidateRun_retention initial_represents initial_represents
      OrderedTree.sample_ordered 4
  refine ⟨out, run, kept, rep, count, ?_⟩
  have different : Diverges (candidatePath 4 OrderedTree.sample) [.left] := by
    simp [candidatePath, OrderedTree.sample, Diverges]
  rw [offPath [.left] different]
  exact follow_mono extension initial_left_address

theorem combined_comparison_bound :
    (insertCandidateRun initial.1 initial.2 4).2.1 ≤ 3 := by
  rw [insertCandidateRun_profile initial_represents]
  exact (candidateProfile_bounds 4 none OrderedTree.sample).1

/-- The composed contract connects allocation to the independently defined
root-value observer, including the initially empty input. -/
theorem first_insert_root_observation :
    (insertCandidateRun (empty : Store Nat) none 7).1.map rootValue = some (some 7) :=
  insertCandidateRootValue_correct Represents.nil 7

theorem duplicate_root_observation :
    (insertAbortRun initial.1 initial.2 1).1.map rootValue = some (some 2) :=
  insertAbortRootValue_correct initial_represents 1

end Examples.SharedTreeOptimized

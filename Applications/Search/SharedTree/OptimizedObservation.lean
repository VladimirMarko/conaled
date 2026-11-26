import Applications.Search.SharedTree.Optimized
import Applications.Search.SharedTree.Observation

/-!
# Relational clients of aborting shared insertion

The squares preserve the operational tree value for every represented input.
Their independent set interpretation requires the ordering laws from the pure
realization. Optional results and optional root observations remain distinct.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type} [LinearOrder α]

def insertAbortSquare (x : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) where
  impl state := (insertAbortRun state.1 state.2 x).1
  spec tree := some (OrderedTree.insertAbort x tree)
  preserves := by
    intro state tree h
    obtain ⟨out, run, rep⟩ := insertAbortRun_value h x
    rw [run]
    exact rep

def insertCandidateSquare (x : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) where
  impl state := (insertCandidateRun state.1 state.2 x).1
  spec tree := some (OrderedTree.insertCandidate x tree)
  preserves := by
    intro state tree h
    obtain ⟨out, run, rep⟩ := insertCandidateRun_value h x
    rw [run]
    exact rep

def insertAbortRootValueSquare (x : α) :
    Relational.RelSquare (representation α)
      ⟨Option (Option α), Option (Option α), Eq⟩ :=
  Relational.compose (optionalRootValueSquare α) (insertAbortSquare x)

def insertCandidateRootValueSquare (x : α) :
    Relational.RelSquare (representation α)
      ⟨Option (Option α), Option (Option α), Eq⟩ :=
  Relational.compose (optionalRootValueSquare α) (insertCandidateSquare x)

theorem insertAbortRun_rootValue_correct {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    (insertAbortRun s root x).1.map rootValue =
      some (treeValue (OrderedTree.insertAbort x t)) :=
  (insertAbortRootValueSquare x).preserves (r := (s, root)) (s := t) h

theorem insertCandidateRun_rootValue_correct {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    (insertCandidateRun s root x).1.map rootValue =
      some (treeValue (OrderedTree.insertCandidate x t)) :=
  (insertCandidateRootValueSquare x).preserves (r := (s, root)) (s := t) h

end Search.SharedTree

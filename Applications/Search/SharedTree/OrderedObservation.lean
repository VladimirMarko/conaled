import Applications.Search.SharedTree.Ordered
import Applications.Search.SharedTree.Observation

/-!
# Ordered insertion as a relational computation

The heap traversal refines the independent tree operation even for an unordered
tree. The separate ordered-set corollary requires the strict search invariant.
Optional observations distinguish a failed traversal from a successful empty
tree; composing them does not silently discard failure.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type} [LinearOrder α]

def insertSquare (x : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) where
  impl state := (insertRun state.1 state.2 x).1
  spec tree := some (OrderedTree.insert x tree)
  preserves := by
    intro state tree h
    obtain ⟨out, run, _, rep, _, _⟩ := insertRun_correct h x
    change (optionalRepresentation α).Rel (insertRun state.1 state.2 x).1 _
    rw [run]
    exact rep

def optionalRootValueSquare (α : Type) :
    Relational.RelSquare (optionalRepresentation α)
      ⟨Option (Option α), Option (Option α), Eq⟩ where
  impl state := state.map rootValue
  spec tree := tree.map treeValue
  preserves := by
    intro state tree h
    cases state with
    | none =>
        cases tree with
        | none => rfl
        | some tree => exact False.elim h
    | some state =>
        cases tree with
        | none => exact False.elim h
        | some tree =>
            exact congrArg some ((rootValueSquare α).preserves h)

def insertRootValueSquare (x : α) :
    Relational.RelSquare (representation α)
      ⟨Option (Option α), Option (Option α), Eq⟩ :=
  Relational.compose (optionalRootValueSquare α) (insertSquare x)

theorem insertRootValue_correct {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    (insertRun s root x).1.map rootValue = some (treeValue (OrderedTree.insert x t)) :=
  (insertRootValueSquare x).preserves (r := (s, root)) (s := t) h

/-- Contents and ordering are properties of the independent observed value;
the execution and retained old version are obtained from the physical theorem. -/
theorem insertRun_ordered {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) (x : α) :
    ∃ out, insertRun s root x = (some out, insertProfile x t) ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      Represents out.1.heap root t ∧
      OrderedTree.Ordered (OrderedTree.insert x t) ∧
      (∀ y, OrderedTree.Contains y (OrderedTree.insert x t) ↔
        y = x ∨ OrderedTree.Contains y t) := by
  obtain ⟨out, run, extension, rep, _, _⟩ := insertRun_correct h x
  exact ⟨out, run, rep, h.mono extension, OrderedTree.ordered_insert ordered x,
    fun y => OrderedTree.contains_insert x y t⟩

end Search.SharedTree

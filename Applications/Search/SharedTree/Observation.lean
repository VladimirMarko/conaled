import Applications.Search.SharedTree.Basic
import SquareKit.Relations

/-!
# Relational observations of shared trees

There is no total decoder for arbitrary root/store pairs. These adapters use
the existing relational-square interface and retain optional failure. The
two-child input has one common store; combining arbitrary separate stores is
not an operation supported by the allocator.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree

variable {α : Type}

def representation (α : Type) : Relational.RelRep :=
  ⟨Store α × Root, BinaryTree α,
    fun state tree => Represents state.1.heap state.2 tree⟩

def optionalRepresentation (α : Type) : Relational.RelRep where
  R := Option (Store α × Root)
  S := Option (BinaryTree α)
  Rel out value := match out, value with
    | none, none => True
    | some state, some tree => Represents state.1.heap state.2 tree
    | _, _ => False

def pairInput (α : Type) : Relational.RelRep where
  R := Store α × Root × Root
  S := BinaryTree α × BinaryTree α
  Rel input value := Represents input.1.heap input.2.1 value.1 ∧
    Represents input.1.heap input.2.2 value.2

def allocateSquare (x : α) :
    Relational.RelSquare (pairInput α) (representation α) where
  impl input := allocate input.1 x input.2.1 input.2.2
  spec value := .node x value.1 value.2
  preserves := by
    intro input value h
    exact allocate_represents h.1 h.2 x

def rootValue (state : Store α × Root) : Option α :=
  (read state.1 state.2).map fun c => c.1.1

def treeValue : BinaryTree α → Option α
  | .nil => none
  | .node x _ _ => some x

def rootValueSquare (α : Type) :
    Relational.RelSquare (representation α) ⟨Option α, Option α, Eq⟩ where
  impl := rootValue
  spec := treeValue
  preserves := by
    intro state tree h
    rcases state with ⟨s, root⟩
    change Represents s.heap root tree at h
    cases h with
    | nil => rfl
    | node lookup _ _ _ _ => simp [rootValue, read, treeValue, lookup]

/-- Lift root observation while distinguishing traversal failure from an empty tree. -/
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


/-- Compose allocation with the independently specified root-value observation. -/
def allocatedValueSquare (x : α) :
    Relational.RelSquare (pairInput α) ⟨Option α, Option α, Eq⟩ :=
  Relational.compose (rootValueSquare α) (allocateSquare x)

theorem rootValue_allocate {s : Store α} {l r : Root} {lt rt : BinaryTree α}
    (hl : Represents s.heap l lt) (hr : Represents s.heap r rt) (x : α) :
    rootValue (allocate s x l r) = some x :=
  (allocatedValueSquare x).preserves (r := (s, l, r)) (s := (lt, rt)) ⟨hl, hr⟩

end Search.SharedTree

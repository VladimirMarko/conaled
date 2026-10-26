import Applications.Resources.RandomAccess.CacheCosts
import Applications.Resources.Measured

/-! Actual recursive append and explicit pending-stack traversal on shared trees.
Provenance and statement review: `docs/research/adwh-tree-flattening.md`. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.TreeFlattening
open Bracketing
universe u
variable {α : Type u}

/-- Count the constructors inspected by a full tree traversal. -/
def nodes (t : Tree α) : Nat := (RandomAccessCosts.structuralSizeRun t).2

@[simp] theorem nodes_leaf (x : α) : nodes (.leaf x) = 1 := rfl
@[simp] theorem nodes_fork (l r : Tree α) :
    nodes (.fork l r) = 1 + nodes l + nodes r := by
  simp [nodes, RandomAccessCosts.structuralSizeRun]; omega

def pending : List (Tree α) → Nat
  | [] => 0
  | t :: ts => nodes t + pending ts

/-- Ordinary append, with one charge for each copied cell of its first list. -/
def appendWithCost : List α → List α → List α × Nat
  | [], ys => (ys, 0)
  | x :: xs, ys =>
      let rest := appendWithCost xs ys
      (x :: rest.1, rest.2 + 1)

theorem appendWithCost_exact (xs ys : List α) :
    appendWithCost xs ys = (xs ++ ys, xs.length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendWithCost, ih]

/-- The original recursive append traversal, retaining its actual result. -/
def fromTWithCost : Tree α → List α × Nat
  | .leaf x => ([x], 1)
  | .fork l r =>
      let left := fromTWithCost l
      let right := fromTWithCost r
      let joined := appendWithCost left.1 right.1
      (joined.1, left.2 + right.2 + joined.2 + 1)

theorem fromTWithCost_value (t : Tree α) : (fromTWithCost t).1 = fringeSpec t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr => simp [fromTWithCost, appendWithCost_exact, ihl, ihr, fringeSpec]

/-- The additional list cells copied by recursive append, over every node. -/
def copies : Tree α → Nat
  | .leaf _ => 0
  | .fork l r => copies l + copies r + (fringeSpec l).length

theorem fromTWithCost_count (t : Tree α) :
    (fromTWithCost t).2 = nodes t + copies t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr =>
    simp only [fromTWithCost, appendWithCost_exact, fromTWithCost_value,
      ihl, ihr, nodes_fork, copies]
    omega

/-- Answer 3.8's worklist algorithm, with its pending-tree measure explicit. -/
def fromTsWithCost : List (Tree α) → List α × Nat
  | [] => ([], 1)
  | .leaf x :: ts =>
      let rest := fromTsWithCost ts
      (x :: rest.1, rest.2 + 1)
  | .fork l r :: ts =>
      let rest := fromTsWithCost (l :: r :: ts)
      (rest.1, rest.2 + 1)
termination_by ts => pending ts
decreasing_by
  all_goals simp only [pending, nodes_leaf, nodes_fork]; omega

def fromTs (ts : List (Tree α)) : List α := (fromTsWithCost ts).1

theorem fromTsWithCost_exact (ts : List (Tree α)) :
    fromTsWithCost ts = (ts.flatMap fringeSpec, pending ts + 1) := by
  induction ts using (measure pending).wf.induction with
  | h ts ih =>
    cases ts with
    | nil => rw [fromTsWithCost]; rfl
    | cons t ts =>
      cases t with
      | leaf x =>
        have hlt : pending ts < pending (.leaf x :: ts) := by simp [pending, nodes_leaf]
        rw [fromTsWithCost, ih ts hlt]
        simp [List.flatMap_cons, fringeSpec, pending, nodes_leaf, Nat.add_comm]
      | fork l r =>
        have hlt : pending (l :: r :: ts) < pending (.fork l r :: ts) := by
          simp only [pending, nodes_fork]; omega
        rw [fromTsWithCost, ih (l :: r :: ts) hlt]
        simp [List.flatMap_cons, fringeSpec, pending, nodes_fork, List.append_assoc]
        omega

theorem fromTs_refinement (ts : List (Tree α)) :
    fromTs ts = ts.flatMap fringeSpec := by simp [fromTs, fromTsWithCost_exact]

theorem fromTs_singleton (t : Tree α) : fromTs [t] = fringeSpec t := by
  simp [fromTs_refinement]

theorem fromTs_suffix (ts us : List (Tree α)) :
    fromTs (ts ++ us) = fromTs ts ++ fromTs us := by
  simp [fromTs_refinement]

theorem pending_append (ts us : List (Tree α)) :
    pending (ts ++ us) = pending ts + pending us := by
  induction ts with
  | nil => simp [pending]
  | cons t ts ih => simp [pending, ih, Nat.add_assoc]

end Resources.TreeFlattening

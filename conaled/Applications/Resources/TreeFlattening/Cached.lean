import Applications.Resources.TreeFlattening.Core

/-! Source-facing cached-tree executions. Erasure simulates whole measured results;
these algorithms do not execute an erasure prepass or inspect cache values. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.TreeFlattening
open RandomAccess
universe u
variable {α : Type u}

def cachedFromTWithCost : Tree α → Measured (List α) Nat
  | .leaf x => ([x], 1)
  | .node _ l r =>
      let left := cachedFromTWithCost l
      let right := cachedFromTWithCost r
      let joined := appendWithCost left.1 right.1
      (joined.1, left.2 + right.2 + joined.2 + 1)

theorem cachedFromTWithCost_erasure (t : Tree α) :
    cachedFromTWithCost t = fromTWithCost (erase t) := by
  induction t with
  | leaf x => rfl
  | node n l r hl hr => simp [cachedFromTWithCost, erase, fromTWithCost, hl, hr]

def cachedFromTsWithCost : List (Tree α) → Measured (List α) Nat
  | [] => ([], 1)
  | .leaf x :: ts =>
      let rest := cachedFromTsWithCost ts
      (x :: rest.1, rest.2 + 1)
  | .node _ l r :: ts =>
      let rest := cachedFromTsWithCost (l :: r :: ts)
      (rest.1, rest.2 + 1)
termination_by ts => pending (ts.map erase)
decreasing_by
  all_goals simp only [List.map_cons, erase, pending, nodes_leaf, nodes_fork]; omega

theorem cachedFromTsWithCost_erasure (ts : List (Tree α)) :
    cachedFromTsWithCost ts = fromTsWithCost (ts.map erase) := by
  induction ts using (measure (fun (ts : List (Tree α)) => pending (ts.map erase))).wf.induction with
  | h ts ih =>
    cases ts with
    | nil => simp [cachedFromTsWithCost, fromTsWithCost]
    | cons t ts =>
      cases t with
      | leaf x =>
        have hlt : pending (ts.map erase) < pending ((Tree.leaf x :: ts).map erase) := by
          simp [pending, erase]
        rw [cachedFromTsWithCost, ih ts hlt]
        simp only [List.map_cons, erase, fromTsWithCost]
      | node n l r =>
        have hlt : pending ((l :: r :: ts).map erase) <
            pending ((Tree.node n l r :: ts).map erase) := by
          simp only [List.map_cons, erase, pending, nodes_fork]; omega
        rw [cachedFromTsWithCost, ih (l :: r :: ts) hlt]
        simp only [List.map_cons, erase, fromTsWithCost]

theorem cachedFromTWithCost_value (t : Tree α) :
    (cachedFromTWithCost t).1 = fromT t := by
  rw [cachedFromTWithCost_erasure, fromTWithCost_value, ← fromT_eq_fringe]

theorem cachedFromTsWithCost_exact (ts : List (Tree α)) :
    cachedFromTsWithCost ts = (ts.flatMap fromT, pending (ts.map erase) + 1) := by
  rw [cachedFromTsWithCost_erasure, fromTsWithCost_exact]
  simp only [List.flatMap_map, ← fromT_eq_fringe]

end Resources.TreeFlattening

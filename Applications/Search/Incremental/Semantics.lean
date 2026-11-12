import Applications.Search.RationalCost
import Applications.Dijkstra.Store
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Prod.Lex.Basic

/-! Finite positive rational graphs and their one-step distance equation.
The graph may change between repairs; no common denominator is fixed. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental

abbrev Cost := WithTop ℚ
abbrev Graph (n : Nat) := Fin n → Fin n → Cost
abbrev Labels (n : Nat) := Fin n → Cost
variable {n : Nat}

def Positive (w : Graph n) : Prop := ∀ u v, 0 < w u v

def Nonnegative (g : Labels n) : Prop := ∀ u, 0 ≤ g u

def predecessorMinimum (w : Graph n) (g : Labels n) (v : Fin n) : Cost :=
  Finset.univ.inf fun u => g u + w u v

def rhsValue (w : Graph n) (start : Fin n) (g : Labels n) (v : Fin n) : Cost :=
  if v = start then 0 else predecessorMinimum w g v

def Bellman (w : Graph n) (start : Fin n) (g : Labels n) : Prop :=
  ∀ v, g v = rhsValue w start g v

def ConsistentHeuristic (w : Graph n) (goal : Fin n) (h : Fin n → ℚ) : Prop :=
  (∀ v, 0 ≤ h v) ∧ h goal = 0 ∧
    ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost)

def adjacency (w : Graph n) : RationalCost.Graph (Fin n) := fun u =>
  (List.finRange n).map fun v => (v, w u v)

def DistanceResult (w : Graph n) (start goal : Fin n) (d : Cost) : Prop :=
  RationalCost.DistanceResult (adjacency w) (fun v => decide (v = goal)) start d

@[simp] theorem edge_iff (w : Graph n) (u v : Fin n) (d : ℚ) :
    RationalCost.Edge (adjacency w) u v d ↔ w u v = (d : Cost) := by
  simp [RationalCost.Edge, adjacency, Prod.mk.injEq]

@[simp] theorem rhsValue_start (w : Graph n) (start : Fin n) (g : Labels n) :
    rhsValue w start g start = 0 := by simp [rhsValue]

theorem predecessorMinimum_le (w : Graph n) (g : Labels n) (u v : Fin n) :
    predecessorMinimum w g v ≤ g u + w u v :=
  Finset.inf_le (Finset.mem_univ u)

theorem le_predecessorMinimum_iff (w : Graph n) (g : Labels n) (v : Fin n) (a : Cost) :
    a ≤ predecessorMinimum w g v ↔ ∀ u, a ≤ g u + w u v := by
  simp [predecessorMinimum, Finset.le_inf_iff]

theorem rhsValue_nonnegative {w : Graph n} (hw : Positive w) (start : Fin n)
    {g : Labels n} (hg : Nonnegative g) (v : Fin n) : 0 ≤ rhsValue w start g v := by
  unfold rhsValue
  split
  · exact le_rfl
  · exact (le_predecessorMinimum_iff w g v 0).mpr fun u => add_nonneg (hg u) (le_of_lt (hw u v))

end Search.Incremental

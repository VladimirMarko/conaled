import Applications.Bracketing.Interpretation
import Applications.DynamicProgramming.Knapsack

open Bracketing Bracketing.Recursive Bracketing.Cached
namespace Examples.Bracketing

def four : Input Nat := ⟨[1, 2, 3, 4], by decide⟩
def balanced : Tree Nat := .fork (.fork (.leaf 1) (.leaf 2)) (.fork (.leaf 3) (.leaf 4))

/-- Sequential work charges the total size of each merge. -/
theorem work_solution : (solveSquare (· + ·) (· + ·)).impl four = balanced := by
  have h := (solveSquare (α := Nat) (· + ·) (· + ·)).commutes four
  change (solveSquare (· + ·) (· + ·)).impl four = mctH (· + ·) (· + ·) _ _ at h
  apply h.trans
  change mctH (· + ·) (· + ·) [1, 2, 3, 4] _ = balanced
  decide +kernel

theorem work_optimum : balanced ∈ Optimization.minimizers
    {t | fringeSpec t = [1, 2, 3, 4]} (costH (· + ·) (· + ·)) := by
  rw [← work_solution]
  exact solveSquare_minimizer _ _ addition_monotone four

theorem work_cost : costH (· + ·) (· + ·) balanced = 8 := rfl

/-- Parallel child execution with unit fork charge minimizes depth. -/
theorem depth_solution : (solveSquare max (fun _ _ => 1)).impl four = balanced := by
  have h := (solveSquare (α := Nat) max (fun _ _ => 1)).commutes four
  change (solveSquare max (fun _ _ => 1)).impl four = mctH max (fun _ _ => 1) _ _ at h
  apply h.trans
  change mctH max (fun _ _ => 1) [1, 2, 3, 4] _ = balanced
  decide +kernel

theorem depth_optimum : balanced ∈ Optimization.minimizers
    {t | fringeSpec t = [1, 2, 3, 4]} (costH max (fun _ _ => 1)) := by
  rw [← depth_solution]
  exact solveSquare_minimizer _ _ parallel_max_monotone four

theorem depth_cost : costH max (fun _ _ => 1) balanced = 2 := rfl

/-- All-zero costs keep the first cut, recursively, rather than a balanced tree. -/
theorem tied_first_cut : _root_.Bracketing.Array.mct3Option (· + ·) (fun _ _ => 0) [1, 2, 3] =
    some (.fork (.leaf 1) (.fork (.leaf 2) (.leaf 3))) := by
  rw [_root_.Bracketing.Array.mct3Option_eq_some_mct2 _ _ _ (by decide), mct2_eq_mct]
  decide +kernel

theorem empty_request : _root_.Bracketing.Array.mct3Option max (fun _ _ => 1) ([] : List Nat) = none :=
  _root_.Bracketing.Array.mct3Option_nil _ _

theorem nonmonotone_not_optimum :
    mctH badH badCharge [(), (), (), ()] (by decide) ∉
      Optimization.minimizers {t | fringeSpec t = [(), (), (), ()]} (costH badH badCharge) := by
  intro h
  have hc := h.2 nonmonotone_failure.2.1
  change costH badH badCharge _ ≤ costH badH badCharge badCompetitor at hc
  rw [nonmonotone_failure.1, nonmonotone_failure.2.2] at hc
  omega

/-- An interpretation from ordered leaves to their count composes with tree
folding; concatenation order is retained before taking length. -/
theorem leaf_count_fusion (t : Tree Nat) :
    (t.fold (fun x => [x]) (· ++ ·)).length = t.fold (fun _ => 1) (· + ·) := by
  exact Tree.fold_fusion _ _ _ _ List.length (fun _ => rfl)
    (fun _ _ => List.length_append) t

theorem ordered_pair : balanced.fold (fun x => ([x], 1))
    (fun l r => (l.1 ++ r.1, l.2 + r.2)) = ([1, 2, 3, 4], 4) := by
  rw [Tree.fold_pair]
  rfl

end Examples.Bracketing

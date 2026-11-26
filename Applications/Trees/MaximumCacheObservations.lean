import Applications.Trees.MaximumCache
import Applications.Trees.BasicObservations
import Mathlib.Data.List.MinMax

/-! Ordered meaning of the raw maximum cache and its independent fold.
The shared operations remain Max-only. A linear order supplies the standard
optional-list-maximum laws used here, including both attainment and an upper
bound over the independently observed key set. No bottom or label inhabitant
is introduced, and the raw reader is not changed into a traversal.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.MaximumCache
universe u
variable {α : Type u} [LinearOrder α]

private theorem foldl_max_eq_elim (xs : List α) (a : α) :
    xs.foldl max a = xs.max?.elim a (max a) :=
  Option.some.inj ((List.max?_cons' (x := a) (xs := xs)).symm.trans
    (List.max?_cons (x := a) (xs := xs)))

/-- The exact inorder node algebra, using the standard optional maximum. -/
private theorem max?_append_cons (xs : List α) (a : α) (ys : List α) :
    (xs ++ a :: ys).max? = combine xs.max? a ys.max? := by
  cases xs with
  | nil =>
      simpa only [List.nil_append, List.max?_nil, combine, localMax, Option.elim_none]
        using (List.max?_cons (x := a) (xs := ys))
  | cons b bs =>
      rw [List.cons_append, List.max?_cons', List.foldl_append, List.foldl_cons]
      simp only [combine, localMax, List.max?_cons', Option.elim_some]
      rw [max_comm (bs.foldl max b) a, foldl_max_eq_elim]

/-- Observe the canonical inorder fold by `List.max?` using actual fold fusion. -/
theorem summary_eq_max?_inorder (t : BinaryTree α) :
    summary t = (Trees.inorder t).max? :=
  (Trees.fold_fusion ([] : List α) (fun l a r => l ++ (a :: r))
    (none : Option α) combine (fun xs => xs.max?) rfl
    (fun l a r => max?_append_cons l a r) t).symm

/-- The optional fold returns an attained greatest label, not merely a bound. -/
theorem summary_eq_some_iff (t : BinaryTree α) (m : α) :
    summary t = some m ↔ m ∈ Trees.setTree t ∧
      ∀ x ∈ Trees.setTree t, x ≤ m := by
  rw [summary_eq_max?_inorder, List.max?_eq_some_iff]
  simp only [Trees.mem_inorder_iff_mem_setTree]

/-- All-node raw validity connects the direct reader to the canonical key list. -/
theorem mx_eq_max?_inorder (t : BinaryTree (α × α)) (ht : Valid t) :
    mx t = (Trees.inorder (Trees.Cached.erase t)).max? := by
  rw [mx_eq_summary t ht, summary_eq_max?_inorder]

/-- A valid source cache returns exactly the greatest element of its key set.
The membership conjunct retains attainment and excludes an invented default. -/
theorem mx_eq_some_iff (t : BinaryTree (α × α)) (ht : Valid t) (m : α) :
    mx t = some m ↔ m ∈ Trees.setTree (Trees.Cached.erase t) ∧
      ∀ x ∈ Trees.setTree (Trees.Cached.erase t), x ≤ m := by
  rw [mx_eq_summary t ht, summary_eq_some_iff]

end Trees.MaximumCache

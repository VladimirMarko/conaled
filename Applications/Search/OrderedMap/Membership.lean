import Applications.Search.OrderedMap.Basic
import Applications.Search.OrderedTree.Observations
import Applications.Trees.Cached

/-! Equality-key membership in augmented trees ignores annotations.
The raw boolean reuses ordered-map lookup. Erasure connects that same path to
the existing ordered-set program; strict order is needed only to identify the
path answer with the independently observed whole-tree contents.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u v w
variable {κ : Type u} {ν : Type v} {μ : Type w}

section Comparison
variable [LT κ] [DecidableLT κ]

def containsKey (query : κ) (t : BinaryTree (κ × ν)) : Bool :=
  (lookup query t).isSome

@[simp] theorem containsKey_nil (query : κ) :
    containsKey query (.nil : BinaryTree (κ × ν)) = false := rfl

theorem containsKey_node (query key : κ) (value : ν) (l r : BinaryTree (κ × ν)) :
    containsKey query (.node (key, value) l r) =
      if query < key then containsKey query l
      else if key < query then containsKey query r else true := by
  by_cases qk : query < key
  · simp only [containsKey, lookup, ite_eq_left qk]
  · by_cases kq : key < query
    · simp only [containsKey, lookup, ite_eq_right qk, ite_eq_left kq]
    · simp only [containsKey, lookup, ite_eq_right qk, ite_eq_right kq,
        Option.isSome_some]

end Comparison

section LinearOrder
variable [LinearOrder κ]

/-- Raw path agreement: the tree need not be ordered or correctly annotated. -/
theorem containsKey_eq_member_erase (query : κ) (t : BinaryTree (κ × ν)) :
    containsKey query t = OrderedTree.member query (Trees.Cached.erase t) := by
  induction t with
  | nil => rfl
  | node binding l r ihl ihr =>
      rcases binding with ⟨key, value⟩
      by_cases qk : query < key
      · simpa only [containsKey, lookup, Trees.Cached.erase_node,
          OrderedTree.member, OrderedTree.memberRun, ite_eq_left qk] using ihl
      · by_cases kq : key < query
        · simpa only [containsKey, lookup, Trees.Cached.erase_node,
            OrderedTree.member, OrderedTree.memberRun, ite_eq_right qk,
            ite_eq_left kq] using ihr
        · simp only [containsKey, lookup, Trees.Cached.erase_node,
            OrderedTree.member, OrderedTree.memberRun, ite_eq_right qk,
            ite_eq_right kq, Option.isSome_some]

/-- Even different annotation carriers can have the same membership behavior. -/
theorem containsKey_congr_erase {left : BinaryTree (κ × ν)}
    {right : BinaryTree (κ × μ)} (same : Trees.Cached.erase left = Trees.Cached.erase right)
    (query : κ) : containsKey query left = containsKey query right := by
  rw [containsKey_eq_member_erase, containsKey_eq_member_erase, same]

theorem containsKey_eq_true_iff_mem_inorder {t : BinaryTree (κ × ν)}
    (ordered : OrderedTree.OrderedBy Prod.fst t) (query : κ) :
    containsKey query t = true ↔ query ∈ Trees.inorder (Trees.Cached.erase t) := by
  rw [containsKey_eq_member_erase]
  exact (OrderedTree.member_correct
    ((OrderedTree.orderedBy_iff_map Prod.fst t).mp ordered) query).trans
      (OrderedTree.contains_iff_mem_entries query (Trees.Cached.erase t))

theorem containsKey_eq_true_iff_mem_setTree {t : BinaryTree (κ × ν)}
    (ordered : OrderedTree.OrderedBy Prod.fst t) (query : κ) :
    containsKey query t = true ↔ query ∈ Trees.setTree (Trees.Cached.erase t) :=
  (containsKey_eq_true_iff_mem_inorder ordered query).trans
    (Trees.mem_inorder_iff_mem_setTree query (Trees.Cached.erase t))

/-- The companion's strict-inorder premise recovers the same semantic law. -/
theorem containsKey_eq_true_iff_of_inorder_pairwise {t : BinaryTree (κ × ν)}
    (ordered : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) (query : κ) :
    containsKey query t = true ↔ query ∈ Trees.inorder (Trees.Cached.erase t) :=
  containsKey_eq_true_iff_mem_inorder
    ((OrderedTree.orderedBy_iff_map Prod.fst t).mpr
      (OrderedTree.ordered_of_inorder_pairwise ordered)) query

end LinearOrder
end Search.OrderedMap

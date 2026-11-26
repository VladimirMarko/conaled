import Applications.Search.IntervalSet.Contract
import Applications.Search.IntervalTree.Refinement
import Applications.Search.IntervalTree.Search
import Applications.Search.OrderedMap.Membership

/-! The seven ordinary laws are transported through the existing strict-list
model, with cache consistency as an independent auxiliary invariant. Low
compatibility is needed only for the additional overlap law.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Operations
variable [LE α] [Max α] [Bot α] [LT κ] [DecidableLT κ]

def deleteOps (iv : κ → IntervalKey α) : AbstractSet.DeleteOps κ (BinaryTree (κ × α)) where
  empty := .nil
  insert := insert iv
  member := OrderedMap.containsKey
  delete := delete iv

end Operations

section Validity
variable [LE α] [Max α] [Bot α] [LT κ]

def Valid (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) : Prop :=
  CacheValid iv t ∧ OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))

end Validity

section Algebraic
variable [LE α] [Max α] [Bot α] [LinearOrder κ]

/-- Every insertable key must satisfy the literal singleton's local cache law. -/
theorem inorder_refinement_of_singleton (iv : κ → IntervalKey α)
    (singleton : ∀ key, (iv key).high = max (iv key).high (max ⊥ ⊥)) :
    AbstractSet.Refinement (deleteOps iv) OrderedList.ops
      (fun t => Trees.inorder (Trees.Cached.erase t)) (CacheValid iv) OrderedList.Strict where
  empty := rfl
  auxiliary_empty := cacheValid_nil iv
  insert key _ _ strict := inorder_insert iv key strict
  auxiliary_insert key _ valid _ := insert_cacheValid_of_singleton iv key (singleton key) valid
  delete key _ _ strict := inorder_delete iv key strict
  auxiliary_delete key _ valid _ := delete_cacheValid iv key valid
  member key t _ strict := by
    change OrderedMap.containsKey key t = decide (key ∈ Trees.inorder (Trees.Cached.erase t))
    rw [OrderedMap.containsKey_eq_member_erase]
    exact OrderedTree.member_inorder key strict

theorem set_laws_of_singleton (iv : κ → IntervalKey α)
    (singleton : ∀ key, (iv key).high = max (iv key).high (max ⊥ ⊥)) :
    AbstractSet.DeleteLaws (deleteOps iv)
      (fun t => Trees.setTree (Trees.Cached.erase t)) (Valid iv) :=
  ((inorder_refinement_of_singleton iv singleton).laws OrderedList.laws).congr_observe
    (fun t _ key => Trees.mem_inorder_iff_mem_setTree key (Trees.Cached.erase t))

end Algebraic

section Canonical
variable [LinearOrder α] [OrderBot α] [LinearOrder κ]

theorem inorder_refinement (iv : κ → IntervalKey α) :
    AbstractSet.Refinement (deleteOps iv) OrderedList.ops
      (fun t => Trees.inorder (Trees.Cached.erase t)) (CacheValid iv) OrderedList.Strict :=
  inorder_refinement_of_singleton iv (fun _ => by simp)

/-- Ordinary complete-key semantics do not require compatibility of projected lows. -/
theorem set_laws (iv : κ → IntervalKey α) :
    AbstractSet.DeleteLaws (deleteOps iv)
      (fun t => Trees.setTree (Trees.Cached.erase t)) (Valid iv) :=
  set_laws_of_singleton iv (fun _ => by simp)

theorem intervalSet_laws (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low) :
    IntervalSet.Laws (deleteOps iv) (search iv) iv
      (fun t => Trees.setTree (Trees.Cached.erase t)) (Valid iv) where
  toDeleteLaws := set_laws iv
  overlap t valid query :=
    (search_correct_of_strict iv compatible valid.1 valid.2 query).trans
      (IntervalSet.hasOverlap_image_iff iv (Trees.setTree (Trees.Cached.erase t)) query).symm

end Canonical
end Search.IntervalTree

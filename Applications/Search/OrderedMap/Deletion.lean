import Applications.Search.OrderedMap.DeletionInterface
import Applications.Search.OrderedMap.Enumeration
import Applications.Search.OrderedTree.DeletionCorrectness

/-!
# Both keyed tree deletions as valid-state finite maps

The structural deletion theorem preserves full surviving bindings. Only this
downstream bridge uses the accepted lookup/enumeration correspondence. The
independent whole-tree observer law is stated on ordered states; deletion
does not preserve a raw path observer on arbitrary malformed trees.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u v
variable {κ : Type u} {ν : Type v}
open Search.OrderedTree (Contains OrderedBy)

section Operations
variable [LT κ] [DecidableLT κ]

def delete (key : κ) (t : BinaryTree (κ × ν)) : BinaryTree (κ × ν) :=
  Search.OrderedTree.deleteBy Prod.fst key t

def deleteJoin (key : κ) (t : BinaryTree (κ × ν)) : BinaryTree (κ × ν) :=
  Search.OrderedTree.deleteJoinBy Prod.fst key t

end Operations

section LinearOrder
variable [LinearOrder κ]

theorem ordered_delete {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t) (key : κ) :
    OrderedBy Prod.fst (delete key t) := Search.OrderedTree.orderedBy_deleteBy Prod.fst key ordered

theorem ordered_deleteJoin {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t) (key : κ) :
    OrderedBy Prod.fst (deleteJoin key t) :=
  Search.OrderedTree.orderedBy_deleteJoinBy Prod.fst key ordered

theorem contains_delete {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (binding : κ × ν) :
    Contains binding (delete key t) ↔ Contains binding t ∧ binding.1 ≠ key :=
  Search.OrderedTree.contains_deleteBy Prod.fst key ordered binding

theorem contains_deleteJoin {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (binding : κ × ν) :
    Contains binding (deleteJoin key t) ↔ Contains binding t ∧ binding.1 ≠ key :=
  Search.OrderedTree.contains_deleteJoinBy Prod.fst key ordered binding

private theorem lookup_of_removal {t s : BinaryTree (κ × ν)}
    (ht : OrderedBy Prod.fst t) (hs : OrderedBy Prod.fst s) (key query : κ)
    (contents : ∀ binding, Contains binding s ↔ Contains binding t ∧ binding.1 ≠ key) :
    lookup query s = if query = key then none else lookup query t := by
  apply Option.ext
  intro value
  rw [lookup_eq_some_iff_mem_entries hs,
    ← Search.OrderedTree.contains_iff_mem_entries, contents,
    Search.OrderedTree.contains_iff_mem_entries,
    ← lookup_eq_some_iff_mem_entries ht]
  by_cases heq : query = key <;> simp [heq]

theorem lookup_delete {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key query : κ) :
    lookup query (delete key t) = if query = key then none else lookup query t :=
  lookup_of_removal ordered (ordered_delete ordered key) key query (contains_delete ordered key)

theorem lookup_deleteJoin {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key query : κ) :
    lookup query (deleteJoin key t) = if query = key then none else lookup query t :=
  lookup_of_removal ordered (ordered_deleteJoin ordered key) key query
    (contains_deleteJoin ordered key)

theorem observe_delete {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t) (key : κ) :
    observe (delete key t) = erase key (observe t) := by
  funext query
  simpa only [lookup_correct (ordered_delete ordered key), lookup_correct ordered, erase] using
    lookup_delete ordered key query

theorem observe_deleteJoin {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t) (key : κ) :
    observe (deleteJoin key t) = erase key (observe t) := by
  funext query
  simpa only [lookup_correct (ordered_deleteJoin ordered key), lookup_correct ordered, erase] using
    lookup_deleteJoin ordered key query

def deleteTrees (κ : Type u) (ν : Type v) [LinearOrder κ] : DeleteOps κ ν (Tree κ ν) where
  toOps := trees κ ν
  delete key t := ⟨delete key t.1, ordered_delete t.2 key⟩

def deleteJoinTrees (κ : Type u) (ν : Type v) [LinearOrder κ] : DeleteOps κ ν (Tree κ ν) where
  toOps := trees κ ν
  delete key t := ⟨deleteJoin key t.1, ordered_deleteJoin t.2 key⟩

theorem deleteTrees_projection : (deleteTrees κ ν).toOps = trees κ ν := rfl

theorem deleteJoinTrees_projection : (deleteJoinTrees κ ν).toOps = trees κ ν := rfl

theorem deleteTrees_laws : DeleteLaws (deleteTrees κ ν) decode where
  toLaws := trees_laws
  delete key t := observe_delete t.2 key

theorem deleteJoinTrees_laws : DeleteLaws (deleteJoinTrees κ ν) decode where
  toLaws := trees_laws
  delete key t := observe_deleteJoin t.2 key

end LinearOrder
end Search.OrderedMap

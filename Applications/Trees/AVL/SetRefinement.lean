import Applications.Trees.AVL.Updates
import Applications.Trees.HeightBalance.SetRefinement

/-!
# The cached AVL Set instance

The executable operations are exactly the tolerance-one complete-annotation
programs. The auxiliary invariant is the existing `AVL.Valid`; strict inorder
supplies the independent search-order condition. All Set laws and mixed-history
clients use the shared seven-field operational refinement.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u
variable {α : Type u}

/-- Ordinary cached AVL operations, with the actual comparison-path membership. -/
def deleteOps [LT α] [DecidableLT α] :
    Search.AbstractSet.DeleteOps α (BinaryTree (α × Nat)) :=
  HeightBalance.deleteOps heightAnnotation 1

@[simp] theorem deleteOps_empty [LT α] [DecidableLT α] :
    (deleteOps : Search.AbstractSet.DeleteOps α (BinaryTree (α × Nat))).empty = .nil :=
  rfl

@[simp] theorem deleteOps_insert [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) : deleteOps.insert x t = insert x t := rfl

@[simp] theorem deleteOps_delete [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) : deleteOps.delete x t = delete x t := rfl

@[simp] theorem deleteOps_member [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) :
    deleteOps.member x t = Search.OrderedMap.containsKey x t := rfl

/-- Complete cached AVL validity and strict search ordering remain separate. -/
def SetValid [LT α] (t : BinaryTree (α × Nat)) : Prop :=
  Valid t ∧ Search.OrderedList.Strict (Trees.inorder (Cached.erase t))

@[simp] theorem setValid_nil [LT α] :
    SetValid (.nil : BinaryTree (α × Nat)) :=
  ⟨valid_nil, Search.OrderedList.strict_nil⟩

/-- The public ordinary validity predicate has exactly the generic d=1 meaning. -/
theorem setValid_iff_generic [LT α] (t : BinaryTree (α × Nat)) :
    SetValid t ↔ HeightBalance.SetValid heightAnnotation 1 t :=
  and_congr (validD_one_iff t).symm Iff.rfl

/-- All seven fields use the actual ordinary updates and comparison search. -/
theorem inorder_refinement [LinearOrder α] : Search.AbstractSet.Refinement
    (deleteOps : Search.AbstractSet.DeleteOps α (BinaryTree (α × Nat)))
    Search.OrderedList.ops (fun t => Trees.inorder (Cached.erase t))
    Valid Search.OrderedList.Strict where
  empty := rfl
  auxiliary_empty := valid_nil
  insert x t hv hs :=
    (HeightBalance.inorder_refinement heightAnnotation 1 (by decide)).insert x t
      ((validD_one_iff t).mpr hv) hs
  auxiliary_insert x t hv _ := (valid_insert x t hv).1
  delete x t hv hs :=
    (HeightBalance.inorder_refinement heightAnnotation 1 (by decide)).delete x t
      ((validD_one_iff t).mpr hv) hs
  auxiliary_delete x t hv _ := (valid_delete x t hv).1
  member x t hv hs :=
    (HeightBalance.inorder_refinement heightAnnotation 1 (by decide)).member x t
      ((validD_one_iff t).mpr hv) hs

/-- Full Set laws use the independent structural observer, not search as an oracle. -/
theorem set_laws [LinearOrder α] : Search.AbstractSet.DeleteLaws
    (deleteOps : Search.AbstractSet.DeleteOps α (BinaryTree (α × Nat)))
    (fun t => Trees.setTree (Cached.erase t)) SetValid :=
  (inorder_refinement.laws Search.OrderedList.laws).congr_observe
    (fun t _ x => Trees.mem_inorder_iff_mem_setTree x (Cached.erase t))

end Trees.AVL

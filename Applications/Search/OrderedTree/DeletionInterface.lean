import Applications.Search.AbstractSet.Deletion
import Applications.Search.OrderedTree.DeletionCorrectness

/-! The direct seven-law contracts for the fixed source operations.
Insertion-only clients recover the original baseline algebra by projection.
These proofs precede and do not use the independent list-refinement route. -/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [LinearOrder α]

def deleteOps : AbstractSet.DeleteOps α (BinaryTree α) where
  toOps := baselineOps
  delete := delete

def deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α) where
  toOps := baselineOps
  delete := deleteJoin

theorem deleteOps_projection :
    (deleteOps : AbstractSet.DeleteOps α (BinaryTree α)).toOps = baselineOps := rfl

theorem deleteJoinOps_projection :
    (deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α)).toOps = baselineOps := rfl

theorem deleteLaws : AbstractSet.DeleteLaws
    (deleteOps : AbstractSet.DeleteOps α (BinaryTree α)) (fun t x => Contains x t) Ordered where
  toLaws := baseline_laws
  delete_valid x _ h := ordered_delete h x
  delete x _ h z := contains_delete h x z

theorem deleteJoin_laws : AbstractSet.DeleteLaws
    (deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α)) (fun t x => Contains x t) Ordered where
  toLaws := baseline_laws
  delete_valid x _ h := ordered_deleteJoin h x
  delete x _ h z := contains_deleteJoin h x z

theorem delete_set_laws : AbstractSet.DeleteLaws
    (deleteOps : AbstractSet.DeleteOps α (BinaryTree α)) Trees.setTree Ordered :=
  deleteLaws.congr_observe (fun t _ x => contains_iff_mem_setTree x t)

theorem deleteJoin_set_laws : AbstractSet.DeleteLaws
    (deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α)) Trees.setTree Ordered :=
  deleteJoin_laws.congr_observe (fun t _ x => contains_iff_mem_setTree x t)

abbrev ValidTree (α : Type u) [LinearOrder α] := {t : BinaryTree α // Ordered t}

def validDeleteOps : AbstractSet.DeleteOps α (ValidTree α) where
  empty := ⟨.nil, ordered_nil⟩
  insert x t := ⟨insert x t.1, ordered_insert t.2 x⟩
  member x t := member x t.1
  delete x t := ⟨delete x t.1, ordered_delete t.2 x⟩

theorem validDeleteOps_laws : AbstractSet.DeleteLaws
    (validDeleteOps : AbstractSet.DeleteOps α (ValidTree α))
    (fun t => Trees.setTree t.1) (fun _ => True) where
  empty_valid := trivial
  empty x := delete_set_laws.empty x
  insert_valid _ _ _ := trivial
  insert x t _ z := delete_set_laws.insert x t.1 t.2 z
  member x t _ := delete_set_laws.member x t.1 t.2
  delete_valid _ _ _ := trivial
  delete x t _ z := delete_set_laws.delete x t.1 t.2 z

end Search.OrderedTree

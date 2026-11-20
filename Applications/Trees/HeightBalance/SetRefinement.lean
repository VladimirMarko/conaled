import Applications.Trees.HeightBalance.OrderedUpdates
import Applications.Search.AbstractSet.Refinement
import Applications.Search.OrderedMap.Membership

/-!
# Set refinement of complete-annotation height-balanced updates

The operations are the existing local insertion and predecessor deletion,
with the ordered-map root-to-leaf membership program. Strict inorder supplies
their list semantics; the independent auxiliary invariant retains both actual
balance and correctness of the complete cached annotation. The shared
refinement interface derives Set laws and mixed-history clients from these
separate facts. Source correspondence: `docs/research/fdsa-height-set-refinement.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

/-- The actual local updates and comparison-path query, for every natural tolerance. -/
def deleteOps [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) :
    Search.AbstractSet.DeleteOps α (BinaryTree (α × σ)) where
  empty := .nil
  insert := insert ann d
  member := Search.OrderedMap.containsKey
  delete := delete ann d

@[simp] theorem deleteOps_empty [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) :
    (deleteOps ann d).empty = .nil := rfl

@[simp] theorem deleteOps_insert [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ)) :
    (deleteOps ann d).insert x t = insert ann d x t := rfl

@[simp] theorem deleteOps_delete [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ)) :
    (deleteOps ann d).delete x t = delete ann d x t := rfl

@[simp] theorem deleteOps_member [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ)) :
    (deleteOps ann d).member x t = Search.OrderedMap.containsKey x t := rfl

/-- Complete cache/shape validity and strict ordering remain separate components. -/
def SetValid [LT α] (ann : HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) : Prop :=
  ValidD ann d t ∧ Search.OrderedList.Strict (Trees.inorder (Cached.erase t))

@[simp] theorem setValid_nil [LT α] (ann : HeightAnnotation α σ) (d : Nat) :
    SetValid ann d (.nil : BinaryTree (α × σ)) :=
  ⟨validD_nil ann d, Search.OrderedList.strict_nil⟩

/-- Query correctness needs strict inorder, independently of summaries or balance. -/
theorem member_inorder [LinearOrder α] (x : α) (t : BinaryTree (α × σ))
    (hs : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedMap.containsKey x t =
      decide (x ∈ Trees.inorder (Cached.erase t)) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact Search.OrderedMap.containsKey_eq_true_iff_of_inorder_pairwise hs x

/-- All seven operational obligations, with positivity used for auxiliary closure. -/
theorem inorderRefinement [LinearOrder α]
    (ann : HeightAnnotation α σ) (d : Nat) (hd : 1 ≤ d) :
    Search.AbstractSet.Refinement (deleteOps ann d) Search.OrderedList.ops
      (fun t => Trees.inorder (Cached.erase t))
      (ValidD ann d) Search.OrderedList.Strict where
  empty := rfl
  auxiliary_empty := validD_nil ann d
  insert x t _ hs := inorder_insert ann d x t hs
  auxiliary_insert x t hv _ := (validD_insert ann d x t hd hv).1
  delete x t _ hs := inorder_delete ann d x t hs
  auxiliary_delete x t hv _ := (validD_delete ann d x t hd hv).1
  member x t _ hs := member_inorder x t hs

/-- The independent structural Set observer inherits complete insertion/deletion laws. -/
theorem setLaws [LinearOrder α]
    (ann : HeightAnnotation α σ) (d : Nat) (hd : 1 ≤ d) :
    Search.AbstractSet.DeleteLaws (deleteOps ann d)
      (fun t => Trees.setTree (Cached.erase t)) (SetValid ann d) :=
  ((inorderRefinement ann d hd).laws Search.OrderedList.laws).congr_observe
    (fun t _ x => Trees.mem_inorder_iff_mem_setTree x (Cached.erase t))

/-- Different tolerances and annotation carriers preserve a common list history.
No injectivity of the inorder view or equality of the concrete states is needed. -/
theorem inorder_execute_eq [LinearOrder α]
    (leftAnn : HeightAnnotation α σ) (rightAnn : HeightAnnotation α τ)
    (d e : Nat) (hd : 1 ≤ d) (he : 1 ≤ e)
    (updates : List (Search.AbstractSet.Update α))
    {left : BinaryTree (α × σ)} {right : BinaryTree (α × τ)}
    (hl : SetValid leftAnn d left) (hr : SetValid rightAnn e right)
    (same : Trees.inorder (Cached.erase left) = Trees.inorder (Cached.erase right)) :
    Trees.inorder (Cached.erase
      (Search.AbstractSet.execute (deleteOps leftAnn d) updates left)) =
    Trees.inorder (Cached.erase
      (Search.AbstractSet.execute (deleteOps rightAnn e) updates right)) := by
  calc
    Trees.inorder (Cached.erase
        (Search.AbstractSet.execute (deleteOps leftAnn d) updates left)) =
        Search.AbstractSet.execute Search.OrderedList.ops updates
          (Trees.inorder (Cached.erase left)) :=
      (inorderRefinement leftAnn d hd).execute Search.OrderedList.laws updates hl
    _ = Search.AbstractSet.execute Search.OrderedList.ops updates
          (Trees.inorder (Cached.erase right)) :=
      congrArg (Search.AbstractSet.execute Search.OrderedList.ops updates) same
    _ = Trees.inorder (Cached.erase
          (Search.AbstractSet.execute (deleteOps rightAnn e) updates right)) :=
      ((inorderRefinement rightAnn e he).execute Search.OrderedList.laws updates hr).symm

/-- Actual path-query answers agree after the common word in valid representations. -/
theorem member_execute_eq [LinearOrder α]
    (leftAnn : HeightAnnotation α σ) (rightAnn : HeightAnnotation α τ)
    (d e : Nat) (hd : 1 ≤ d) (he : 1 ≤ e)
    (updates : List (Search.AbstractSet.Update α))
    {left : BinaryTree (α × σ)} {right : BinaryTree (α × τ)}
    (hl : SetValid leftAnn d left) (hr : SetValid rightAnn e right)
    (same : Trees.inorder (Cached.erase left) = Trees.inorder (Cached.erase right)) (x : α) :
    Search.OrderedMap.containsKey x
      (Search.AbstractSet.execute (deleteOps leftAnn d) updates left) =
    Search.OrderedMap.containsKey x
      (Search.AbstractSet.execute (deleteOps rightAnn e) updates right) := by
  calc
    Search.OrderedMap.containsKey x
        (Search.AbstractSet.execute (deleteOps leftAnn d) updates left) =
        Search.OrderedList.ops.member x
          (Search.AbstractSet.execute Search.OrderedList.ops updates
            (Trees.inorder (Cached.erase left))) :=
      (inorderRefinement leftAnn d hd).member_execute
        Search.OrderedList.laws updates hl x
    _ = Search.OrderedList.ops.member x
          (Search.AbstractSet.execute Search.OrderedList.ops updates
            (Trees.inorder (Cached.erase right))) :=
      congrArg (fun xs => Search.OrderedList.ops.member x
        (Search.AbstractSet.execute Search.OrderedList.ops updates xs)) same
    _ = Search.OrderedMap.containsKey x
          (Search.AbstractSet.execute (deleteOps rightAnn e) updates right) :=
      ((inorderRefinement rightAnn e he).member_execute
        Search.OrderedList.laws updates hr x).symm

end Trees.HeightBalance

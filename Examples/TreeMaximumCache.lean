import Applications.Trees.MaximumCacheObservations

/-! Connected source maximum-cache clients. Raw root reads and smart nodes
remain local; generic annotation is a separate full-tree operation. The cases
protect occurrence-preserving key erasure, negative maxima, all-node validity
and the sufficient but unnecessary domain of the reverse adapter law.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeMaximumCache
open Trees Trees.MaximumCache
universe u v
variable {α : Type u} {β : Type v}

theorem empty_label_reader : mx (.nil : BinaryTree (Empty × Empty)) = none := mx_nil

theorem empty_boundary (t : BinaryTree (α × α)) : mx t = none ↔ t = .nil :=
  mx_eq_none_iff t

theorem erased_key_set (t : BinaryTree (α × β)) :
    setTree (Cached.erase t) = Prod.fst '' setTree t :=
  setTree_map Prod.fst t

theorem erased_key_occurrences (t : BinaryTree (α × β)) :
    inorder (Cached.erase t) = (inorder t).map Prod.fst := Cached.inorder_erase t

theorem singleton_value [Max α] (a : α) : mx (nodeMx .nil a .nil) = some a := rfl

theorem singleton_valid [Max α] (a : α) : invarMx (nodeMx .nil a .nil) :=
  nodeMx_valid .nil a .nil invarMx_nil invarMx_nil

def negativeKeys : BinaryTree Int :=
  .node (-5) (.node (-2) .nil .nil) (.node (-9) .nil .nil)

def negativeCached : BinaryTree (Int × Int) :=
  nodeMx (nodeMx .nil (-2) .nil) (-5) (nodeMx .nil (-9) .nil)

theorem negative_valid : invarMx negativeCached :=
  nodeMx_valid _ (-5) _ (singleton_valid (-2)) (singleton_valid (-9))

theorem negative_erases : Cached.erase negativeCached = negativeKeys := rfl

theorem negative_reads : mx negativeCached = some (-2) := by decide

theorem negative_greatest :
    (-2 : Int) ∈ setTree (Cached.erase negativeCached) ∧
      ∀ x ∈ setTree (Cached.erase negativeCached), x ≤ (-2 : Int) :=
  (mx_eq_some_iff negativeCached negative_valid (-2)).mp negative_reads

theorem negative_standard_maximum : (inorder negativeKeys).max? = some (-2) :=
  (mx_eq_max?_inorder negativeCached negative_valid).symm.trans negative_reads

/-- Zero would be an incorrect answer even though it is an upper bound. -/
theorem negative_not_zero : mx negativeCached ≠ some 0 := by
  rw [negative_reads]
  decide

theorem negative_lift_valid : Cached.Valid none combine (lift negativeCached) :=
  (invarMx_iff_valid_lift negativeCached).mp negative_valid

theorem negative_lift_reader : Cached.read none (lift negativeCached) = some (-2) :=
  (read_lift negativeCached).trans negative_reads

theorem negative_smart_node_bridge :
    lift negativeCached = Cached.smartNode none combine
      (lift (nodeMx .nil (-2) .nil)) (-5) (lift (nodeMx .nil (-9) .nil)) :=
  lift_nodeMx _ (-5) _

theorem negative_raw_roundtrip : project (lift negativeCached) = negativeCached :=
  project_lift negativeCached

theorem negative_optional_roundtrip :
    lift (project (lift negativeCached)) = lift negativeCached :=
  lift_project _ negative_lift_valid

/-- The actual generic annotation pass projects back to this source cache. -/
theorem negative_generic_annotation :
    project (Cached.annotate none combine negativeKeys) = negativeCached := by decide

theorem negative_annotation_valid : invarMx (annotate negativeKeys) :=
  annotate_valid negativeKeys

theorem negative_annotation_erases : Cached.erase (annotate negativeKeys) = negativeKeys :=
  erase_annotate negativeKeys

theorem negative_annotation_reads : mx (annotate negativeKeys) = some (-2) :=
  (mx_annotate negativeKeys).trans
    ((summary_eq_max?_inorder negativeKeys).trans negative_standard_maximum)

def repeatedCached : BinaryTree (Nat × Nat) :=
  nodeMx (nodeMx .nil 4 .nil) 4 (nodeMx .nil 1 .nil)

theorem repeated_valid : invarMx repeatedCached :=
  nodeMx_valid _ 4 _ (singleton_valid 4) (singleton_valid 1)

theorem repeated_occurrences : inorder (Cached.erase repeatedCached) = [4, 4, 1] := rfl

theorem repeated_maximum :
    mx repeatedCached = some 4 ∧ (inorder (Cached.erase repeatedCached)).max? = some 4 :=
  ⟨by decide, (mx_eq_max?_inorder repeatedCached repeated_valid).symm.trans (by decide)⟩

theorem asymmetric_left :
    invarMx (nodeMx (nodeMx .nil (7 : Nat) .nil) 2 .nil) ∧
      mx (nodeMx (nodeMx .nil (7 : Nat) .nil) 2 .nil) = some 7 :=
  ⟨nodeMx_valid _ 2 _ (singleton_valid 7) invarMx_nil, by decide⟩

theorem asymmetric_right :
    invarMx (nodeMx .nil (2 : Nat) (nodeMx .nil 7 .nil)) ∧
      mx (nodeMx .nil (2 : Nat) (nodeMx .nil 7 .nil)) = some 7 :=
  ⟨nodeMx_valid _ 2 _ invarMx_nil (singleton_valid 7), by decide⟩

/-- This descendant falsely claims 100 as the maximum of its sole key -9. -/
def forgedLeaf : BinaryTree (Int × Int) := .node (-9, 100) .nil .nil

theorem forged_leaf_invalid : ¬ invarMx forgedLeaf := by
  change ¬ (True ∧ True ∧ (100 : Int) = -9)
  decide

def forgedParent : BinaryTree (Int × Int) := nodeMx forgedLeaf 100 .nil

theorem forged_parent_local_root :
    mx forgedParent = combine (mx forgedLeaf) 100 (mx (.nil : BinaryTree (Int × Int))) :=
  mx_nodeMx forgedLeaf 100 .nil

/-- Even a correct greatest value at the root does not establish all-node validity. -/
theorem forged_parent_root_correct :
    mx forgedParent = (inorder (Cached.erase forgedParent)).max? := by decide

theorem forged_parent_invalid : ¬ invarMx forgedParent := by
  intro h
  exact forged_leaf_invalid ((nodeMx_valid_iff forgedLeaf 100 .nil).mp h).1

def absentOptional : BinaryTree (Nat × Option Nat) := .node (3, none) .nil .nil

theorem absent_optional_invalid : ¬ Cached.Valid none combine absentOptional := by
  change ¬ (True ∧ True ∧ (none : Option Nat) = some 3)
  decide

theorem absent_optional_changes : lift (project absentOptional) ≠ absentOptional := by decide

/-- Projection preserves keys even for an invalid optional cache. -/
theorem absent_optional_erases : Cached.erase (project absentOptional) = Cached.erase absentOptional :=
  erase_project absentOptional

def wrongSome : BinaryTree (Nat × Option Nat) := .node (3, some 99) .nil .nil

theorem wrong_some_invalid : ¬ Cached.Valid none combine wrongSome := by
  change ¬ (True ∧ True ∧ (some 99 : Option Nat) = some 3)
  decide

theorem wrong_some_roundtrip : lift (project wrongSome) = wrongSome := rfl

theorem validity_not_necessary :
    lift (project wrongSome) = wrongSome ∧ ¬ Cached.Valid none combine wrongSome :=
  ⟨wrong_some_roundtrip, wrong_some_invalid⟩

end Examples.TreeMaximumCache

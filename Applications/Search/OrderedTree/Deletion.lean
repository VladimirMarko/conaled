import Applications.Search.OrderedTree.Basic
import Applications.Trees.Leftmost
import Applications.Trees.JoinHeight

/-!
# The two source deletion algorithms

Only the outer ordered search is shared. The equality callbacks retain the
different successor-extraction and root-promoting join algorithms. Labels may
carry arbitrary payloads; comparison uses only their keys. The height bound
is structural and applies to malformed and duplicate-containing trees too.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u v
variable {α : Type u} {κ : Type v}

section Operations
variable [LT κ] [DecidableLT κ]

def deleteWith (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (key : α → κ) (q : κ) : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node a l r =>
      if q < key a then .node a (deleteWith combine key q l) r
      else if key a < q then .node a l (deleteWith combine key q r)
      else combine l r

def deleteBy (key : α → κ) (q : κ) (t : BinaryTree α) : BinaryTree α :=
  deleteWith Trees.joinLeftmost key q t

def deleteJoinBy (key : α → κ) (q : κ) (t : BinaryTree α) : BinaryTree α :=
  deleteWith Trees.join key q t

@[simp] theorem deleteBy_nil (key : α → κ) (q : κ) :
    deleteBy key q .nil = .nil := rfl

@[simp] theorem deleteJoinBy_nil (key : α → κ) (q : κ) :
    deleteJoinBy key q .nil = .nil := rfl

theorem deleteBy_node (key : α → κ) (q : κ) (a : α) (l r : BinaryTree α) :
    deleteBy key q (.node a l r) =
      if q < key a then .node a (deleteBy key q l) r
      else if key a < q then .node a l (deleteBy key q r)
      else Trees.joinLeftmost l r := rfl

theorem deleteJoinBy_node (key : α → κ) (q : κ) (a : α) (l r : BinaryTree α) :
    deleteJoinBy key q (.node a l r) =
      if q < key a then .node a (deleteJoinBy key q l) r
      else if key a < q then .node a l (deleteJoinBy key q r)
      else Trees.join l r := rfl

theorem height_deleteWith_le
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (bound : ∀ l r, (combine l r).height ≤ max l.height r.height + 1)
    (key : α → κ) (q : κ) (t : BinaryTree α) :
    (deleteWith combine key q t).height ≤ t.height := by
  induction t with
  | nil => exact Nat.le_refl 0
  | node a l r ihl ihr =>
      simp only [deleteWith]
      split
      · simp only [BinaryTree.height]
        omega
      · split
        · simp only [BinaryTree.height]
          omega
        · exact bound l r

theorem height_deleteBy_le (key : α → κ) (q : κ) (t : BinaryTree α) :
    (deleteBy key q t).height ≤ t.height :=
  height_deleteWith_le Trees.joinLeftmost Trees.height_joinLeftmost_le key q t

theorem height_deleteJoinBy_le (key : α → κ) (q : κ) (t : BinaryTree α) :
    (deleteJoinBy key q t).height ≤ t.height :=
  height_deleteWith_le Trees.join Trees.height_join_le key q t

end Operations

section LinearKeys
variable [LinearOrder κ]

theorem deleteBy_eq_root (key : α → κ) (a : α) (l r : BinaryTree α) :
    deleteBy key (key a) (.node a l r) = Trees.joinLeftmost l r := by
  simp [deleteBy_node]

theorem deleteBy_eq_root_nil (key : α → κ) (a : α) (l : BinaryTree α) :
    deleteBy key (key a) (.node a l .nil) = l := by
  rw [deleteBy_eq_root, Trees.joinLeftmost_nil_right]

theorem deleteBy_eq_root_extract (key : α → κ) (a x : α)
    (l r s : BinaryTree α) (found : Trees.extractLeftmost r = some (x, s)) :
    deleteBy key (key a) (.node a l r) = .node x l s := by
  rw [deleteBy_eq_root, Trees.joinLeftmost_of_extract found]

theorem deleteJoinBy_eq_root (key : α → κ) (a : α) (l r : BinaryTree α) :
    deleteJoinBy key (key a) (.node a l r) = Trees.join l r := by
  simp [deleteJoinBy_node]

/-- The library's lawful comparison gives precisely the source's three branches. -/
theorem deleteWith_node_compare
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (key : α → κ) (q : κ) (a : α) (l r : BinaryTree α) :
    deleteWith combine key q (.node a l r) =
      match compare q (key a) with
      | .lt => .node a (deleteWith combine key q l) r
      | .eq => combine l r
      | .gt => .node a l (deleteWith combine key q r) := by
  by_cases hlt : q < key a
  · simp [deleteWith, hlt, compare_lt_iff_lt.mpr hlt]
  · by_cases hgt : key a < q
    · simp [deleteWith, hlt, hgt, compare_gt_iff_gt.mpr hgt]
    · have heq : q = key a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst q
      simp [deleteWith]

end LinearKeys

section Sets
variable [LinearOrder α]

def delete (x : α) (t : BinaryTree α) : BinaryTree α := deleteBy id x t

def deleteJoin (x : α) (t : BinaryTree α) : BinaryTree α := deleteJoinBy id x t

theorem height_delete_le (x : α) (t : BinaryTree α) :
    (delete x t).height ≤ t.height := height_deleteBy_le id x t

theorem height_deleteJoin_le (x : α) (t : BinaryTree α) :
    (deleteJoin x t).height ≤ t.height := height_deleteJoinBy_le id x t

theorem member_node_compare (x a : α) (l r : BinaryTree α) :
    member x (.node a l r) =
      match compare x a with
      | .lt => member x l
      | .eq => true
      | .gt => member x r := by
  by_cases hlt : x < a
  · simp [member, memberRun, hlt, compare_lt_iff_lt.mpr hlt]
  · by_cases hgt : a < x
    · simp [member, memberRun, hlt, hgt, compare_gt_iff_gt.mpr hgt]
    · have heq : x = a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst x
      simp [member, memberRun]

theorem insert_node_compare (x a : α) (l r : BinaryTree α) :
    insert x (.node a l r) =
      match compare x a with
      | .lt => .node a (insert x l) r
      | .eq => .node a l r
      | .gt => .node a l (insert x r) := by
  by_cases hlt : x < a
  · simp [insert, hlt, compare_lt_iff_lt.mpr hlt]
  · by_cases hgt : a < x
    · simp [insert, hlt, hgt, compare_gt_iff_gt.mpr hgt]
    · have heq : x = a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst x
      simp [insert]

end Sets
end Search.OrderedTree

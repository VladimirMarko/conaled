import Batteries.Recycling.RBTree.Basic
import Mathlib.Data.Tree.Basic

/-!
# Raw colored source search trees

The existing colored carrier retains every raw input. Source balancing tests
left-left, left-right, right-left and right-right in that order; the provider's
side-specific insertion routines have different behavior on overlapping cases.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

/-- Keys and payloads retain independent universes on the existing raw carrier. -/
abbrev Tree (κ : Type u) (ν : Type v) := RBTree.RBNode (κ × ν)

/-- The source empty state has no payload default. -/
abbrev empty : Tree κ ν := .nil

/-- The source all-node predicate inspects labels independently of search. -/
abbrev ForallT (P : κ → ν → Prop) (t : Tree κ ν) : Prop :=
  t.All (fun binding => P binding.1 binding.2)

@[simp] theorem forallT_nil (P : κ → ν → Prop) :
    ForallT P (.nil : Tree κ ν) := trivial

theorem forallT_node (P : κ → ν → Prop) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    ForallT P (.node color left (key, value) right) ↔
      P key value ∧ ForallT P left ∧ ForallT P right := Iff.rfl

/-- Erase only colors through the existing fold, retaining original key/value data. -/
def eraseColors (t : Tree κ ν) : BinaryTree (κ × ν) :=
  t.fold .nil (fun left binding right => .node binding left right)

@[simp] theorem eraseColors_nil : eraseColors (.nil : Tree κ ν) = .nil := rfl

theorem eraseColors_node (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    eraseColors (.node color left (key, value) right) =
      .node (key, value) (eraseColors left) (eraseColors right) := rfl

/-- Search the colored tree using the supplied short-circuit Boolean tests. -/
def lookup? (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν) : Option ν :=
  (t.find? fun binding =>
    if ltb query binding.1 then .lt
    else if ltb binding.1 query then .gt else .eq).map Prod.snd

/-- Apply a caller's default only after the optional search. -/
def lookup (ltb : κ → κ → Bool) (default : ν) (query : κ) (t : Tree κ ν) : ν :=
  (lookup? ltb query t).getD default

@[simp] theorem lookup?_nil (ltb : κ → κ → Bool) (query : κ) :
    lookup? ltb query (.nil : Tree κ ν) = none := rfl

theorem lookup?_node (ltb : κ → κ → Bool) (query : κ) (color : RBTree.RBColor)
    (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    lookup? ltb query (.node color left (key, value) right) =
      if ltb query key then lookup? ltb query left
      else if ltb key query then lookup? ltb query right else some value := by
  cases hleft : ltb query key <;> cases hright : ltb key query <;>
    simp [lookup?, RBTree.RBNode.find?, hleft, hright]

@[simp] theorem lookup_nil (ltb : κ → κ → Bool) (default : ν) (query : κ) :
    lookup ltb default query (.nil : Tree κ ν) = default := rfl

theorem lookup_node (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (color : RBTree.RBColor) (left : Tree κ ν) (key : κ) (value : ν) (right : Tree κ ν) :
    lookup ltb default query (.node color left (key, value) right) =
      if ltb query key then lookup ltb default query left
      else if ltb key query then lookup ltb default query right else value := by
  simp only [lookup, lookup?_node]
  split
  · rfl
  · split <;> rfl

/-- The source accumulator traversal is the provider's in-order right fold. -/
abbrev elementsAux (t : Tree κ ν) (suffix : List (κ × ν)) : List (κ × ν) :=
  t.foldr List.cons suffix

/-- Enumerate the original bindings in their raw in-order arrangement. -/
abbrev elements (t : Tree κ ν) : List (κ × ν) := t.toList

@[simp] theorem elementsAux_nil (suffix : List (κ × ν)) :
    elementsAux (.nil : Tree κ ν) suffix = suffix := rfl

theorem elementsAux_node (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) (suffix : List (κ × ν)) :
    elementsAux (.node color left (key, value) right) suffix =
      elementsAux left ((key, value) :: elementsAux right suffix) := rfl

@[simp] theorem elements_nil : elements (.nil : Tree κ ν) = [] := rfl

/-- Blacken only the root through the existing provider operation. -/
abbrev makeBlack (t : Tree κ ν) : Tree κ ν := t.setBlack

@[simp] theorem makeBlack_nil : makeBlack (.nil : Tree κ ν) = .nil := rfl

theorem makeBlack_node (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    makeBlack (.node color left (key, value) right) =
      .node .black left (key, value) right := rfl

/-- The complete source matcher, including its observable priority on raw trees. -/
def balance (color : RBTree.RBColor) (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) : Tree κ ν :=
  match color with
  | .red => .node .red left (key, value) right
  | .black =>
    match left with
    | .node .red (.node .red a x b) y c =>
        .node .red (.node .black a x b) y (.node .black c (key, value) right)
    | .node .red a x (.node .red b y c) =>
        .node .red (.node .black a x b) y (.node .black c (key, value) right)
    | _ =>
      match right with
      | .node .red (.node .red b y c) z d =>
          .node .red (.node .black left (key, value) b) y (.node .black c z d)
      | .node .red b y (.node .red c z d) =>
          .node .red (.node .black left (key, value) b) y (.node .black c z d)
      | _ => .node .black left (key, value) right

/-- Source insertion applies the complete matcher after either recursive descent. -/
def ins (ltb : κ → κ → Bool) (key : κ) (value : ν) : Tree κ ν → Tree κ ν
  | .nil => .node .red .nil (key, value) .nil
  | .node color left (old, previous) right =>
      if ltb key old then balance color (ins ltb key value left) old previous right
      else if ltb old key then balance color left old previous (ins ltb key value right)
      else .node color left (key, value) right

/-- The source public insertion always blackens the result of its raw insertion. -/
def insert (ltb : κ → κ → Bool) (key : κ) (value : ν) (t : Tree κ ν) : Tree κ ν :=
  makeBlack (ins ltb key value t)

@[simp] theorem ins_nil (ltb : κ → κ → Bool) (key : κ) (value : ν) :
    ins ltb key value (.nil : Tree κ ν) = .node .red .nil (key, value) .nil := rfl

theorem ins_node (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (color : RBTree.RBColor) (left : Tree κ ν) (old : κ) (previous : ν)
    (right : Tree κ ν) :
    ins ltb key value (.node color left (old, previous) right) =
      if ltb key old then balance color (ins ltb key value left) old previous right
      else if ltb old key then balance color left old previous (ins ltb key value right)
      else .node color left (key, value) right := rfl

theorem insert_eq_makeBlack_ins (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (t : Tree κ ν) : insert ltb key value t = makeBlack (ins ltb key value t) := rfl

@[simp] theorem insert_nil (ltb : κ → κ → Bool) (key : κ) (value : ν) :
    insert ltb key value (.nil : Tree κ ν) = .node .black .nil (key, value) .nil := rfl

/-- Every source balance branch constructs a node, including raw malformed inputs. -/
theorem balance_ne_nil (color : RBTree.RBColor) (left : Tree κ ν)
    (key : κ) (value : ν) (right : Tree κ ν) :
    balance color left key value right ≠ .nil := by
  unfold balance
  split
  · intro h
    cases h
  · split
    · intro h
      cases h
    · intro h
      cases h
    · split <;> intro h <;> cases h

theorem makeBlack_ne_nil {t : Tree κ ν} (nonempty : t ≠ .nil) :
    makeBlack t ≠ .nil := by
  cases t with
  | nil => exact nonempty
  | node color left binding right =>
      intro h
      cases h

/-- Raw insertion is nonempty for every supplied Boolean comparator. -/
theorem ins_ne_nil (ltb : κ → κ → Bool) (key : κ) (value : ν) (t : Tree κ ν) :
    ins ltb key value t ≠ .nil := by
  cases t with
  | nil => intro h; cases h
  | node color left binding right =>
      cases binding with
      | mk old previous =>
          rw [ins_node]
          split
          · exact balance_ne_nil _ _ _ _ _
          · split
            · exact balance_ne_nil _ _ _ _ _
            · intro h
              cases h

theorem insert_ne_nil (ltb : κ → κ → Bool) (key : κ) (value : ν) (t : Tree κ ν) :
    insert ltb key value t ≠ .nil :=
  makeBlack_ne_nil (ins_ne_nil ltb key value t)

end Search.RedBlack

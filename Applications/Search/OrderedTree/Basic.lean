import Mathlib.Data.Tree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Defs.LinearOrder
import Applications.Resources.Measured
import SquareKit.Relations

/-!
# Ordered node-valued trees and finite contents

The structural type is Mathlib's `BinaryTree`. Content and ordering are
independent observations: `Contains` visits both children, whereas the search
algorithms below may discard a child only under `Ordered`. `OrderedBy` also
serves keyed trees whose payloads have no order.

These are tree values, not allocated cell graphs. Constructor equality here
does not assert physical sharing or the absence of allocation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u v
variable {α : Type u} {κ : Type v}

/-- Independent membership observation; it does not perform directed search. -/
def Contains (x : α) : BinaryTree α → Prop
  | .nil => False
  | .node y l r => x = y ∨ Contains x l ∨ Contains x r

/-- Inorder occurrence contents, including repetitions in unordered trees. -/
def entries : BinaryTree α → List α
  | .nil => []
  | .node x l r => entries l ++ x :: entries r

theorem contains_iff_mem_entries (x : α) (t : BinaryTree α) :
    Contains x t ↔ x ∈ entries t := by
  induction t with
  | nil => simp [Contains, entries]
  | node y l r hl hr =>
      simp only [Contains, entries, List.mem_append, List.mem_cons, ← hl, ← hr]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem entries_length (t : BinaryTree α) : (entries t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node x l r hl hr => simp [entries, hl, hr, Nat.add_assoc]

/-- All labels, with no order or equality assumptions on the label type. -/
def All (P : α → Prop) : BinaryTree α → Prop
  | .nil => True
  | .node x l r => P x ∧ All P l ∧ All P r

theorem all_iff (P : α → Prop) (t : BinaryTree α) :
    All P t ↔ ∀ x, Contains x t → P x := by
  induction t with
  | nil => simp [All, Contains]
  | node y l r hl hr =>
      simp only [All, hl, hr, Contains]
      constructor
      · rintro ⟨hy, hleft, hright⟩ x (h | h | h)
        · simpa only [h] using hy
        · exact hleft x h
        · exact hright x h
      · intro h
        exact ⟨h y (Or.inl rfl), fun x hx => h x (Or.inr (Or.inl hx)),
          fun x hx => h x (Or.inr (Or.inr hx))⟩

theorem All.of_contains {P : α → Prop} {t : BinaryTree α}
    (h : All P t) {x : α} (hx : Contains x t) : P x := (all_iff P t).mp h x hx

theorem All.mono {P Q : α → Prop} {t : BinaryTree α}
    (h : All P t) (pq : ∀ x, P x → Q x) : All Q t :=
  (all_iff Q t).mpr fun x hx => pq x (h.of_contains hx)

/-- Strict bounds constrain every descendant, rather than just child roots. -/
def OrderedBy [LT κ] (key : α → κ) : BinaryTree α → Prop
  | .nil => True
  | .node x l r => OrderedBy key l ∧ OrderedBy key r ∧
      All (fun y => key y < key x) l ∧ All (fun y => key x < key y) r

def Ordered [LT α] : BinaryTree α → Prop := OrderedBy id

@[simp] theorem ordered_nil [LT α] : Ordered (.nil : BinaryTree α) := trivial

theorem ordered_node [LT α] (x : α) (l r : BinaryTree α) :
    Ordered (.node x l r) ↔
      Ordered l ∧ Ordered r ∧ All (fun y => y < x) l ∧ All (fun y => x < y) r :=
  Iff.rfl

theorem all_map {β : Type v} (f : α → β) (P : β → Prop) (t : BinaryTree α) :
    All P (t.map f) ↔ All (fun x => P (f x)) t := by
  induction t with
  | nil => rfl
  | node x l r hl hr => simp [BinaryTree.map, All, hl, hr]

theorem orderedBy_iff_map [LT κ] (key : α → κ) (t : BinaryTree α) :
    OrderedBy key t ↔ Ordered (t.map key) := by
  induction t with
  | nil => rfl
  | node x l r hl hr =>
      simp only [OrderedBy, BinaryTree.map, ordered_node, ← hl, ← hr, all_map]

section LinearOrder
variable [LinearOrder α]

theorem contains_left_iff {x y : α} {l r : BinaryTree α}
    (ordered : Ordered (.node y l r)) (xy : x < y) :
    Contains x (.node y l r) ↔ Contains x l := by
  constructor
  · rintro (h | h | h)
    · exact False.elim ((ne_of_lt xy) h)
    · exact h
    · exact False.elim ((lt_asymm xy) (ordered.2.2.2.of_contains h))
  · exact fun h => Or.inr (Or.inl h)

theorem contains_right_iff {x y : α} {l r : BinaryTree α}
    (ordered : Ordered (.node y l r)) (yx : y < x) :
    Contains x (.node y l r) ↔ Contains x r := by
  constructor
  · rintro (h | h | h)
    · exact False.elim ((ne_of_gt yx) h)
    · exact False.elim ((lt_asymm yx) (ordered.2.2.1.of_contains h))
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- The source algorithm, with one charge for each executed element `<` test.
Empty-node inspection and other work are intentionally not this measure. -/
def memberRun (x : α) : BinaryTree α → Resources.Measured Bool Nat
  | .nil => (false, 0)
  | .node y l r =>
      if x < y then
        let q := memberRun x l
        (q.1, q.2 + 1)
      else if y < x then
        let q := memberRun x r
        (q.1, q.2 + 2)
      else (true, 2)

def member (x : α) (t : BinaryTree α) : Bool := (memberRun x t).1

theorem member_correct {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    member x t = true ↔ Contains x t := by
  induction t with
  | nil => simp [member, memberRun, Contains]
  | node y l r hl hr =>
      by_cases xy : x < y
      · simpa only [member, memberRun, ite_eq_left xy] using
          (hl ordered.1).trans (contains_left_iff ordered xy).symm
      · by_cases yx : y < x
        · simpa only [member, memberRun, ite_eq_right xy, ite_eq_left yx] using
            (hr ordered.2.1).trans (contains_right_iff ordered yx).symm
        · have eq : x = y := le_antisymm (le_of_not_gt yx) (le_of_not_gt xy)
          simp [member, memberRun, Contains, eq]

theorem memberRun_bound (x : α) (t : BinaryTree α) :
    (memberRun x t).2 ≤ 2 * t.height := by
  induction t with
  | nil => simp [memberRun]
  | node y l r hl hr =>
      simp only [memberRun]
      split
      · simp only [BinaryTree.height]
        have le : l.height ≤ max l.height r.height := Nat.le_max_left _ _
        omega
      · split
        · simp only [BinaryTree.height]
          have le : r.height ≤ max l.height r.height := Nat.le_max_right _ _
          omega
        · simp only [BinaryTree.height]
          omega

/-- Baseline path copying: a matching subtree is returned unchanged, while
each strict comparison branch rebuilds its ancestor on the recursive return. -/
def insert (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | .node y l r =>
      if x < y then .node y (insert x l) r
      else if y < x then .node y l (insert x r)
      else .node y l r

theorem contains_insert (x z : α) (t : BinaryTree α) :
    Contains z (insert x t) ↔ z = x ∨ Contains z t := by
  induction t with
  | nil => simp [insert, Contains]
  | node y l r hl hr =>
      by_cases xy : x < y
      · simp only [insert, ite_eq_left xy, Contains, hl]
        tauto
      · by_cases yx : y < x
        · simp only [insert, ite_eq_right xy, ite_eq_left yx, Contains, hr]
          tauto
        · have eq : x = y := le_antisymm (le_of_not_gt yx) (le_of_not_gt xy)
          simp [insert, Contains, eq]

theorem all_insert {P : α → Prop} {t : BinaryTree α} (h : All P t)
    (x : α) (hx : P x) : All P (insert x t) := by
  apply (all_iff P _).mpr
  intro y hy
  rcases (contains_insert x y t).mp hy with eq | hy
  · simpa only [eq] using hx
  · exact h.of_contains hy

theorem ordered_insert {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    Ordered (insert x t) := by
  induction t with
  | nil => simp [insert, Ordered, OrderedBy, All]
  | node y l r hl hr =>
      by_cases xy : x < y
      · rw [insert, ite_eq_left xy]
        exact ⟨hl ordered.1, ordered.2.1, all_insert ordered.2.2.1 x xy,
          ordered.2.2.2⟩
      · by_cases yx : y < x
        · rw [insert, ite_eq_right xy, ite_eq_left yx]
          exact ⟨ordered.1, hr ordered.2.1, ordered.2.2.1,
            all_insert ordered.2.2.2 x yx⟩
        · simpa only [insert, ite_eq_right xy, ite_eq_right yx] using ordered

end LinearOrder
end Search.OrderedTree

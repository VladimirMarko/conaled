import Applications.Sequences.SharedList.Basic
import Mathlib.Data.Tree.Basic

/-!
# Immutable binary-tree cells

The existing fresh-cell store is instantiated with a value and a left root as
its payload, and a right root as its second field. No list invariant is imposed
on those cells. `Represents` supplies the independent binary-tree observation,
including backwards references for both children. Ordering is a separate law
for search-tree clients; repeated values and shared children are permitted here.

Allocation counts concern this mathematical cell store, not Lean's allocator.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree

abbrev Root := Sequences.SharedList.Root
abbrev Cell (α : Type) := (α × Root) × Root
abbrev Store (α : Type) := Sequences.SharedList.Store (α × Root)
abbrev Below := Sequences.SharedList.Below

variable {α : Type}

def empty : Store α := Sequences.SharedList.empty

/-- A root observes an unfolded tree, allowing its two children to share cells. -/
inductive Represents (heap : Durability.Heap (Cell α)) : Root → BinaryTree α → Prop
  | nil : Represents heap none .nil
  | node {a : Nat} {x : α} {l r : Root} {lt rt : BinaryTree α} :
      heap a = some ((x, l), r) → Below l a → Below r a →
      Represents heap l lt → Represents heap r rt →
      Represents heap (some a) (.node x lt rt)

theorem Represents.mono {a b : Durability.Heap (Cell α)}
    (extension : Durability.Extends a b) {root : Root} {t : BinaryTree α}
    (h : Represents a root t) : Represents b root t := by
  induction h with
  | nil => exact .nil
  | node lookup leftBelow rightBelow _ _ ihl ihr =>
      exact .node (extension _ _ lookup) leftBelow rightBelow ihl ihr

theorem Represents.unique {heap : Durability.Heap (Cell α)}
    {root : Root} {t u : BinaryTree α}
    (h : Represents heap root t) (k : Represents heap root u) : t = u := by
  induction h generalizing u with
  | nil => cases k; rfl
  | @node a x l r lt rt lookup _ _ _ _ ihl ihr =>
      cases k with
      | @node _ y l' r' lt' rt' lookup' _ _ hl hr =>
          have eq : ((x, l), r) = ((y, l'), r') :=
            Option.some.inj (lookup.symm.trans lookup')
          cases eq
          exact congrArg₂ (BinaryTree.node x) (ihl hl) (ihr hr)

theorem Represents.below_next {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) : Below root s.next := by
  cases h with
  | nil => trivial
  | @node a x l r lt rt lookup _ _ _ _ =>
      change a < s.next
      by_contra hn
      have vacant := s.vacant a (by omega)
      rw [vacant] at lookup
      contradiction

/-- Height, unlike unfolded node count, is bounded by the backwards frontier. -/
theorem Represents.height_le {heap : Durability.Heap (Cell α)}
    {root : Root} {t : BinaryTree α} (h : Represents heap root t) {n : Nat}
    (below : Below root n) : t.height ≤ n := by
  induction h generalizing n with
  | nil => simp
  | @node a x l r lt rt _ leftBelow rightBelow _ _ ihl ihr =>
      have hl := ihl leftBelow
      have hr := ihr rightBelow
      change a < n at below
      simp only [BinaryTree.height]
      omega

theorem Represents.height_le_next {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) : t.height ≤ s.next :=
  h.height_le h.below_next

def allocate (s : Store α) (x : α) (l r : Root) : Store α × Root :=
  Sequences.SharedList.allocate s (x, l) r

@[simp] theorem allocate_next (s : Store α) (x : α) (l r : Root) :
    (allocate s x l r).1.next = s.next + 1 := rfl

@[simp] theorem allocate_root (s : Store α) (x : α) (l r : Root) :
    (allocate s x l r).2 = some s.next := rfl

@[simp] theorem allocate_lookup (s : Store α) (x : α) (l r : Root) :
    (allocate s x l r).1.heap s.next = some ((x, l), r) :=
  Sequences.SharedList.allocate_lookup s (x, l) r

theorem allocate_extends (s : Store α) (x : α) (l r : Root) :
    Durability.Extends s.heap (allocate s x l r).1.heap :=
  Sequences.SharedList.allocate_extends s (x, l) r

theorem allocate_represents {s : Store α} {l r : Root} {lt rt : BinaryTree α}
    (hl : Represents s.heap l lt) (hr : Represents s.heap r rt) (x : α) :
    Represents (allocate s x l r).1.heap (allocate s x l r).2 (.node x lt rt) :=
  .node (allocate_lookup s x l r) hl.below_next hr.below_next
    (hl.mono (allocate_extends s x l r)) (hr.mono (allocate_extends s x l r))

/-- Allocation preserves every old observed tree, including other retained roots. -/
theorem allocate_retains (s : Store α) (x : α) (l r old : Root) (t : BinaryTree α)
    (h : Represents s.heap old t) :
    Represents (allocate s x l r).1.heap old t :=
  h.mono (allocate_extends s x l r)

def read (s : Store α) (root : Root) : Option (Cell α) := root.bind s.heap

@[simp] theorem read_none (s : Store α) : read s none = none := rfl

theorem read_node {s : Store α} {root : Root} {x : α} {lt rt : BinaryTree α}
    (h : Represents s.heap root (.node x lt rt)) :
    ∃ l r, read s root = some ((x, l), r) ∧
      Represents s.heap l lt ∧ Represents s.heap r rt := by
  cases h with
  | @node a _ l r _ _ lookup _ _ hl hr =>
      exact ⟨l, r, by simpa [read] using lookup, hl, hr⟩

/-- The allocated node stores exactly the supplied child roots. -/
@[simp] theorem read_allocate (s : Store α) (x : α) (l r : Root) :
    read (allocate s x l r).1 (allocate s x l r).2 = some ((x, l), r) := by
  simp [read]

end Search.SharedTree

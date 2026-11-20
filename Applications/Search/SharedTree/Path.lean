import Applications.Search.SharedTree.Basic
import Applications.Trees.Direction

/-!
# Paths and unchanged off-path roots

`Rebuilds` records the concrete old and new cell lookups along a path. Each
ancestor keeps its label and its unselected child address. This relation alone
does not assert fresh allocation; an execution must establish that separately.
The observation theorem identifies actual roots at every path which diverges
from the rebuilt path, in the extended heap that retains the old version.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type}

/-- The structural search route needs comparisons, independently of their order
laws. A map can supply a key projection without ordering its stored payloads. -/
def searchPathBy {κ : Type} [LT κ] [DecidableLT κ] (key : α → κ) (x : κ) :
    BinaryTree α → List Branch
  | .nil => []
  | .node y l r =>
      if x < key y then .left :: searchPathBy key x l
      else if key y < x then .right :: searchPathBy key x r
      else []

theorem searchPathBy_length_le {κ : Type} [LT κ] [DecidableLT κ]
    (key : α → κ) (x : κ) (t : BinaryTree α) :
    (searchPathBy key x t).length ≤ t.height := by
  induction t with
  | nil => simp [searchPathBy]
  | node y l r hl hr =>
      have leLeft := Nat.le_max_left l.height r.height
      have leRight := Nat.le_max_right l.height r.height
      simp only [searchPathBy]
      split
      · simp only [List.length_cons, BinaryTree.height]
        omega
      · split
        · simp only [List.length_cons, BinaryTree.height]
          omega
        · simp

def child (direction : Branch) (cell : Cell α) : Root :=
  match direction with
  | .left => cell.1.2
  | .right => cell.2

/-- An empty path succeeds even at an empty root; traversing past empty fails. -/
def follow (heap : Durability.Heap (Cell α)) : List Branch → Root → Option Root
  | [], root => some root
  | direction :: path, root =>
      (root.bind heap).bind fun cell => follow heap path (child direction cell)

theorem follow_step {heap : Durability.Heap (Cell α)} {a : Nat} {cell : Cell α}
    (lookup : heap a = some cell) (direction : Branch) (path : List Branch) :
    follow heap (direction :: path) (some a) = follow heap path (child direction cell) := by
  simp [follow, lookup]

theorem follow_mono {before after : Durability.Heap (Cell α)}
    (extension : Durability.Extends before after) {path : List Branch} {r q : Root}
    (h : follow before path r = some q) : follow after path r = some q := by
  induction path generalizing r with
  | nil => exact h
  | cons direction path ih =>
      cases r with
      | none => simp [follow] at h
      | some a =>
          cases lookup : before a with
          | none => simp [follow, lookup] at h
          | some cell =>
              rw [follow_step lookup] at h
              rw [follow_step (extension _ _ lookup)]
              exact ih h

/-- The probe enters an unselected branch after a possibly empty common prefix. -/
def Diverges : List Branch → List Branch → Prop
  | .left :: path, .left :: probe => Diverges path probe
  | .right :: path, .right :: probe => Diverges path probe
  | .left :: _, .right :: _ => True
  | .right :: _, .left :: _ => True
  | _, _ => False

inductive Rebuilds (before after : Durability.Heap (Cell α)) :
    Root → Root → List Branch → Prop
  | here (oldRoot newRoot : Root) : Rebuilds before after oldRoot newRoot []
  | left {a b : Nat} {x : α} {l r newLeft : Root} {path : List Branch} :
      before a = some ((x, l), r) → after b = some ((x, newLeft), r) →
      Rebuilds before after l newLeft path →
      Rebuilds before after (some a) (some b) (.left :: path)
  | right {a b : Nat} {x : α} {l r newRight : Root} {path : List Branch} :
      before a = some ((x, l), r) → after b = some ((x, l), newRight) →
      Rebuilds before after r newRight path →
      Rebuilds before after (some a) (some b) (.right :: path)

theorem Rebuilds.mono {before after later : Durability.Heap (Cell α)}
    {r q : Root} {path : List Branch} (h : Rebuilds before after r q path)
    (extension : Durability.Extends after later) : Rebuilds before later r q path := by
  induction h with
  | here r q => exact .here r q
  | left oldLookup newLookup _ ih => exact .left oldLookup (extension _ _ newLookup) ih
  | right oldLookup newLookup _ ih => exact .right oldLookup (extension _ _ newLookup) ih

/-- Off-path observations have identical addresses, not merely equal tree values.
Both old and new versions are read in the same cell-preserving final heap. -/
theorem Rebuilds.off_path {before after : Durability.Heap (Cell α)}
    {r q : Root} {path : List Branch} (h : Rebuilds before after r q path)
    (extension : Durability.Extends before after) (probe : List Branch)
    (different : Diverges path probe) : follow after probe q = follow after probe r := by
  induction h generalizing probe with
  | here r q => cases probe <;> simp [Diverges] at different
  | left oldLookup newLookup _ ih =>
      cases probe with
      | nil => simp [Diverges] at different
      | cons direction probe =>
          rw [follow_step newLookup, follow_step (extension _ _ oldLookup)]
          cases direction with
          | left => exact ih probe different
          | right => rfl
  | right oldLookup newLookup _ ih =>
      cases probe with
      | nil => simp [Diverges] at different
      | cons direction probe =>
          rw [follow_step newLookup, follow_step (extension _ _ oldLookup)]
          cases direction with
          | left => rfl
          | right => exact ih probe different

end Search.SharedTree

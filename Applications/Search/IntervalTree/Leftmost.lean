import Applications.Search.IntervalTree.Basic
import Applications.Trees.Leftmost

/-! A single left-spine extraction with smart reconstruction. The optional
interface records the empty domain; its nonempty wrapper has no fallback key.
Erasure reuses the shared tree program and its raw inorder proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v} [LE α] [Max α] [Bot α]

/-- The name follows the source; leastness would require a separate order premise. -/
def splitMin (iv : κ → IntervalKey α) :
    BinaryTree (κ × α) → Option (κ × BinaryTree (κ × α))
  | .nil => none
  | .node (a, _) .nil r => some (a, r)
  | .node (a, _) (.node b ll lr) r =>
      (splitMin iv (.node b ll lr)).map fun p => (p.1, node iv p.2 a r)

@[simp] theorem splitMin_nil (iv : κ → IntervalKey α) :
    splitMin iv .nil = none := rfl

@[simp] theorem splitMin_node_nil (iv : κ → IntervalKey α) (a : κ) (m : α)
    (r : BinaryTree (κ × α)) :
    splitMin iv (.node (a, m) .nil r) = some (a, r) := rfl

theorem splitMin_node_of_ne_nil (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) (hne : l ≠ .nil) :
    splitMin iv (.node (a, m) l r) =
      (splitMin iv l).map (fun p => (p.1, node iv p.2 a r)) := by
  cases l <;> simp_all [splitMin]

@[simp] theorem splitMin_eq_none_iff (iv : κ → IntervalKey α)
    (t : BinaryTree (κ × α)) : splitMin iv t = none ↔ t = .nil := by
  induction t with
  | nil => simp
  | node a l r ihl _ =>
      rcases a with ⟨a, m⟩
      cases l <;> simp_all [splitMin]

theorem splitMin_exists (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (hne : t ≠ .nil) : ∃ x s, splitMin iv t = some (x, s) := by
  cases h : splitMin iv t with
  | none => exact False.elim (hne ((splitMin_eq_none_iff iv t).mp h))
  | some p => exact ⟨p.1, p.2, rfl⟩

def splitMinNonempty (iv : κ → IntervalKey α) (t : BinaryTree (κ × α))
    (hne : t ≠ .nil) : κ × BinaryTree (κ × α) :=
  (splitMin iv t).get (by
    apply Option.isSome_iff_exists.mpr
    obtain ⟨x, s, h⟩ := splitMin_exists iv hne
    exact ⟨(x, s), h⟩)

theorem splitMinNonempty_spec (iv : κ → IntervalKey α) (t : BinaryTree (κ × α))
    (hne : t ≠ .nil) : splitMin iv t = some (splitMinNonempty iv t hne) := by
  simp only [splitMinNonempty, Option.some_get]

theorem splitMinNonempty_eq (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (hne : t ≠ .nil) {x : κ} {s : BinaryTree (κ × α)}
    (found : splitMin iv t = some (x, s)) : splitMinNonempty iv t hne = (x, s) :=
  Option.some.inj ((splitMinNonempty_spec iv t hne).symm.trans found)

/-- Both the complete label and the erased residual agree with the shared program. -/
theorem erase_splitMin (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    (splitMin iv t).map (fun p => (p.1, Trees.Cached.erase p.2)) =
      Trees.extractLeftmost (Trees.Cached.erase t) := by
  induction t with
  | nil => rfl
  | node a l r ihl _ =>
      rcases a with ⟨a, m⟩
      cases l with
      | nil => rfl
      | node b ll lr =>
          rcases b with ⟨b, n⟩
          simp only [splitMin, Trees.Cached.erase_node, Trees.extractLeftmost,
            Option.map_map] at ihl ⊢
          rw [← ihl, Option.map_map]
          simp only [Function.comp_def, erase_node]

theorem extractLeftmost_of_splitMin (iv : κ → IntervalKey α)
    {t s : BinaryTree (κ × α)} {x : κ} (found : splitMin iv t = some (x, s)) :
    Trees.extractLeftmost (Trees.Cached.erase t) = some (x, Trees.Cached.erase s) := by
  rw [← erase_splitMin iv t, found]
  rfl

theorem splitMin_inorder (iv : κ → IntervalKey α) {t s : BinaryTree (κ × α)}
    {x : κ} (found : splitMin iv t = some (x, s)) :
    x :: Trees.inorder (Trees.Cached.erase s) = Trees.inorder (Trees.Cached.erase t) :=
  Trees.extractLeftmost_inorder (extractLeftmost_of_splitMin iv found)

theorem splitMin_cacheValid (iv : κ → IntervalKey α) {t s : BinaryTree (κ × α)}
    {x : κ} (valid : CacheValid iv t) (found : splitMin iv t = some (x, s)) :
    CacheValid iv s := by
  induction t generalizing x s with
  | nil => cases found
  | node a l r ihl _ =>
      rcases a with ⟨a, m⟩
      have parts := (cacheValid_node iv a m l r).mp valid
      cases l with
      | nil =>
          simp only [splitMin_node_nil, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact parts.2.1
      | node b ll lr =>
          obtain ⟨y, s', hy⟩ := splitMin_exists iv
            (t := .node b ll lr) (by intro h; cases h)
          simp only [splitMin, hy, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact node_cacheValid iv (ihl parts.1 hy) a parts.2.1

/-- Successor deletion extracts once from a proved nonempty right tree. -/
def join (iv : κ → IntervalKey α) (l : BinaryTree (κ × α)) :
    BinaryTree (κ × α) → BinaryTree (κ × α)
  | .nil => l
  | .node a rl rr =>
      let p := splitMinNonempty iv (.node a rl rr) (by intro h; cases h)
      node iv l p.1 p.2

@[simp] theorem join_nil_right (iv : κ → IntervalKey α) (l : BinaryTree (κ × α)) :
    join iv l .nil = l := rfl

theorem join_of_splitMin (iv : κ → IntervalKey α) {l r s : BinaryTree (κ × α)}
    {x : κ} (found : splitMin iv r = some (x, s)) : join iv l r = node iv l x s := by
  cases r with
  | nil => cases found
  | node a rl rr =>
      simp only [join, splitMinNonempty_eq iv (by intro h; cases h) found]

theorem erase_join (iv : κ → IntervalKey α) (l r : BinaryTree (κ × α)) :
    Trees.Cached.erase (join iv l r) =
      Trees.joinLeftmost (Trees.Cached.erase l) (Trees.Cached.erase r) := by
  cases r with
  | nil => rfl
  | node a rl rr =>
      obtain ⟨x, s, found⟩ := splitMin_exists iv
        (t := .node a rl rr) (by intro h; cases h)
      rw [join_of_splitMin iv found, erase_node,
        Trees.joinLeftmost_of_extract (extractLeftmost_of_splitMin iv found)]

theorem inorder_join (iv : κ → IntervalKey α) (l r : BinaryTree (κ × α)) :
    Trees.inorder (Trees.Cached.erase (join iv l r)) =
      Trees.inorder (Trees.Cached.erase l) ++ Trees.inorder (Trees.Cached.erase r) := by
  rw [erase_join, Trees.inorder_joinLeftmost]

theorem join_cacheValid (iv : κ → IntervalKey α) {l r : BinaryTree (κ × α)}
    (left : CacheValid iv l) (right : CacheValid iv r) : CacheValid iv (join iv l r) := by
  cases r with
  | nil => exact left
  | node a rl rr =>
      obtain ⟨x, s, found⟩ := splitMin_exists iv
        (t := .node a rl rr) (by intro h; cases h)
      rw [join_of_splitMin iv found]
      exact node_cacheValid iv left x (splitMin_cacheValid iv right found)

end Search.IntervalTree

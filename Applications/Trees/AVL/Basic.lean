import Applications.Trees.Cached
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Lean.Elab.Tactic.Omega

/-! Cached AVL foundations on the existing product-labelled binary tree.
The raw reader and local constructor use stored heights. Recursive cache
correctness and independent shape balance together recover the source invariant.
Search ordering is separate; the existing ordered-map membership program ignores
these annotations. Source and statement assessment:
`docs/research/fdsa-avl-foundations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u v
variable {α : Type u} {β : Type v}

/-- The height fold's local summary operation, independent of payload. -/
def heightCombine (left : Nat) (_ : α) (right : Nat) : Nat :=
  max left right + 1

/-- Read only the root annotation, including on incorrectly cached trees. -/
def ht (t : BinaryTree (α × Nat)) : Nat := Cached.read 0 t

/-- Reuse both children and compute only the new root's height annotation. -/
def node (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    BinaryTree (α × Nat) := Cached.smartNode 0 heightCombine l a r

/-- Correct height summaries at every node; this does not require balance. -/
def CacheValid (t : BinaryTree (α × Nat)) : Prop :=
  Cached.Valid 0 heightCombine t

@[simp] theorem ht_nil : ht (.nil : BinaryTree (α × Nat)) = 0 := rfl

@[simp] theorem ht_node (a : α) (n : Nat) (l r : BinaryTree (α × Nat)) :
    ht (.node (a, n) l r) = n := rfl

theorem node_eq (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    node l a r = .node (a, max (ht l) (ht r) + 1) l r := rfl

@[simp] theorem ht_node_smart (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : ht (node l a r) = max (ht l) (ht r) + 1 :=
  Cached.read_smartNode 0 heightCombine l a r

@[simp] theorem erase_node (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    Cached.erase (node l a r) = .node a (Cached.erase l) (Cached.erase r) :=
  Cached.erase_smartNode 0 heightCombine l a r

@[simp] theorem height_node (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (node l a r).height = max l.height r.height + 1 := rfl

theorem inorder_node (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    Trees.inorder (Cached.erase (node l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) := by
  rw [erase_node, Trees.inorder_node]

/-- Both natural inequalities are necessary to express the signed condition. -/
theorem height_balance_iff (hl hr : Nat) :
    |(hl : Int) - (hr : Int)| ≤ 1 ↔ hl ≤ hr + 1 ∧ hr ≤ hl + 1 := by
  rw [abs_le]
  omega

/-- Recursive AVL shape balance, independent of annotations and label order. -/
def Balanced : BinaryTree α → Prop
  | .nil => True
  | .node _ l r =>
      Balanced l ∧ Balanced r ∧ l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

@[simp] theorem balanced_nil : Balanced (.nil : BinaryTree α) := trivial

theorem balanced_node (a : α) (l r : BinaryTree α) :
    Balanced (.node a l r) ↔
      Balanced l ∧ Balanced r ∧ l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1 :=
  Iff.rfl

/-- Arbitrary label maps preserve and reflect shape balance. -/
theorem balanced_map (f : α → β) (t : BinaryTree α) :
    Balanced (t.map f) ↔ Balanced t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, balanced_node, Trees.height_map, ihl, ihr]

@[simp] theorem cacheValid_nil : CacheValid (.nil : BinaryTree (α × Nat)) :=
  Cached.valid_nil 0 heightCombine

theorem cacheValid_node (a : α) (n : Nat) (l r : BinaryTree (α × Nat)) :
    CacheValid (.node (a, n) l r) ↔
      CacheValid l ∧ CacheValid r ∧ n = max (ht l) (ht r) + 1 := Iff.rfl

/-- Repairing the root does not repair a malformed child. -/
theorem node_cacheValid_iff (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    CacheValid (node l a r) ↔ CacheValid l ∧ CacheValid r :=
  Cached.smartNode_valid_iff 0 heightCombine l a r

theorem ht_eq_height_of_cacheValid (t : BinaryTree (α × Nat)) (h : CacheValid t) :
    ht t = t.height := by
  calc
    ht t = Trees.fold 0 heightCombine (Cached.erase t) :=
      Cached.read_eq_fold 0 heightCombine t h
    _ = (Cached.erase t).height := Trees.fold_height _
    _ = t.height := Cached.height_erase t

/-- The cached AVL invariant combines independent shape and cache conditions. -/
def Valid (t : BinaryTree (α × Nat)) : Prop :=
  Balanced (Cached.erase t) ∧ CacheValid t

theorem valid_iff (t : BinaryTree (α × Nat)) :
    Valid t ↔ Balanced (Cached.erase t) ∧ CacheValid t := Iff.rfl

@[simp] theorem valid_nil : Valid (.nil : BinaryTree (α × Nat)) :=
  ⟨balanced_nil, cacheValid_nil⟩

/-- Exact source characterization: actual signed heights, the correct root
cache, and recursive validity of both children. -/
theorem valid_node_iff (a : α) (n : Nat) (l r : BinaryTree (α × Nat)) :
    Valid (.node (a, n) l r) ↔
      Valid l ∧ Valid r ∧ |(l.height : Int) - (r.height : Int)| ≤ 1 ∧
        n = max l.height r.height + 1 := by
  constructor
  · rintro ⟨hs, hc⟩
    rcases (balanced_node a (Cached.erase l) (Cached.erase r)).mp
      (by simpa only [Cached.erase_node] using hs) with ⟨hsl, hsr, hlr, hrl⟩
    rcases (cacheValid_node a n l r).mp hc with ⟨hcl, hcr, hn⟩
    refine ⟨⟨hsl, hcl⟩, ⟨hsr, hcr⟩, ?_, ?_⟩
    · apply (height_balance_iff _ _).mpr
      simpa only [Cached.height_erase] using And.intro hlr hrl
    · simpa only [ht_eq_height_of_cacheValid l hcl, ht_eq_height_of_cacheValid r hcr]
        using hn
  · rintro ⟨hl, hr, hbal, hn⟩
    refine ⟨?_, ?_⟩
    · rw [Cached.erase_node, balanced_node]
      refine ⟨hl.1, hr.1, ?_, ?_⟩
      · simpa only [Cached.height_erase] using ((height_balance_iff _ _).mp hbal).1
      · simpa only [Cached.height_erase] using ((height_balance_iff _ _).mp hbal).2
    · apply (cacheValid_node a n l r).mpr
      refine ⟨hl.2, hr.2, ?_⟩
      simpa only [ht_eq_height_of_cacheValid l hl.2, ht_eq_height_of_cacheValid r hr.2]
        using hn

theorem ht_eq_height (t : BinaryTree (α × Nat)) (h : Valid t) : ht t = t.height :=
  ht_eq_height_of_cacheValid t h.2

/-- Valid children need the local height condition as well as correct caches. -/
theorem node_valid_iff (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    Valid (node l a r) ↔
      Valid l ∧ Valid r ∧ |(l.height : Int) - (r.height : Int)| ≤ 1 := by
  rw [node_eq, valid_node_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hl, hr, hbal⟩
    refine ⟨hl, hr, hbal, ?_⟩
    rw [ht_eq_height l hl, ht_eq_height r hr]

theorem valid_singleton (a : α) : Valid (node .nil a .nil) :=
  (node_valid_iff .nil a .nil).mpr
    ⟨valid_nil, valid_nil, (height_balance_iff 0 0).mpr ⟨by decide, by decide⟩⟩

/-- Whole-tree decoration is separate from local smart construction. -/
def annotate (t : BinaryTree α) : BinaryTree (α × Nat) :=
  Cached.annotate 0 heightCombine t

theorem annotate_cacheValid (t : BinaryTree α) : CacheValid (annotate t) :=
  Cached.annotate_valid 0 heightCombine t

theorem erase_annotate (t : BinaryTree α) : Cached.erase (annotate t) = t :=
  Cached.erase_annotate 0 heightCombine t

theorem ht_annotate (t : BinaryTree α) : ht (annotate t) = t.height := by
  calc
    ht (annotate t) = Trees.fold 0 heightCombine t := Cached.read_annotate 0 heightCombine t
    _ = t.height := Trees.fold_height t

/-- Decoration fixes caches, but neither creates nor destroys shape balance. -/
theorem valid_annotate_iff (t : BinaryTree α) : Valid (annotate t) ↔ Balanced t := by
  constructor
  · intro h
    simpa only [erase_annotate] using h.1
  · intro h
    exact ⟨by simpa only [erase_annotate] using h, annotate_cacheValid t⟩

end Trees.AVL

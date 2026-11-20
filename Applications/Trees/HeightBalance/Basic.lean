import Applications.Trees.Cached
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Lean.Elab.Tactic.Omega

/-! Height balance for trees carrying an arbitrary complete cached summary.
The projected height is an observation of the summary algebra, rather than a
replacement for its other coordinates. Shape balance and recursive cache
correctness remain separate predicates. Source and statement assessment:
`docs/research/fdsa-height-rebalance.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v w
variable {α : Type u} {σ : Type v} {β : Type w}

/-- A complete local summary algebra equipped with its height observation. -/
structure HeightAnnotation (α : Type u) (σ : Type v) where
  empty : σ
  combine : σ → α → σ → σ
  height : σ → Nat
  height_empty : height empty = 0
  height_combine : ∀ l a r,
    height (combine l a r) = max (height l) (height r) + 1

/-- Read only the stored root summary, even when it is malformed. -/
def ht (ann : HeightAnnotation α σ) (t : BinaryTree (α × σ)) : Nat :=
  ann.height (Cached.read ann.empty t)

/-- Reuse the children and compute the new root's complete annotation. -/
def node (ann : HeightAnnotation α σ) (l : BinaryTree (α × σ))
    (a : α) (r : BinaryTree (α × σ)) : BinaryTree (α × σ) :=
  Cached.smartNode ann.empty ann.combine l a r

/-- Every complete annotation, including those of descendants, is correct. -/
def CacheValid (ann : HeightAnnotation α σ) (t : BinaryTree (α × σ)) : Prop :=
  Cached.Valid ann.empty ann.combine t

@[simp] theorem ht_nil (ann : HeightAnnotation α σ) :
    ht ann (.nil : BinaryTree (α × σ)) = 0 := ann.height_empty

@[simp] theorem ht_node (ann : HeightAnnotation α σ) (a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    ht ann (.node (a, s) l r) = ann.height s := rfl

theorem node_eq (ann : HeightAnnotation α σ) (l : BinaryTree (α × σ))
    (a : α) (r : BinaryTree (α × σ)) :
    node ann l a r =
      .node (a, ann.combine (Cached.read ann.empty l) a (Cached.read ann.empty r)) l r :=
  rfl

@[simp] theorem ht_node_smart (ann : HeightAnnotation α σ)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    ht ann (node ann l a r) = max (ht ann l) (ht ann r) + 1 :=
  ann.height_combine _ a _

@[simp] theorem erase_node (ann : HeightAnnotation α σ)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    Cached.erase (node ann l a r) = .node a (Cached.erase l) (Cached.erase r) :=
  Cached.erase_smartNode ann.empty ann.combine l a r

@[simp] theorem height_node (ann : HeightAnnotation α σ)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    (node ann l a r).height = max l.height r.height + 1 := rfl

theorem inorder_node (ann : HeightAnnotation α σ) (l : BinaryTree (α × σ))
    (a : α) (r : BinaryTree (α × σ)) :
    Trees.inorder (Cached.erase (node ann l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) := by
  rw [erase_node, Trees.inorder_node]

@[simp] theorem cacheValid_nil (ann : HeightAnnotation α σ) :
    CacheValid ann (.nil : BinaryTree (α × σ)) :=
  Cached.valid_nil ann.empty ann.combine

theorem cacheValid_node (ann : HeightAnnotation α σ) (a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    CacheValid ann (.node (a, s) l r) ↔
      CacheValid ann l ∧ CacheValid ann r ∧
        s = ann.combine (Cached.read ann.empty l) a (Cached.read ann.empty r) := Iff.rfl

/-- Computing a new root does not repair a malformed retained child. -/
theorem node_cacheValid_iff (ann : HeightAnnotation α σ)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    CacheValid ann (node ann l a r) ↔ CacheValid ann l ∧ CacheValid ann r :=
  Cached.smartNode_valid_iff ann.empty ann.combine l a r

/-- The algebra's height observation commutes with the ordinary tree fold. -/
theorem height_fold (ann : HeightAnnotation α σ) (t : BinaryTree α) :
    ann.height (Trees.fold ann.empty ann.combine t) = t.height := by
  calc
    ann.height (Trees.fold ann.empty ann.combine t) =
        Trees.fold (0 : Nat) (fun l (_ : α) r => max l r + 1) t :=
      Trees.fold_fusion ann.empty ann.combine 0 (fun l (_ : α) r => max l r + 1)
        ann.height ann.height_empty ann.height_combine t
    _ = t.height := Trees.fold_height t

theorem ht_eq_height_of_cacheValid (ann : HeightAnnotation α σ)
    (t : BinaryTree (α × σ)) (h : CacheValid ann t) : ht ann t = t.height := by
  calc
    ht ann t = ann.height (Trees.fold ann.empty ann.combine (Cached.erase t)) :=
      congrArg ann.height (Cached.read_eq_fold ann.empty ann.combine t h)
    _ = (Cached.erase t).height := height_fold ann _
    _ = t.height := Cached.height_erase t

/-- Cast before subtraction: natural truncated subtraction loses a sign. -/
theorem height_balance_iff (d hl hr : Nat) :
    |(hl : Int) - (hr : Int)| ≤ (d : Int) ↔ hl ≤ hr + d ∧ hr ≤ hl + d := by
  rw [abs_le]
  omega

theorem height_lower_bound_iff (d hl hr : Nat) : hr - d ≤ hl ↔ hr ≤ hl + d := by
  omega

/-- A positive integer tolerance has a positive, exact natural representative. -/
theorem int_tolerance_toNat (D : Int) (hD : 1 ≤ D) :
    1 ≤ D.toNat ∧ (D.toNat : Int) = D := by
  omega

theorem height_balance_int_iff (D : Int) (hD : 1 ≤ D) (hl hr : Nat) :
    |(hl : Int) - (hr : Int)| ≤ D ↔ hl ≤ hr + D.toNat ∧ hr ≤ hl + D.toNat := by
  simpa only [(int_tolerance_toNat D hD).2] using height_balance_iff D.toNat hl hr

/-- Recursive balance of the actual shape, independent of any cached summary. -/
def BalancedD (d : Nat) : BinaryTree α → Prop
  | .nil => True
  | .node _ l r =>
      BalancedD d l ∧ BalancedD d r ∧ l.height ≤ r.height + d ∧ r.height ≤ l.height + d

@[simp] theorem balancedD_nil (d : Nat) : BalancedD d (.nil : BinaryTree α) := trivial

theorem balancedD_node (d : Nat) (a : α) (l r : BinaryTree α) :
    BalancedD d (.node a l r) ↔
      BalancedD d l ∧ BalancedD d r ∧ l.height ≤ r.height + d ∧ r.height ≤ l.height + d :=
  Iff.rfl

theorem balancedD_map (d : Nat) (f : α → β) (t : BinaryTree α) :
    BalancedD d (t.map f) ↔ BalancedD d t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, balancedD_node, Trees.height_map, ihl, ihr]

/-- Shape balance together with correctness of the complete cached algebra. -/
def ValidD (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ)) : Prop :=
  BalancedD d (Cached.erase t) ∧ CacheValid ann t

theorem validD_iff (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ)) :
    ValidD ann d t ↔ BalancedD d (Cached.erase t) ∧ CacheValid ann t := Iff.rfl

@[simp] theorem validD_nil (ann : HeightAnnotation α σ) (d : Nat) :
    ValidD ann d (.nil : BinaryTree (α × σ)) :=
  ⟨balancedD_nil d, cacheValid_nil ann⟩

/-- Exact node validity includes the whole summary equation, not just height. -/
theorem validD_node_iff (ann : HeightAnnotation α σ) (d : Nat) (a : α) (s : σ)
    (l r : BinaryTree (α × σ)) :
    ValidD ann d (.node (a, s) l r) ↔
      ValidD ann d l ∧ ValidD ann d r ∧
        |(l.height : Int) - (r.height : Int)| ≤ (d : Int) ∧
        s = ann.combine (Cached.read ann.empty l) a (Cached.read ann.empty r) := by
  constructor
  · rintro ⟨hs, hc⟩
    rcases (balancedD_node d a (Cached.erase l) (Cached.erase r)).mp
      (by simpa only [Cached.erase_node] using hs) with ⟨hsl, hsr, hlr, hrl⟩
    rcases (cacheValid_node ann a s l r).mp hc with ⟨hcl, hcr, hn⟩
    refine ⟨⟨hsl, hcl⟩, ⟨hsr, hcr⟩, ?_, hn⟩
    apply (height_balance_iff d _ _).mpr
    simpa only [Cached.height_erase] using And.intro hlr hrl
  · rintro ⟨hl, hr, hbal, hn⟩
    refine ⟨?_, (cacheValid_node ann a s l r).mpr ⟨hl.2, hr.2, hn⟩⟩
    rw [Cached.erase_node, balancedD_node]
    refine ⟨hl.1, hr.1, ?_, ?_⟩
    · simpa only [Cached.height_erase] using ((height_balance_iff d _ _).mp hbal).1
    · simpa only [Cached.height_erase] using ((height_balance_iff d _ _).mp hbal).2

theorem ht_eq_height (ann : HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) (h : ValidD ann d t) : ht ann t = t.height :=
  ht_eq_height_of_cacheValid ann t h.2

theorem node_validD_iff (ann : HeightAnnotation α σ) (d : Nat)
    (l : BinaryTree (α × σ)) (a : α) (r : BinaryTree (α × σ)) :
    ValidD ann d (node ann l a r) ↔
      ValidD ann d l ∧ ValidD ann d r ∧
        |(l.height : Int) - (r.height : Int)| ≤ (d : Int) := by
  rw [node_eq, validD_node_iff]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · rintro ⟨hl, hr, hbal⟩
    exact ⟨hl, hr, hbal, rfl⟩

end Trees.HeightBalance

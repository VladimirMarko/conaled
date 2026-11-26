import Applications.Resources.HeightBalance.Updates
import Applications.Resources.HeightBalance.Membership
import Applications.Trees.AVL.SetRefinement

/-!
# Ordinary measured cached AVL operations

These are the actual complete-annotation measured programs at tolerance one.
The height projection costs zero; the combining callback executes max and then
successor, one event each. Comparison costs one. Root reads, constructors and
entries retain the generic tariff, including both additions in the outer repair
test. Returned callbacks, recursive trees and predecessors are consumed directly.

Raw erasure, structural work, cache validity and strict set ordering are separate
contracts. This source-event model does not assert machine runtime or allocation.
Correspondence: `docs/research/fdsa-avl-continuation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.AVL
universe u
variable {α : Type u}

def heightRun (h : Nat) : Measured Nat Nat := (h, 0)

/-- The successor consumes the actual maximum returned by the first event. -/
def combineRun (l : Nat) (_ : α) (r : Nat) : Measured Nat Nat :=
  bind (max l r, 1) (fun largest => (largest + 1, 1))

def ltRun [LT α] [DecidableLT α] (x y : α) : Measured Bool Nat :=
  (decide (x < y), 1)

@[simp] theorem heightRun_value (h : Nat) : (heightRun h).1 = h := rfl
@[simp] theorem heightRun_cost (h : Nat) : (heightRun h).2 = 0 := rfl
@[simp] theorem combineRun_value (l : Nat) (a : α) (r : Nat) :
    (combineRun l a r).1 = Trees.AVL.heightCombine l a r := rfl
@[simp] theorem combineRun_cost (l : Nat) (a : α) (r : Nat) :
    (combineRun l a r).2 = 2 := rfl
@[simp] theorem ltRun_value [LT α] [DecidableLT α] (x y : α) :
    (ltRun x y).1 = decide (x < y) := rfl
@[simp] theorem ltRun_cost [LT α] [DecidableLT α] (x y : α) :
    (ltRun x y).2 = 1 := rfl

def htRun (t : BinaryTree (α × Nat)) : Measured Nat Nat :=
  HeightBalance.htRun 0 heightRun t

def nodeRun (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    Measured (BinaryTree (α × Nat)) Nat :=
  TreeCache.nodeRun 0 combineRun l a r

def balLRun (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    Measured (BinaryTree (α × Nat)) Nat :=
  HeightBalance.balLRun 0 heightRun combineRun 1 l a r

def balRRun (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    Measured (BinaryTree (α × Nat)) Nat :=
  HeightBalance.balRRun 0 heightRun combineRun 1 l a r

def lookupRun [LT α] [DecidableLT α] (q : α) (t : BinaryTree (α × Nat)) :
    Measured (Option Nat) Nat := HeightBalance.lookupRun ltRun q t

def memberRun [LT α] [DecidableLT α] (q : α) (t : BinaryTree (α × Nat)) :
    Measured Bool Nat := HeightBalance.memberRun ltRun q t

def insertRun [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    Measured (BinaryTree (α × Nat)) Nat :=
  HeightBalance.insertRun 0 heightRun combineRun ltRun 1 x t

def splitMaxRun (t : BinaryTree (α × Nat)) :
    Measured (Option (BinaryTree (α × Nat) × α)) Nat :=
  HeightBalance.splitMaxRun 0 heightRun combineRun 1 t

def deleteRun [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    Measured (BinaryTree (α × Nat)) Nat :=
  HeightBalance.deleteRun 0 heightRun combineRun ltRun 1 x t

@[simp] theorem htRun_eq (t : BinaryTree (α × Nat)) :
    htRun t = (Trees.AVL.ht t, 1) := rfl

@[simp] theorem nodeRun_eq (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : nodeRun l a r = (Trees.AVL.node l a r, 5) := rfl

theorem htRun_value (t : BinaryTree (α × Nat)) :
    (htRun t).1 = Trees.AVL.ht t := rfl
theorem htRun_cost (t : BinaryTree (α × Nat)) : (htRun t).2 = 1 := rfl
theorem nodeRun_value (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : (nodeRun l a r).1 = Trees.AVL.node l a r := rfl
theorem nodeRun_cost (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : (nodeRun l a r).2 = 5 := rfl

theorem balLRun_value (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : (balLRun l a r).1 = Trees.AVL.balL l a r :=
  HeightBalance.balLRun_value Trees.AVL.heightAnnotation heightRun combineRun 1 l a r
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem balRRun_value (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) : (balRRun l a r).1 = Trees.AVL.balR l a r :=
  HeightBalance.balRRun_value Trees.AVL.heightAnnotation heightRun combineRun 1 l a r
    (fun _ => rfl) (fun _ _ _ => rfl)

private theorem ordinary_ht (t : BinaryTree (α × Nat)) :
    HeightBalance.htRun 0 heightRun t = (Trees.AVL.ht t, 1) := rfl

private theorem ordinary_node (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    TreeCache.nodeRun 0 combineRun l a r = (Trees.AVL.node l a r, 5) := rfl

/-- The generic program still executes two additions; only their values simplify. -/
private theorem ordinary_excess (l r : BinaryTree (α × Nat)) :
    HeightBalance.excessRun 0 heightRun 1 l r =
      (decide (Trees.AVL.ht l = Trees.AVL.ht r + 2), 5) := by
  simp [HeightBalance.excessRun, ordinary_ht, bind, Nat.add_assoc]

private theorem ordinary_le (l r : BinaryTree (α × Nat)) :
    HeightBalance.leHeightRun 0 heightRun l r =
      (decide (Trees.AVL.ht l ≤ Trees.AVL.ht r), 3) := rfl

theorem balLRun_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (h : Trees.AVL.ht l ≠ Trees.AVL.ht r + 2) :
    balLRun l a r = (Trees.AVL.node l a r, 11) := by
  simp [balLRun, HeightBalance.balLRun, ordinary_excess, h, ordinary_node,
    bind, CallCount.tick]

theorem balRRun_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (h : Trees.AVL.ht r ≠ Trees.AVL.ht l + 2) :
    balRRun l a r = (Trees.AVL.node l a r, 11) := by
  simp [balRRun, HeightBalance.balRRun, ordinary_excess, h, ordinary_node,
    bind, CallCount.tick]

theorem balLRun_single (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (B : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (h : n = Trees.AVL.ht C + 2) (hs : Trees.AVL.ht B ≤ Trees.AVL.ht A) :
    balLRun (.node (a, n) A B) c C = (Trees.AVL.node A a (Trees.AVL.node B c C), 19) := by
  simp [balLRun, HeightBalance.balLRun, ordinary_excess, ordinary_le, h, hs,
    ordinary_node, bind, CallCount.tick]

theorem balLRun_double (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (h : n = Trees.AVL.ht C + 2) (hs : Trees.AVL.ht A < m) :
    balLRun (.node (a, n) A (.node (b, m) P Q)) c C =
      (Trees.AVL.node (Trees.AVL.node A a P) b (Trees.AVL.node Q c C), 24) := by
  simp [balLRun, HeightBalance.balLRun, ordinary_excess, ordinary_le, h,
    Nat.not_le.mpr hs, ordinary_node, bind, CallCount.tick]

theorem balRRun_single (A : BinaryTree (α × Nat)) (a : α)
    (B : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (h : n = Trees.AVL.ht A + 2) (hs : Trees.AVL.ht B ≤ Trees.AVL.ht C) :
    balRRun A a (.node (c, n) B C) = (Trees.AVL.node (Trees.AVL.node A a B) c C, 19) := by
  simp [balRRun, HeightBalance.balRRun, ordinary_excess, ordinary_le, h, hs,
    ordinary_node, bind, CallCount.tick]

theorem balRRun_double (A : BinaryTree (α × Nat)) (a : α)
    (P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (h : n = Trees.AVL.ht A + 2) (hs : Trees.AVL.ht C < m) :
    balRRun A a (.node (c, n) (.node (b, m) P Q) C) =
      (Trees.AVL.node (Trees.AVL.node A a P) b (Trees.AVL.node Q c C), 24) := by
  simp [balRRun, HeightBalance.balRRun, ordinary_excess, ordinary_le, h,
    Nat.not_le.mpr hs, ordinary_node, bind, CallCount.tick]

theorem lookupRun_value [LT α] [DecidableLT α] (q : α) (t : BinaryTree (α × Nat)) :
    (lookupRun q t).1 = Search.OrderedMap.lookup q t :=
  HeightBalance.lookupRun_value_of_global ltRun q t (fun _ _ => rfl)

theorem memberRun_value [LT α] [DecidableLT α] (q : α) (t : BinaryTree (α × Nat)) :
    (memberRun q t).1 = Search.OrderedMap.containsKey q t :=
  HeightBalance.memberRun_value ltRun q t (fun _ _ => rfl)

theorem insertRun_value [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (insertRun x t).1 = Trees.AVL.insert x t :=
  HeightBalance.insertRun_value Trees.AVL.heightAnnotation heightRun combineRun ltRun 1 x t
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

theorem splitMaxRun_value (t : BinaryTree (α × Nat)) :
    (splitMaxRun t).1 = Trees.AVL.splitMaxOption t :=
  HeightBalance.splitMaxRun_value Trees.AVL.heightAnnotation heightRun combineRun 1 t
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem deleteRun_value [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (deleteRun x t).1 = Trees.AVL.delete x t :=
  HeightBalance.deleteRun_value Trees.AVL.heightAnnotation heightRun combineRun ltRun 1 x t
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem lookupRun_nil [LT α] [DecidableLT α] (q : α) :
    lookupRun q .nil = (none, 1) := rfl
@[simp] theorem memberRun_nil [LT α] [DecidableLT α] (q : α) :
    memberRun q .nil = (false, 1) := rfl
@[simp] theorem insertRun_nil [LT α] [DecidableLT α] (x : α) :
    insertRun x .nil = (Trees.AVL.node .nil x .nil, 6) := rfl
@[simp] theorem splitMaxRun_nil : splitMaxRun (.nil : BinaryTree (α × Nat)) = (none, 1) := rfl
@[simp] theorem splitMaxRun_node_nil (a : α) (n : Nat) (l : BinaryTree (α × Nat)) :
    splitMaxRun (.node (a, n) l .nil) = (some (l, a), 1) := rfl
@[simp] theorem deleteRun_nil [LT α] [DecidableLT α] (x : α) :
    deleteRun x .nil = (.nil, 1) := rfl

theorem lookupRun_node [LT α] [DecidableLT α] (q a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    lookupRun q (.node (a, n) l r) =
      if q < a then ((lookupRun q l).1, 2 + (lookupRun q l).2)
      else if a < q then ((lookupRun q r).1, 3 + (lookupRun q r).2)
      else (some n, 3) := by
  simpa only [lookupRun, ltRun, decide_eq_true_eq] using
    HeightBalance.lookupRun_node ltRun q (a, n) l r

theorem memberRun_node [LT α] [DecidableLT α] (q a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    memberRun q (.node (a, n) l r) =
      if q < a then ((memberRun q l).1, 2 + (memberRun q l).2)
      else if a < q then ((memberRun q r).1, 3 + (memberRun q r).2)
      else (true, 3) := by
  simpa only [memberRun, ltRun, decide_eq_true_eq] using
    HeightBalance.memberRun_node ltRun q (a, n) l r

theorem insertRun_node [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    insertRun x (.node (a, n) l r) =
      if x < a then
        let child := insertRun x l
        let repair := balLRun child.1 a r
        (repair.1, 2 + child.2 + repair.2)
      else if a < x then
        let child := insertRun x r
        let repair := balRRun l a child.1
        (repair.1, 3 + child.2 + repair.2)
      else (.node (a, n) l r, 4) := by
  simp only [insertRun, HeightBalance.insertRun_node, ltRun, balLRun, balRRun,
    bind, CallCount.tick, decide_eq_true_eq]
  split
  · apply Prod.ext
    · rfl
    · dsimp; omega
  · split
    · apply Prod.ext
      · rfl
      · dsimp; omega
    · rfl

theorem splitMaxRun_node_of_ne_nil (a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) (hr : r ≠ .nil) :
    splitMaxRun (.node (a, n) l r) =
      let child := splitMaxRun r
      match child.1 with
      | none => (none, 1 + child.2)
      | some (right, m) =>
          let repair := balLRun l a right
          (some (repair.1, m), 1 + child.2 + repair.2) := by
  rw [splitMaxRun, HeightBalance.splitMaxRun_node_of_ne_nil _ _ _ _ _ _ _ _ hr]
  cases h : (HeightBalance.splitMaxRun 0 heightRun combineRun 1 r).1 with
  | none =>
      simp only [splitMaxRun, h, bind, pure, CallCount.tick]
      apply Prod.ext
      · rfl
      · dsimp; omega
  | some p =>
      rcases p with ⟨right, m⟩
      simp only [splitMaxRun, h, balLRun, bind, pure, CallCount.tick]
      apply Prod.ext
      · rfl
      · dsimp; omega

theorem deleteRun_node [LT α] [DecidableLT α] (x a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    deleteRun x (.node (a, n) l r) =
      if x < a then
        let child := deleteRun x l
        let repair := balRRun child.1 a r
        (repair.1, 2 + child.2 + repair.2)
      else if a < x then
        let child := deleteRun x r
        let repair := balLRun l a child.1
        (repair.1, 3 + child.2 + repair.2)
      else
        let child := splitMaxRun l
        match child.1 with
        | none => (r, 3 + child.2)
        | some (left, m) =>
            let repair := balRRun left m r
            (repair.1, 3 + child.2 + repair.2) := by
  simp only [deleteRun, HeightBalance.deleteRun_node, ltRun, bind, CallCount.tick,
    decide_eq_true_eq, balLRun, balRRun, splitMaxRun]
  split
  · apply Prod.ext
    · rfl
    · dsimp; omega
  · split
    · apply Prod.ext
      · rfl
      · dsimp; omega
    · cases h : (HeightBalance.splitMaxRun 0 heightRun combineRun 1 l).1 with
      | none =>
          apply Prod.ext
          · rfl
          · dsimp [pure]; omega
      | some p =>
          rcases p with ⟨left, m⟩
          apply Prod.ext
          · rfl
          · dsimp; omega

theorem balLRun_cost_le (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (balLRun l a r).2 ≤ 24 := by
  simpa only [balLRun] using HeightBalance.balLRun_cost_le 0 heightRun combineRun 1 l a r
    0 2 (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)

theorem balRRun_cost_le (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (balRRun l a r).2 ≤ 24 := by
  simpa only [balRRun] using HeightBalance.balRRun_cost_le 0 heightRun combineRun 1 l a r
    0 2 (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)

theorem lookupRun_cost_le [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (lookupRun x t).2 ≤ 3 * t.height + 1 := by
  simpa only [lookupRun] using HeightBalance.lookupRun_cost_le ltRun x t 1
    (fun _ _ => Nat.le_refl _)

theorem memberRun_cost_le [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (memberRun x t).2 ≤ 3 * t.height + 1 := by
  simpa only [memberRun] using HeightBalance.memberRun_cost_le ltRun x t 1
    (fun _ _ => Nat.le_refl _)

theorem insertRun_cost_le [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (insertRun x t).2 ≤ 27 * t.height + 6 := by
  simpa only [insertRun, Nat.add_assoc] using
    HeightBalance.insertRun_cost_le 0 heightRun combineRun ltRun 1 x t 0 2 1
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

theorem splitMaxRun_cost_le (t : BinaryTree (α × Nat)) :
    (splitMaxRun t).2 ≤ 25 * t.height + 1 := by
  simpa only [splitMaxRun] using HeightBalance.splitMaxRun_cost_le 0 heightRun combineRun 1 t
    0 2 (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)

theorem splitMaxRun_cost_le_of_ne_nil (t : BinaryTree (α × Nat)) (hne : t ≠ .nil) :
    (splitMaxRun t).2 ≤ 25 * t.height := by
  simpa only [splitMaxRun] using
    HeightBalance.splitMaxRun_cost_le_of_ne_nil 0 heightRun combineRun 1 t
      0 2 (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) hne

theorem deleteRun_cost_le [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat)) :
    (deleteRun x t).2 ≤ 27 * t.height + 1 := by
  simpa only [deleteRun] using
    HeightBalance.deleteRun_cost_le 0 heightRun combineRun ltRun 1 x t 0 2 1
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

theorem memberRun_correct [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (memberRun x t).1 = true ↔ x ∈ Trees.setTree (Trees.Cached.erase t) :=
  HeightBalance.memberRun_correct ltRun x t (fun _ _ => rfl) strict

theorem insertRun_valid [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.Valid t) :
    Trees.AVL.Valid (insertRun x t).1 ∧
      ((insertRun x t).1.height = t.height ∨ (insertRun x t).1.height = t.height + 1) := by
  rw [insertRun_value]
  exact Trees.AVL.valid_insert x t hv

theorem splitMaxRun_valid (t t' : BinaryTree (α × Nat)) (m : α)
    (returned : (splitMaxRun t).1 = some (t', m)) (hv : Trees.AVL.Valid t) :
    Trees.AVL.Valid t' ∧ (t.height = t'.height ∨ t.height = t'.height + 1) :=
  Trees.AVL.valid_splitMaxOption t t' m ((splitMaxRun_value t).symm.trans returned) hv

theorem deleteRun_valid [LT α] [DecidableLT α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.Valid t) :
    Trees.AVL.Valid (deleteRun x t).1 ∧
      (t.height = (deleteRun x t).1.height ∨ t.height = (deleteRun x t).1.height + 1) := by
  rw [deleteRun_value]
  exact Trees.AVL.valid_delete x t hv

theorem insertRun_setValid [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.SetValid t) : Trees.AVL.SetValid (insertRun x t).1 := by
  rw [insertRun_value]
  exact Trees.AVL.set_laws.insert_valid x t hv

theorem deleteRun_setValid [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.SetValid t) : Trees.AVL.SetValid (deleteRun x t).1 := by
  rw [deleteRun_value]
  exact Trees.AVL.set_laws.delete_valid x t hv

theorem insertRun_mem [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.SetValid t) (y : α) :
    y ∈ Trees.setTree (Trees.Cached.erase (insertRun x t).1) ↔
      y = x ∨ y ∈ Trees.setTree (Trees.Cached.erase t) := by
  rw [insertRun_value]
  exact Trees.AVL.set_laws.insert x t hv y

theorem deleteRun_mem [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (hv : Trees.AVL.SetValid t) (y : α) :
    y ∈ Trees.setTree (Trees.Cached.erase (deleteRun x t).1) ↔
      y ≠ x ∧ y ∈ Trees.setTree (Trees.Cached.erase t) := by
  rw [deleteRun_value]
  exact Trees.AVL.set_laws.delete x t hv y

end Resources.AVL

import Applications.Trees.AVL.Basic
import Applications.Trees.HeightBalance.Rebalance

/-! Ordinary AVL local repair is the tolerance-one specialization of the
complete-summary height-balancing algebra. The existing AVL carrier, reader,
constructor and invariant retain their original definitions. Source and
statement assessment: `docs/research/fdsa-height-rebalance.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u
variable {α : Type u}

/-- The existing height algebra, with identity height observation. -/
def heightAnnotation : HeightBalance.HeightAnnotation α Nat where
  empty := 0
  combine := heightCombine
  height := id
  height_empty := rfl
  height_combine := by intros; rfl

@[simp] theorem ht_heightAnnotation (t : BinaryTree (α × Nat)) :
    HeightBalance.ht heightAnnotation t = ht t := rfl

@[simp] theorem node_heightAnnotation (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    HeightBalance.node heightAnnotation l a r = node l a r := rfl

@[simp] theorem cacheValid_heightAnnotation (t : BinaryTree (α × Nat)) :
    HeightBalance.CacheValid heightAnnotation t ↔ CacheValid t := Iff.rfl

/-- The generic shape predicate at tolerance one is the existing AVL owner. -/
theorem balancedD_one_iff (t : BinaryTree α) :
    HeightBalance.BalancedD 1 t ↔ Balanced t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [HeightBalance.balancedD_node, balanced_node, ihl, ihr]

theorem validD_one_iff (t : BinaryTree (α × Nat)) :
    HeightBalance.ValidD heightAnnotation 1 t ↔ Valid t := by
  simp only [HeightBalance.validD_iff, valid_iff, balancedD_one_iff,
    cacheValid_heightAnnotation]

/-- For the height-only instance, the complete cache equation becomes the
source's equation in actual child heights, using recursive cache correctness. -/
theorem validD_node_actual_iff (d : Nat) (a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    HeightBalance.ValidD heightAnnotation d (.node (a, n) l r) ↔
      HeightBalance.ValidD heightAnnotation d l ∧
      HeightBalance.ValidD heightAnnotation d r ∧
      |(l.height : Int) - (r.height : Int)| ≤ (d : Int) ∧
      n = max l.height r.height + 1 := by
  rw [HeightBalance.validD_node_iff]
  constructor
  · rintro ⟨hl, hr, hbal, hn⟩
    refine ⟨hl, hr, hbal, ?_⟩
    change n = max (ht l) (ht r) + 1 at hn
    simpa only [ht_eq_height_of_cacheValid l hl.2,
      ht_eq_height_of_cacheValid r hr.2] using hn
  · rintro ⟨hl, hr, hbal, hn⟩
    refine ⟨hl, hr, hbal, ?_⟩
    change n = max (ht l) (ht r) + 1
    simpa only [ht_eq_height_of_cacheValid l hl.2,
      ht_eq_height_of_cacheValid r hr.2] using hn

/-- A positive integer tolerance is transported through its exact natural
representative; negative integer tolerances are not silently truncated. -/
theorem validD_integer_node_iff (D : Int) (hD : 1 ≤ D) (a : α) (n : Nat)
    (l r : BinaryTree (α × Nat)) :
    HeightBalance.ValidD heightAnnotation D.toNat (.node (a, n) l r) ↔
      HeightBalance.ValidD heightAnnotation D.toNat l ∧
      HeightBalance.ValidD heightAnnotation D.toNat r ∧
      |(l.height : Int) - (r.height : Int)| ≤ D ∧
      n = max l.height r.height + 1 := by
  simpa only [(HeightBalance.int_tolerance_toNat D hD).2] using
    validD_node_actual_iff D.toNat a n l r

/-- Repair a possible extra level on the left, using stored heights. -/
def balL (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    BinaryTree (α × Nat) := HeightBalance.balL heightAnnotation 1 l a r

/-- Repair a possible extra level on the right, using the direct right program. -/
def balR (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    BinaryTree (α × Nat) := HeightBalance.balR heightAnnotation 1 l a r

theorem left_ne_nil_of_trigger (l r : BinaryTree (α × Nat))
    (h : ht l = ht r + 2) : l ≠ .nil :=
  HeightBalance.left_ne_nil_of_trigger heightAnnotation 1 l r
    (by simpa only [ht_heightAnnotation, Nat.add_assoc] using h)

theorem right_ne_nil_of_trigger (l r : BinaryTree (α × Nat))
    (h : ht r = ht l + 2) : r ≠ .nil :=
  HeightBalance.right_ne_nil_of_trigger heightAnnotation 1 l r
    (by simpa only [ht_heightAnnotation, Nat.add_assoc] using h)

theorem ne_nil_of_ht_lt (l r : BinaryTree (α × Nat))
    (h : ht l < ht r) : r ≠ .nil :=
  HeightBalance.ne_nil_of_ht_lt heightAnnotation l r h

theorem balL_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (h : ht l ≠ ht r + 2) :
    balL l a r = node l a r := by
  exact HeightBalance.balL_of_ne heightAnnotation 1 l a r
    (by simpa only [ht_heightAnnotation, Nat.add_assoc] using h)

theorem balR_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (h : ht r ≠ ht l + 2) :
    balR l a r = node l a r := by
  exact HeightBalance.balR_of_ne heightAnnotation 1 l a r
    (by simpa only [ht_heightAnnotation, Nat.add_assoc] using h)

theorem balL_single (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (B : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (h : n = ht C + 2) (hs : ht B ≤ ht A) :
    balL (.node (a, n) A B) c C = node A a (node B c C) := by
  exact HeightBalance.balL_single heightAnnotation 1 A a n B c C
    (by simpa only [ht_heightAnnotation, ht_node, Nat.add_assoc] using h) hs

theorem balL_double (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (h : n = ht C + 2) (hs : ht A < m) :
    balL (.node (a, n) A (.node (b, m) P Q)) c C =
      node (node A a P) b (node Q c C) := by
  exact HeightBalance.balL_double heightAnnotation 1 A a n P b m Q c C
    (by simpa only [ht_heightAnnotation, ht_node, Nat.add_assoc] using h) hs

theorem balR_single (A : BinaryTree (α × Nat)) (a : α)
    (B : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (h : n = ht A + 2) (hs : ht B ≤ ht C) :
    balR A a (.node (c, n) B C) = node (node A a B) c C := by
  exact HeightBalance.balR_single heightAnnotation 1 A a B c n C
    (by simpa only [ht_heightAnnotation, ht_node, Nat.add_assoc] using h) hs

theorem balR_double (A : BinaryTree (α × Nat)) (a : α)
    (P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (h : n = ht A + 2) (hs : ht C < m) :
    balR A a (.node (c, n) (.node (b, m) P Q) C) =
      node (node A a P) b (node Q c C) := by
  exact HeightBalance.balR_double heightAnnotation 1 A a P b m Q c n C
    (by simpa only [ht_heightAnnotation, ht_node, Nat.add_assoc] using h) hs

theorem inorder_balL (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    Trees.inorder (Cached.erase (balL l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) :=
  HeightBalance.inorder_balL heightAnnotation 1 l a r

theorem inorder_balR (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    Trees.inorder (Cached.erase (balR l a r)) =
      Trees.inorder (Cached.erase l) ++ (a :: Trees.inorder (Cached.erase r)) :=
  HeightBalance.inorder_balR heightAnnotation 1 l a r

theorem cacheValid_balL (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r) :
    CacheValid (balL l a r) := HeightBalance.cacheValid_balL heightAnnotation 1 l a r hl hr

theorem cacheValid_balR (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r) :
    CacheValid (balR l a r) := HeightBalance.cacheValid_balR heightAnnotation 1 l a r hl hr

/-- The single-rotation tie keeps the larger actual-height alternative. -/
theorem height_balL_single (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (B : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (hl : CacheValid (.node (a, n) A B)) (hr : CacheValid C)
    (h : (BinaryTree.node (a, n) A B).height = C.height + 2)
    (hs : ht B ≤ ht A) :
    (balL (.node (a, n) A B) c C).height =
      if B.height = A.height then C.height + 3 else C.height + 2 := by
  simpa only [balL, Nat.add_assoc] using
    HeightBalance.height_balL_single heightAnnotation 1 A a n B c C
      (by decide) hl hr (by simpa only [Nat.add_assoc] using h) hs

theorem height_balR_single (A : BinaryTree (α × Nat)) (a : α)
    (B : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (hl : CacheValid A) (hr : CacheValid (.node (c, n) B C))
    (h : (BinaryTree.node (c, n) B C).height = A.height + 2)
    (hs : ht B ≤ ht C) :
    (balR A a (.node (c, n) B C)).height =
      if B.height = C.height then A.height + 3 else A.height + 2 := by
  simpa only [balR, Nat.add_assoc] using
    HeightBalance.height_balR_single heightAnnotation 1 A a B c n C
      (by decide) hl hr (by simpa only [Nat.add_assoc] using h) hs

theorem height_balL_double (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (B : BinaryTree (α × Nat)) (c : α) (C : BinaryTree (α × Nat))
    (hl : CacheValid (.node (a, n) A B)) (hr : CacheValid C)
    (h : (BinaryTree.node (a, n) A B).height = C.height + 2)
    (hs : ht A < ht B) :
    (balL (.node (a, n) A B) c C).height = C.height + 2 := by
  simpa only [balL, Nat.add_assoc] using
    HeightBalance.height_balL_double heightAnnotation 1 A a n B c C
      (by decide) hl hr (by simpa only [Nat.add_assoc] using h) hs

theorem height_balR_double (A : BinaryTree (α × Nat)) (a : α)
    (B : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (hl : CacheValid A) (hr : CacheValid (.node (c, n) B C))
    (h : (BinaryTree.node (c, n) B C).height = A.height + 2)
    (hs : ht C < ht B) :
    (balR A a (.node (c, n) B C)).height = A.height + 2 := by
  simpa only [balR, Nat.add_assoc] using
    HeightBalance.height_balR_double heightAnnotation 1 A a B c n C
      (by decide) hl hr (by simpa only [Nat.add_assoc] using h) hs

/-- Actual height needs cache correctness, but does not need child balance. -/
theorem height_balL_of_eq (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r)
    (h : l.height = r.height + 2) :
    (balL l a r).height = r.height + 2 ∨ (balL l a r).height = r.height + 3 := by
  simpa only [balL, Nat.add_assoc] using
    HeightBalance.height_balL_of_eq heightAnnotation 1 l a r (by decide) hl hr
      (by simpa only [Nat.add_assoc] using h)

theorem height_balR_of_eq (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r)
    (h : r.height = l.height + 2) :
    (balR l a r).height = l.height + 2 ∨ (balR l a r).height = l.height + 3 := by
  simpa only [balR, Nat.add_assoc] using
    HeightBalance.height_balR_of_eq heightAnnotation 1 l a r (by decide) hl hr
      (by simpa only [Nat.add_assoc] using h)

theorem height_balL_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r)
    (h : l.height ≠ r.height + 2) :
    (balL l a r).height = max l.height r.height + 1 :=
  HeightBalance.height_balL_of_ne heightAnnotation 1 l a r hl hr
    (by simpa only [Nat.add_assoc] using h)

theorem height_balR_of_ne (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : CacheValid l) (hr : CacheValid r)
    (h : r.height ≠ l.height + 2) :
    (balR l a r).height = max l.height r.height + 1 :=
  HeightBalance.height_balR_of_ne heightAnnotation 1 l a r hl hr
    (by simpa only [Nat.add_assoc] using h)

theorem valid_balL (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : Valid l) (hr : Valid r)
    (hlo : r.height - 1 ≤ l.height) (hhi : l.height ≤ r.height + 2) :
    Valid (balL l a r) := by
  apply (validD_one_iff _).mp
  exact HeightBalance.validD_balL heightAnnotation 1 l a r (by decide)
    ((validD_one_iff l).mpr hl) ((validD_one_iff r).mpr hr) hlo
    (by simpa only [Nat.add_assoc] using hhi)

theorem valid_balR (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) (hl : Valid l) (hr : Valid r)
    (hlo : l.height - 1 ≤ r.height) (hhi : r.height ≤ l.height + 2) :
    Valid (balR l a r) := by
  apply (validD_one_iff _).mp
  exact HeightBalance.validD_balR heightAnnotation 1 l a r (by decide)
    ((validD_one_iff l).mpr hl) ((validD_one_iff r).mpr hr) hlo
    (by simpa only [Nat.add_assoc] using hhi)

/-- In the ordinary left double diagram, at least one middle grandchild
reaches the outer/short height. It need not be both grandchildren. -/
theorem double_middle_heights_left (A : BinaryTree (α × Nat)) (a : α) (n : Nat)
    (P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q C : BinaryTree (α × Nat))
    (hv : Valid (.node (a, n) A (.node (b, m) P Q)))
    (hh : (BinaryTree.node (a, n) A (.node (b, m) P Q)).height = C.height + 2)
    (hs : ht A < ht (.node (b, m) P Q)) :
    A.height = C.height ∧ max P.height Q.height = C.height ∧
      (P.height = C.height ∨ Q.height = C.height) := by
  have hparts := (valid_node_iff a n A (.node (b, m) P Q)).mp hv
  have hbal := (height_balance_iff _ _).mp hparts.2.2.1
  have hs' : A.height < max P.height Q.height + 1 := by
    simpa only [ht_eq_height A hparts.1,
      ht_eq_height _ hparts.2.1, BinaryTree.height] using hs
  have hb : max P.height Q.height + 1 ≤ A.height + 1 := hbal.2
  have hh' : max A.height (max P.height Q.height + 1) + 1 = C.height + 1 + 1 := by
    simpa only [BinaryTree.height, Nat.add_assoc] using hh
  have diagram := HeightBalance.double_rotation_height_bounds
    1 A.height P.height Q.height C.height (by decide) hh' hs' hb
  have hm := diagram.1
  have hlo := diagram.2.1
  have hhi := diagram.2.2.1
  omega

/-- Direct right-oriented counterpart of the ordinary middle-height diagram. -/
theorem double_middle_heights_right (A P : BinaryTree (α × Nat)) (b : α) (m : Nat)
    (Q : BinaryTree (α × Nat)) (c : α) (n : Nat) (C : BinaryTree (α × Nat))
    (hv : Valid (.node (c, n) (.node (b, m) P Q) C))
    (hh : (BinaryTree.node (c, n) (.node (b, m) P Q) C).height = A.height + 2)
    (hs : ht C < ht (.node (b, m) P Q)) :
    C.height = A.height ∧ max P.height Q.height = A.height ∧
      (P.height = A.height ∨ Q.height = A.height) := by
  have hparts := (valid_node_iff c n (.node (b, m) P Q) C).mp hv
  have hbal := (height_balance_iff _ _).mp hparts.2.2.1
  have hs' : C.height < max Q.height P.height + 1 := by
    have h : C.height < max P.height Q.height + 1 := by
      simpa only [ht_eq_height C hparts.2.1,
        ht_eq_height _ hparts.1, BinaryTree.height] using hs
    omega
  have hb : max Q.height P.height + 1 ≤ C.height + 1 := by
    have h := hbal.1
    change max P.height Q.height + 1 ≤ C.height + 1 at h
    omega
  have hh' : max C.height (max Q.height P.height + 1) + 1 = A.height + 1 + 1 := by
    change max (max P.height Q.height + 1) C.height + 1 = A.height + 2 at hh
    omega
  have diagram := HeightBalance.double_rotation_height_bounds
    1 C.height Q.height P.height A.height (by decide) hh' hs' hb
  have hm := diagram.1
  have hlo := diagram.2.1
  have hhi := diagram.2.2.1
  omega

end Trees.AVL

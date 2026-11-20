import Applications.Search.BinomialQueue.Core
import Applications.Trees.BasicObservations
import Applications.Sequences.Multiplicity
import Mathlib.Algebra.Order.Group.Multiset

/-!
Permutation-closed occurrence relations for every raw binomial tree and forest.
The existing preorder observation retains repetitions. Proper outer shapes are
enough for the linking/merging occurrence laws; no key-order law is used here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.BinomialQueue

universe u v
variable {K : Type u} {L : Type v}

abbrev treeContents (t : BinaryTree K) : List K := Trees.preorder t

def contents : Queue K → List K
  | [] => []
  | t :: q => treeContents t ++ contents q

def mass (q : Queue K) : Nat := (q.map BinaryTree.numNodes).sum

def occupied : BinaryTree K → Bool
  | .nil => false
  | .node _ _ _ => true

def occupancy (q : Queue K) : List Bool := q.map occupied

/-- Only the outer right subtree is constrained. This is not rank validity. -/
def Proper : BinaryTree K → Prop
  | .nil => True
  | .node _ _ r => r = .nil

inductive TreeElems : BinaryTree K → List K → Prop where
  | nil : TreeElems .nil []
  | node {x : K} {l r : BinaryTree K} {bl br b : List K} :
      TreeElems l bl → TreeElems r br → b.Perm (x :: bl ++ br) →
      TreeElems (.node x l r) b

inductive QueueElems : Queue K → List K → Prop where
  | nil : QueueElems [] []
  | cons {t : BinaryTree K} {q : Queue K} {bt bq b : List K} :
      TreeElems t bt → QueueElems q bq → b.Perm (bt ++ bq) →
      QueueElems (t :: q) b

abbrev Abs (q : Queue K) (xs : List K) := QueueElems q xs

@[simp] theorem contents_nil : contents ([] : Queue K) = [] := rfl

@[simp] theorem contents_cons (t : BinaryTree K) (q : Queue K) :
    contents (t :: q) = treeContents t ++ contents q := rfl

theorem contents_append (p q : Queue K) : contents (p ++ q) = contents p ++ contents q := by
  induction p with
  | nil => rfl
  | cons t p ih => simp [ih, List.append_assoc]

@[simp] theorem mass_nil : mass ([] : Queue K) = 0 := rfl

@[simp] theorem mass_cons (t : BinaryTree K) (q : Queue K) :
    mass (t :: q) = t.numNodes + mass q := rfl

theorem mass_append (p q : Queue K) : mass (p ++ q) = mass p + mass q := by
  induction p with
  | nil => simp
  | cons t p ih => simp [ih, Nat.add_assoc]

theorem contents_length (q : Queue K) : (contents q).length = mass q := by
  induction q with
  | nil => rfl
  | cons t q ih => simp [treeContents, Trees.preorder_length, ih]

theorem contents_map (f : K → L) (q : Queue K) :
    contents (q.map (BinaryTree.map f)) = (contents q).map f := by
  induction q with
  | nil => rfl
  | cons t q ih => simp [treeContents, Trees.preorder_map, ih]

@[simp] theorem occupied_nil : occupied (.nil : BinaryTree K) = false := rfl

@[simp] theorem occupied_node (x : K) (a b : BinaryTree K) :
    occupied (.node x a b) = true := rfl

@[simp] theorem occupied_eq_false (t : BinaryTree K) : occupied t = false ↔ t = .nil := by
  cases t <;> simp [occupied]

@[simp] theorem occupied_eq_true (t : BinaryTree K) : occupied t = true ↔ t ≠ .nil := by
  cases t <;> simp [occupied]

@[simp] theorem occupancy_nil : occupancy ([] : Queue K) = [] := rfl

@[simp] theorem occupancy_cons (t : BinaryTree K) (q : Queue K) :
    occupancy (t :: q) = occupied t :: occupancy q := rfl

@[simp] theorem occupancy_length (q : Queue K) : (occupancy q).length = q.length := by
  simp [occupancy]

@[simp] theorem proper_nil : Proper (.nil : BinaryTree K) := trivial

@[simp] theorem proper_node (x : K) (a b : BinaryTree K) :
    Proper (.node x a b) ↔ b = .nil := Iff.rfl

theorem tree_elems_iff (t : BinaryTree K) (xs : List K) :
    TreeElems t xs ↔ xs.Perm (treeContents t) := by
  constructor
  · intro h
    induction h with
    | nil => exact List.Perm.refl _
    | node _ _ hp ihl ihr => exact hp.trans ((ihl.append ihr).cons _)
  · induction t generalizing xs with
    | nil => intro h; simpa using (List.perm_nil.mp h ▸ TreeElems.nil)
    | node x l r ihl ihr =>
        intro h
        exact TreeElems.node (ihl _ (List.Perm.refl _))
          (ihr _ (List.Perm.refl _)) h

theorem queue_elems_iff (q : Queue K) (xs : List K) :
    QueueElems q xs ↔ xs.Perm (contents q) := by
  constructor
  · intro h
    induction h with
    | nil => exact List.Perm.refl _
    | cons ht _ hp ih => exact hp.trans (((tree_elems_iff _ _).mp ht).append ih)
  · induction q generalizing xs with
    | nil => intro h; simpa using (List.perm_nil.mp h ▸ QueueElems.nil)
    | cons t q ih =>
        intro h
        exact QueueElems.cons ((tree_elems_iff _ _).mpr (List.Perm.refl _))
          (ih _ (List.Perm.refl _)) h

theorem tree_elems_contents (t : BinaryTree K) : TreeElems t (treeContents t) :=
  (tree_elems_iff _ _).mpr (List.Perm.refl _)

theorem queue_elems_contents (q : Queue K) : Abs q (contents q) :=
  (queue_elems_iff _ _).mpr (List.Perm.refl _)

theorem tree_elems_ext (t : BinaryTree K) (a b : List K)
    (hab : a.Perm b) (ha : TreeElems t a) : TreeElems t b :=
  (tree_elems_iff _ _).mpr (hab.symm.trans ((tree_elems_iff _ _).mp ha))

theorem tree_perm (t : BinaryTree K) (a b : List K)
    (ha : TreeElems t a) (hb : TreeElems t b) : a.Perm b :=
  ((tree_elems_iff _ _).mp ha).trans ((tree_elems_iff _ _).mp hb).symm

theorem priqueue_elems_ext (q : Queue K) (a b : List K)
    (hab : a.Perm b) (ha : Abs q a) : Abs q b :=
  (queue_elems_iff _ _).mpr (hab.symm.trans ((queue_elems_iff _ _).mp ha))

theorem abs_perm_raw (q : Queue K) (a b : List K)
    (ha : Abs q a) (hb : Abs q b) : a.Perm b :=
  ((queue_elems_iff _ _).mp ha).trans ((queue_elems_iff _ _).mp hb).symm

theorem tree_can_relate (t : BinaryTree K) : ∃ xs, TreeElems t xs :=
  ⟨treeContents t, tree_elems_contents t⟩

theorem can_relate_raw (q : Queue K) : ∃ xs, Abs q xs :=
  ⟨contents q, queue_elems_contents q⟩

theorem empty_relate : Abs (empty : Queue K) [] := QueueElems.nil

theorem treeContents_eq_nil (t : BinaryTree K) : treeContents t = [] ↔ t = .nil := by
  cases t <;> simp [treeContents]

theorem contents_eq_nil (q : Queue K) : contents q = [] ↔ ∀ t ∈ q, t = .nil := by
  induction q with
  | nil => simp
  | cons t q ih => simp [treeContents_eq_nil, ih]

theorem abs_nil_iff (q : Queue K) : Abs q [] ↔ ∀ t ∈ q, t = .nil := by
  change QueueElems q [] ↔ _
  rw [queue_elems_iff, List.nil_perm, contents_eq_nil]

theorem abs_length (q : Queue K) (xs : List K) (h : Abs q xs) : xs.length = mass q :=
  ((queue_elems_iff _ _).mp h).length_eq.trans (contents_length q)

theorem abs_multiset (q : Queue K) (xs : List K) (h : Abs q xs) :
    (xs : Multiset K) = (contents q : Multiset K) :=
  Multiset.coe_eq_coe.mpr ((queue_elems_iff _ _).mp h)

theorem abs_counts [BEq K] (q : Queue K) (xs : List K) (h : Abs q xs) :
    Sequences.Multiplicity.contents xs = Sequences.Multiplicity.contents (contents q) :=
  Sequences.Multiplicity.perm_contents ((queue_elems_iff _ _).mp h)

theorem smash_proper (greater : K → K → Bool) (t u : BinaryTree K) :
    Proper (smash greater t u) := by
  cases t with
  | nil => simp
  | node x a r =>
    cases r with
    | node => simp [smash_bad_left]
    | nil =>
      cases u with
      | nil => simp
      | node y b s =>
        cases s with
        | node => simp [smash_bad_right]
        | nil => rw [smash_nodes]; split <;> exact rfl

theorem carry_proper (greater : K → K → Bool) (q : Queue K) (t : BinaryTree K)
    (hq : ∀ u ∈ q, Proper u) (ht : Proper t) :
    ∀ u ∈ carry greater q t, Proper u := by
  induction q generalizing t with
  | nil =>
    cases t with
    | nil => simp [carry]
    | node => simpa [carry] using ht
  | cons u q ih =>
    have hu := hq u (by simp)
    have htail : ∀ v ∈ q, Proper v := fun v hv => hq v (by simp [hv])
    cases u with
    | nil => simpa [carry_hole] using And.intro ht htail
    | node x a b =>
      cases t with
      | nil => simpa [carry_leaf] using hq
      | node y c d =>
        simpa only [carry_occupied, List.mem_cons, forall_eq_or_imp, proper_nil,
          true_and] using ih _ htail (smash_proper greater _ _)

theorem smash_contents_nodes (greater : K → K → Bool) (x y : K)
    (a b : BinaryTree K) :
    (treeContents (smash greater (.node x a .nil) (.node y b .nil))).Perm
      (treeContents (.node x a .nil) ++ treeContents (.node y b .nil)) := by
  rw [smash_nodes]
  split <;> simp only [treeContents, Trees.preorder_node, Trees.preorder_nil, List.append_nil]
  · exact (List.Perm.cons x (List.perm_append_comm.cons y)).trans
      (List.perm_middle.symm.cons x)
  · exact (List.Perm.swap x y _).trans (List.perm_middle.symm.cons x)

theorem carry_contents (greater : K → K → Bool) (q : Queue K) (t : BinaryTree K)
    (hq : ∀ u ∈ q, Proper u) (ht : Proper t) :
    (contents (carry greater q t)).Perm (contents q ++ treeContents t) := by
  induction q generalizing t with
  | nil => cases t <;> simp [carry, treeContents]
  | cons u q ih =>
    have hu := hq u (by simp)
    have htail : ∀ v ∈ q, Proper v := fun v hv => hq v (by simp [hv])
    cases u with
    | nil => simpa [carry_hole, treeContents] using
        (List.perm_append_comm : (treeContents t ++ contents q).Perm
          (contents q ++ treeContents t))
    | node x a b =>
      have hb : b = .nil := hu
      subst b
      cases t with
      | nil => simp [treeContents]
      | node y c d =>
        have hd : d = .nil := ht
        subst d
        have h := (ih _ htail (smash_proper greater _ _)).trans
          ((smash_contents_nodes greater y x c a).append_left (contents q))
        have rot : (contents q ++ (treeContents (.node y c .nil) ++
            treeContents (.node x a .nil))).Perm
            ((treeContents (.node x a .nil) ++ contents q) ++
              treeContents (.node y c .nil)) := by
          simpa only [List.append_assoc] using
            (List.perm_append_comm :
              ((contents q ++ treeContents (.node y c .nil)) ++
                treeContents (.node x a .nil)).Perm
              (treeContents (.node x a .nil) ++
                (contents q ++ treeContents (.node y c .nil))))
        simpa only [carry_occupied, contents_cons, treeContents, Trees.preorder_nil,
          List.nil_append] using h.trans rot

theorem join_proper (greater : K → K → Bool) (p q : Queue K) (c : BinaryTree K)
    (hp : ∀ t ∈ p, Proper t) (hq : ∀ t ∈ q, Proper t) (hc : Proper c) :
    ∀ t ∈ join greater p q c, Proper t := by
  induction p generalizing q c with
  | nil => exact carry_proper greater q c hq hc
  | cons p₀ p ih =>
    have hp₀ := hp p₀ (by simp)
    have hpt : ∀ t ∈ p, Proper t := fun t ht => hp t (by simp [ht])
    cases q with
    | nil => exact carry_proper greater (p₀ :: p) c hp hc
    | cons q₀ q =>
      have hq₀ := hq q₀ (by simp)
      have hqt : ∀ t ∈ q, Proper t := fun t ht => hq t (by simp [ht])
      have recNil := ih q .nil hpt hqt proper_nil
      have recSmash (a b : BinaryTree K) := ih q (smash greater a b) hpt hqt
        (smash_proper greater a b)
      cases p₀ <;> cases q₀ <;> cases c <;>
        simp only [join_holes, join_hole_node_leaf, join_hole_node_node,
          join_node_hole_leaf, join_node_hole_node, join_nodes, List.mem_cons,
          forall_eq_or_imp] <;>
        exact ⟨by assumption, by first | exact recNil | exact recSmash _ _⟩

theorem join_contents (greater : K → K → Bool) (p q : Queue K) (c : BinaryTree K)
    (hp : ∀ t ∈ p, Proper t) (hq : ∀ t ∈ q, Proper t) (hc : Proper c) :
    (contents (join greater p q c)).Perm (treeContents c ++ contents p ++ contents q) := by
  induction p generalizing q c with
  | nil =>
    simpa using (carry_contents greater q c hq hc).trans List.perm_append_comm
  | cons p₀ p ih =>
    have hp₀ := hp p₀ (by simp)
    have hpt : ∀ t ∈ p, Proper t := fun t ht => hp t (by simp [ht])
    cases q with
    | nil =>
      simpa using (carry_contents greater (p₀ :: p) c hp hc).trans List.perm_append_comm
    | cons q₀ q =>
      have hq₀ := hq q₀ (by simp)
      have hqt : ∀ t ∈ q, Proper t := fun t ht => hq t (by simp [ht])
      have recNil := Multiset.coe_eq_coe.mpr (ih q .nil hpt hqt proper_nil)
      have recSmash (a b : BinaryTree K) :=
        Multiset.coe_eq_coe.mpr (ih q (smash greater a b) hpt hqt
          (smash_proper greater a b))
      have sm (x y : K) (a b : BinaryTree K) :=
        Multiset.coe_eq_coe.mpr (smash_contents_nodes greater x y a b)
      apply Multiset.coe_eq_coe.mp
      cases p₀ with
      | nil =>
        cases q₀ with
        | nil =>
          simp only [join_holes, contents_cons, treeContents, Trees.preorder_nil,
            List.nil_append, ← Multiset.coe_add] at recNil ⊢
          rw [recNil]
          ac_rfl
        | node y b s =>
          have hs : s = .nil := hq₀
          subst s
          cases c with
          | nil =>
            simp only [join_hole_node_leaf, contents_cons, treeContents,
              Trees.preorder_nil, List.nil_append, ← Multiset.coe_add] at recNil ⊢
            rw [recNil]
            ac_rfl
          | node z d r =>
            have hr : r = .nil := hc
            subst r
            simp only [join_hole_node_node, contents_cons, treeContents,
              Trees.preorder_nil, List.nil_append, ← Multiset.coe_add] at recSmash sm ⊢
            rw [recSmash, sm]
            ac_rfl
      | node x a r =>
        have hr : r = .nil := hp₀
        subst r
        cases q₀ with
        | nil =>
          cases c with
          | nil =>
            simp only [join_node_hole_leaf, contents_cons, treeContents,
              Trees.preorder_nil, List.nil_append, ← Multiset.coe_add] at recNil ⊢
            rw [recNil]
            ac_rfl
          | node z d s =>
            have hs : s = .nil := hc
            subst s
            simp only [join_node_hole_node, contents_cons, treeContents,
              Trees.preorder_nil, List.nil_append, ← Multiset.coe_add] at recSmash sm ⊢
            rw [recSmash, sm]
            ac_rfl
        | node y b s =>
          have hs : s = .nil := hq₀
          subst s
          simp only [join_nodes, contents_cons, ← Multiset.coe_add] at recSmash sm ⊢
          rw [recSmash, sm]
          ac_rfl

end Search.BinomialQueue

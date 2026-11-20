import Applications.Search.BinomialQueue.Contents
import Applications.Resources.BinaryCounter
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log

/-!
Dense rank validity, left-child/right-sibling bounds, and exact mass. The
source permits trailing empty slots. Canonicality and stored slot length are
separate observations, never extra premises hidden inside `priq`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.BinomialQueue

universe u
variable {K : Type u}

section Predicates
variable [LE K]

def pow2heapAux : Nat → K → BinaryTree K → Prop
  | 0, _, .nil => True
  | 0, _, .node _ _ _ => False
  | _ + 1, _, .nil => False
  | n + 1, m, .node k l r =>
      k ≤ m ∧ pow2heapAux n k l ∧ pow2heapAux n m r

def pow2heap (n : Nat) : BinaryTree K → Prop
  | .node m a .nil => pow2heapAux n m a
  | _ => False

def priqFrom (i : Nat) : Queue K → Prop
  | [] => True
  | t :: q => (t = .nil ∨ pow2heap i t) ∧ priqFrom (i + 1) q

abbrev priq (q : Queue K) : Prop := priqFrom 0 q

@[simp] theorem pow2heapAux_zero (m : K) (t : BinaryTree K) :
    pow2heapAux 0 m t ↔ t = .nil := by cases t <;> simp [pow2heapAux]

@[simp] theorem pow2heapAux_succ_nil (n : Nat) (m : K) :
    ¬ pow2heapAux (n + 1) m .nil := id

@[simp] theorem pow2heapAux_succ_node (n : Nat) (m k : K) (l r : BinaryTree K) :
    pow2heapAux (n + 1) m (.node k l r) ↔
      k ≤ m ∧ pow2heapAux n k l ∧ pow2heapAux n m r := Iff.rfl

@[simp] theorem pow2heap_nil (n : Nat) : ¬ pow2heap n (.nil : BinaryTree K) := id

@[simp] theorem pow2heap_node (n : Nat) (m : K) (a : BinaryTree K) :
    pow2heap n (.node m a .nil) ↔ pow2heapAux n m a := Iff.rfl

theorem pow2heap_iff (n : Nat) (t : BinaryTree K) :
    pow2heap n t ↔ ∃ m a, t = .node m a .nil ∧ pow2heapAux n m a := by
  cases t with
  | nil => simp [pow2heap]
  | node m a r => cases r <;> simp [pow2heap]

theorem pow2heap_proper {n : Nat} {t : BinaryTree K} (h : pow2heap n t) : Proper t := by
  obtain ⟨m, a, rfl, _⟩ := (pow2heap_iff _ _).mp h
  rfl

theorem pow2heap_ne_nil {n : Nat} {t : BinaryTree K} (h : pow2heap n t) : t ≠ .nil := by
  rintro rfl
  exact h

@[simp] theorem priqFrom_nil (i : Nat) : priqFrom i ([] : Queue K) := trivial

@[simp] theorem priqFrom_cons (i : Nat) (t : BinaryTree K) (q : Queue K) :
    priqFrom i (t :: q) ↔ (t = .nil ∨ pow2heap i t) ∧ priqFrom (i + 1) q := Iff.rfl

theorem priqFrom_append (i : Nat) (p q : Queue K) :
    priqFrom i (p ++ q) ↔ priqFrom i p ∧ priqFrom (i + p.length) q := by
  induction p generalizing i with
  | nil => simp
  | cons t p ih => simp [ih, Nat.add_comm, Nat.add_left_comm, and_assoc]

theorem priqFrom_proper {i : Nat} {q : Queue K} (h : priqFrom i q) :
    ∀ t ∈ q, Proper t := by
  induction q generalizing i with
  | nil => simp
  | cons t q ih =>
    rcases h with ⟨ht, hq⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · rcases ht with rfl | ht
      · exact proper_nil
      · exact pow2heap_proper ht
    · exact ih hq u hu

theorem pow2heapAux_numNodes {n : Nat} {m : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) : t.numNodes + 1 = 2 ^ n := by
  induction n generalizing m t with
  | zero => have ht := (pow2heapAux_zero _ _).mp h; subst t; rfl
  | succ n ih =>
    cases t with
    | nil => exact False.elim h
    | node k l r =>
      have hl := ih h.2.1
      have hr := ih h.2.2
      simp only [BinaryTree.numNodes, Nat.pow_succ]
      omega

theorem pow2heapAux_height {n : Nat} {m : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) : t.height = n := by
  induction n generalizing m t with
  | zero => have ht := (pow2heapAux_zero _ _).mp h; subst t; rfl
  | succ n ih =>
    cases t with
    | nil => exact False.elim h
    | node k l r => simp only [BinaryTree.height, ih h.2.1, ih h.2.2, max_self]

theorem pow2heap_numNodes {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : t.numNodes = 2 ^ n := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2heap_iff _ _).mp h
  simpa using pow2heapAux_numNodes ha

theorem pow2heap_height {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : t.height = n + 1 := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2heap_iff _ _).mp h
  simp [pow2heapAux_height ha]

theorem empty_priq : priq (empty : Queue K) := trivial

theorem abs_perm (q : Queue K) (a b : List K) (_hq : priq q)
    (ha : Abs q a) (hb : Abs q b) : a.Perm b := abs_perm_raw q a b ha hb

theorem can_relate (q : Queue K) (_hq : priq q) : ∃ a, Abs q a := can_relate_raw q

theorem smash_elems (greater : K → K → Bool) (n : Nat) (t u : BinaryTree K)
    (bt bu : List K) (ht : pow2heap n t) (hu : pow2heap n u)
    (hbt : TreeElems t bt) (hbu : TreeElems u bu) :
    TreeElems (smash greater t u) (bt ++ bu) := by
  obtain ⟨x, a, rfl, _⟩ := (pow2heap_iff _ _).mp ht
  obtain ⟨y, b, rfl, _⟩ := (pow2heap_iff _ _).mp hu
  apply (tree_elems_iff _ _).mpr
  exact (((tree_elems_iff _ _).mp hbt).append ((tree_elems_iff _ _).mp hbu)).trans
    (smash_contents_nodes greater x y a b).symm

theorem carry_elems (greater : K → K → Bool) (n : Nat) (q : Queue K)
    (t : BinaryTree K) (eq et : List K) (hq : priqFrom n q)
    (ht : t = .nil ∨ pow2heap n t) (heq : Abs q eq) (het : TreeElems t et) :
    Abs (carry greater q t) (eq ++ et) := by
  have htp : Proper t := ht.elim (fun h => h ▸ proper_nil) pow2heap_proper
  apply (queue_elems_iff _ _).mpr
  exact (((queue_elems_iff _ _).mp heq).append ((tree_elems_iff _ _).mp het)).trans
    (carry_contents greater q t (priqFrom_proper hq) htp).symm

theorem insert_relate (greater : K → K → Bool) (q : Queue K) (al : List K)
    (k : K) (hq : priq q) (hal : Abs q al) : Abs (insert greater k q) (k :: al) := by
  have h := carry_elems greater 0 q (.node k .nil .nil) al [k] hq
    (Or.inr trivial) hal (tree_elems_contents _)
  exact priqueue_elems_ext _ _ _ (by simp) h

theorem join_elems (greater : K → K → Bool) (n : Nat) (p q : Queue K)
    (c : BinaryTree K) (pe qe ce : List K) (hp : priqFrom n p) (hq : priqFrom n q)
    (hc : c = .nil ∨ pow2heap n c) (hpe : Abs p pe) (hqe : Abs q qe)
    (hce : TreeElems c ce) : Abs (join greater p q c) (ce ++ pe ++ qe) := by
  have hcp : Proper c := hc.elim (fun h => h ▸ proper_nil) pow2heap_proper
  apply (queue_elems_iff _ _).mpr
  exact ((((tree_elems_iff _ _).mp hce).append ((queue_elems_iff _ _).mp hpe)).append
    ((queue_elems_iff _ _).mp hqe)).trans
    (join_contents greater p q c (priqFrom_proper hp) (priqFrom_proper hq) hcp).symm

theorem merge_abs (greater : K → K → Bool) (p q : Queue K) (pl ql : List K)
    (hp : priq p) (hq : priq q) (hpl : Abs p pl) (hql : Abs q ql) :
    Abs (merge greater p q) (pl ++ ql) :=
  join_elems greater 0 p q .nil pl ql [] hp hq (Or.inl rfl) hpl hql TreeElems.nil

theorem merge_relate (greater : K → K → Bool) (p q : Queue K) (pl ql al : List K)
    (hp : priq p) (hq : priq q) (hpl : Abs p pl) (hql : Abs q ql)
    (hal : Abs (merge greater p q) al) : al.Perm (pl ++ ql) :=
  abs_perm_raw _ _ _ hal (merge_abs greater p q pl ql hp hq hpl hql)

theorem insert_mass (greater : K → K → Bool) (k : K) (q : Queue K) (hq : priq q) :
    mass (insert greater k q) = mass q + 1 := by
  have h := abs_length _ _ (insert_relate greater q (contents q) k hq (queue_elems_contents q))
  simpa [contents_length] using h.symm

theorem merge_mass (greater : K → K → Bool) (p q : Queue K) (hp : priq p) (hq : priq q) :
    mass (merge greater p q) = mass p + mass q := by
  have h := abs_length _ _ (merge_abs greater p q (contents p) (contents q) hp hq
    (queue_elems_contents p) (queue_elems_contents q))
  simpa [contents_length] using h.symm

end Predicates

section Ordered
variable [Preorder K]

theorem pow2heapAux_mono {n : Nat} {m M : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) (hm : m ≤ M) : pow2heapAux n M t := by
  induction n generalizing m M t with
  | zero => simpa only [pow2heapAux_zero] using h
  | succ n ih =>
    cases t with
    | nil => exact False.elim h
    | node k l r => exact ⟨h.1.trans hm, h.2.1, ih h.2.2 hm⟩

theorem pow2heapAux_bound {n : Nat} {m : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) : ∀ x ∈ treeContents t, x ≤ m := by
  induction n generalizing m t with
  | zero => have ht := (pow2heapAux_zero _ _).mp h; subst t; simp [treeContents]
  | succ n ih =>
    cases t with
    | nil => exact False.elim h
    | node k l r =>
      intro x hx
      simp only [treeContents, Trees.preorder_node, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact h.1
      · exact (ih h.2.1 x hx).trans h.1
      · exact ih h.2.2 x hx

theorem pow2heap_bound {n : Nat} {m : K} {a : BinaryTree K}
    (h : pow2heap n (.node m a .nil)) :
    ∀ x ∈ treeContents (.node m a .nil), x ≤ m := by
  intro x hx
  simp only [treeContents, Trees.preorder_node, Trees.preorder_nil,
    List.append_nil, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · exact pow2heapAux_bound h x hx

variable [Std.Total (fun x y : K => x ≤ y)]
variable (greater : K → K → Bool)
variable (hgreater : ∀ x y, greater x y = true ↔ ¬ x ≤ y)
include hgreater

theorem smash_valid (n : Nat) (t u : BinaryTree K)
    (ht : pow2heap n t) (hu : pow2heap n u) :
    pow2heap (n + 1) (smash greater t u) := by
  obtain ⟨x, a, rfl, ha⟩ := (pow2heap_iff _ _).mp ht
  obtain ⟨y, b, rfl, hb⟩ := (pow2heap_iff _ _).mp hu
  rw [smash_nodes]
  split
  · rename_i h
    have hyx : y ≤ x := (total_of (fun a b : K => a ≤ b) x y).resolve_left
      ((hgreater x y).mp h)
    exact ⟨hyx, hb, ha⟩
  · rename_i h
    have hxy : x ≤ y := by
      by_contra hn
      exact h ((hgreater x y).mpr hn)
    exact ⟨hxy, ha, hb⟩

theorem carry_valid (n : Nat) (q : Queue K) (t : BinaryTree K)
    (hq : priqFrom n q) (ht : t = .nil ∨ pow2heap n t) :
    priqFrom n (carry greater q t) := by
  induction q generalizing n t with
  | nil =>
    cases t with
    | nil => trivial
    | node => exact ⟨ht, trivial⟩
  | cons u q ih =>
    rcases hq with ⟨hu, hq⟩
    cases u with
    | nil => simpa only [carry_hole, priqFrom_cons] using And.intro ht hq
    | node x a b =>
      cases t with
      | nil => simpa only [carry_leaf, priqFrom_cons] using And.intro hu hq
      | node y c d =>
        refine ⟨Or.inl rfl, ih (n + 1) _ hq (Or.inr ?_)⟩
        exact smash_valid greater hgreater n _ _
          (ht.resolve_left (by simp)) (hu.resolve_left (by simp))

theorem insert_priq (k : K) (q : Queue K) (hq : priq q) : priq (insert greater k q) :=
  carry_valid greater hgreater 0 q (.node k .nil .nil) hq (Or.inr trivial)

theorem join_valid (n : Nat) (p q : Queue K) (c : BinaryTree K)
    (hp : priqFrom n p) (hq : priqFrom n q) (hc : c = .nil ∨ pow2heap n c) :
    priqFrom n (join greater p q c) := by
  induction p generalizing n q c with
  | nil => exact carry_valid greater hgreater n q c hq hc
  | cons p₀ p ih =>
    rcases hp with ⟨hp₀, hpt⟩
    cases q with
    | nil => exact carry_valid greater hgreater n (p₀ :: p) c ⟨hp₀, hpt⟩ hc
    | cons q₀ q =>
      rcases hq with ⟨hq₀, hqt⟩
      have recNil := ih (n + 1) q .nil hpt hqt (Or.inl rfl)
      have recSmash (a b : BinaryTree K) (ha : pow2heap n a) (hb : pow2heap n b) :=
        ih (n + 1) q (smash greater a b) hpt hqt
          (Or.inr (smash_valid greater hgreater n a b ha hb))
      cases p₀ <;> cases q₀ <;> cases c <;>
        simp only [join_holes, join_hole_node_leaf, join_hole_node_node,
          join_node_hole_leaf, join_node_hole_node, join_nodes, priqFrom_cons]
      all_goals constructor
      all_goals first
        | exact hc
        | exact hp₀
        | exact hq₀
        | exact Or.inl trivial
        | exact recNil
        | (apply recSmash <;> first
            | exact hc.resolve_left (by simp)
            | exact hp₀.resolve_left (by simp)
            | exact hq₀.resolve_left (by simp))

theorem merge_priq (p q : Queue K) (hp : priq p) (hq : priq q) :
    priq (merge greater p q) := join_valid greater hgreater 0 p q .nil hp hq (Or.inl rfl)

end Ordered

theorem carry_length_bounds (greater : K → K → Bool) (q : Queue K) (t : BinaryTree K) :
    q.length ≤ (carry greater q t).length ∧ (carry greater q t).length ≤ q.length + 1 := by
  induction q generalizing t with
  | nil => cases t <;> simp [carry]
  | cons u q ih =>
    cases u with
    | nil => simp only [carry_hole, List.length_cons]; omega
    | node x a b =>
      cases t with
      | nil => simp
      | node y c d =>
        have h := ih (smash greater (.node y c d) (.node x a b))
        simp only [carry_occupied, List.length_cons]
        omega

theorem join_length_bounds (greater : K → K → Bool) (p q : Queue K) (c : BinaryTree K) :
    max p.length q.length ≤ (join greater p q c).length ∧
      (join greater p q c).length ≤ max p.length q.length + 1 := by
  induction p generalizing q c with
  | nil => simpa using carry_length_bounds greater q c
  | cons p₀ p ih =>
    cases q with
    | nil => simpa using carry_length_bounds greater (p₀ :: p) c
    | cons q₀ q =>
      have h₁ := ih q .nil
      have h₂ := ih q (smash greater c q₀)
      have h₃ := ih q (smash greater c p₀)
      have h₄ := ih q (smash greater p₀ q₀)
      cases p₀ <;> cases q₀ <;> cases c <;>
        simp only [join_holes, join_hole_node_leaf, join_hole_node_node,
          join_node_hole_leaf, join_node_hole_node, join_nodes, List.length_cons] <;> omega

/-- Empty or a final occupied slot, observed through the existing binary digits. -/
def Canonical (q : Queue K) : Prop := Resources.BinaryCounter.Canonical (occupancy q)

@[simp] theorem canonical_nil : Canonical ([] : Queue K) := trivial

@[simp] theorem canonical_singleton (t : BinaryTree K) : Canonical [t] ↔ t ≠ .nil := by
  simp [Canonical, Resources.BinaryCounter.Canonical]

theorem canonical_cons_nonempty (t : BinaryTree K) (q : Queue K) (hq : q ≠ []) :
    Canonical (t :: q) ↔ Canonical q := by
  apply Resources.BinaryCounter.canonical_cons_nonempty
  intro h
  have he : (occupancy q).length = 0 := congrArg List.length h
  rw [occupancy_length] at he
  exact hq (List.length_eq_zero_iff.mp he)

theorem canonical_append_singleton (p : Queue K) (t : BinaryTree K) :
    Canonical (p ++ [t]) ↔ t ≠ .nil := by
  induction p with
  | nil => exact canonical_singleton t
  | cons u p ih =>
    rw [List.cons_append, canonical_cons_nonempty u (p ++ [t]) (by simp)]
    exact ih

theorem canonical_iff (q : Queue K) :
    Canonical q ↔ q = [] ∨ ∃ p t, q = p ++ [t] ∧ t ≠ .nil := by
  rcases List.eq_nil_or_concat' q with rfl | ⟨p, t, rfl⟩
  · simp
  · constructor
    · intro h
      exact Or.inr ⟨p, t, rfl, (canonical_append_singleton p t).mp h⟩
    · rintro (h | ⟨p', t', h, ht'⟩)
      · simp at h
      · rw [h]
        exact (canonical_append_singleton p' t').mpr ht'

theorem carry_growth_canonical (greater : K → K → Bool) (q : Queue K)
    (t : BinaryTree K) (h : q.length < (carry greater q t).length) :
    Canonical (carry greater q t) := by
  induction q generalizing t with
  | nil =>
    cases t with
    | nil => simp at h
    | node => exact (canonical_singleton _).mpr (by simp)
  | cons u q ih =>
    cases u with
    | nil => simp [carry_hole] at h
    | node x a b =>
      cases t with
      | nil => simp at h
      | node y c d =>
        have hs : q.length < (carry greater q (smash greater (.node y c d) (.node x a b))).length := by
          simpa only [carry_occupied, List.length_cons, Nat.succ_lt_succ_iff] using h
        rw [carry_occupied, canonical_cons_nonempty]
        · exact ih _ hs
        · intro he
          rw [he] at hs
          simp at hs

theorem join_growth_canonical (greater : K → K → Bool) (p q : Queue K)
    (c : BinaryTree K) (h : max p.length q.length < (join greater p q c).length) :
    Canonical (join greater p q c) := by
  induction p generalizing q c with
  | nil => exact carry_growth_canonical greater q c (by simpa using h)
  | cons p₀ p ih =>
    cases q with
    | nil => exact carry_growth_canonical greater (p₀ :: p) c (by simpa using h)
    | cons q₀ q =>
      have step (head carryTree : BinaryTree K)
          (heq : join greater (p₀ :: p) (q₀ :: q) c = head :: join greater p q carryTree) :
          Canonical (join greater (p₀ :: p) (q₀ :: q) c) := by
        rw [heq] at h ⊢
        have ht : max p.length q.length < (join greater p q carryTree).length := by
          simp only [List.length_cons] at h
          omega
        rw [canonical_cons_nonempty]
        · exact ih q carryTree ht
        · intro he
          rw [he] at ht
          simp at ht
      cases p₀ <;> cases q₀ <;> cases c <;> exact step _ _ rfl

theorem smash_ne_nil (greater : K → K → Bool) (t u : BinaryTree K)
    (ht : Proper t) (hu : Proper u) (hnt : t ≠ .nil) (hnu : u ≠ .nil) :
    smash greater t u ≠ .nil := by
  cases t with
  | nil => exact False.elim (hnt rfl)
  | node x a r =>
    have hr : r = .nil := ht
    subst r
    cases u with
    | nil => exact False.elim (hnu rfl)
    | node y b s =>
      have hs : s = .nil := hu
      subst s
      rw [smash_nodes]
      split <;> simp

theorem occupancy_carry (greater : K → K → Bool) (q : Queue K) (t : BinaryTree K)
    (hq : ∀ u ∈ q, Proper u) (ht : Proper t) (hnt : t ≠ .nil) :
    occupancy (carry greater q t) = Resources.BinaryCounter.inc (occupancy q) := by
  induction q generalizing t with
  | nil => cases t <;> simp_all [carry, Resources.BinaryCounter.inc]
  | cons u q ih =>
    have hu := hq u (by simp)
    have htail : ∀ v ∈ q, Proper v := fun v hv => hq v (by simp [hv])
    cases u with
    | nil =>
      rw [carry_hole]
      simp [Resources.BinaryCounter.inc, (occupied_eq_true t).mpr hnt]
    | node x a b =>
      cases t with
      | nil => exact False.elim (hnt rfl)
      | node y c d =>
        simp only [carry_occupied, occupancy_cons, occupied_nil, occupied_node,
          Resources.BinaryCounter.inc]
        rw [ih _ htail (smash_proper greater _ _)
          (smash_ne_nil greater _ _ ht hu hnt (by simp))]

section Mass
variable [LE K]

theorem priqFrom_getElem {i : Nat} {q : Queue K} (hq : priqFrom i q)
    (j : Nat) (hj : j < q.length) : q[j] = .nil ∨ pow2heap (i + j) q[j] := by
  induction q generalizing i j with
  | nil => simp at hj
  | cons t q ih =>
    cases j with
    | zero => simpa using hq.1
    | succ j =>
      have h := ih hq.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem getElem_numNodes {i : Nat} {q : Queue K} (hq : priqFrom i q)
    (j : Nat) (hj : j < q.length) :
    q[j].numNodes = if occupied q[j] then 2 ^ (i + j) else 0 := by
  rcases priqFrom_getElem hq j hj with ht | ht
  · simp [ht]
  · simp [(occupied_eq_true _).mpr (pow2heap_ne_nil ht), pow2heap_numNodes ht]

theorem occupancy_insert (greater : K → K → Bool) (k : K) (q : Queue K) (hq : priq q) :
    occupancy (insert greater k q) = Resources.BinaryCounter.inc (occupancy q) :=
  occupancy_carry greater q (.node k .nil .nil) (priqFrom_proper hq) rfl (by simp)

theorem mass_eq_value {i : Nat} {q : Queue K} (hq : priqFrom i q) :
    mass q = 2 ^ i * Resources.BinaryCounter.value (occupancy q) := by
  induction q generalizing i with
  | nil => simp [Resources.BinaryCounter.value]
  | cons t q ih =>
    rcases hq with ⟨ht, hq⟩
    rcases ht with rfl | ht
    · simp only [mass_cons, BinaryTree.numNodes, Nat.zero_add, occupancy_cons, occupied_nil,
        Resources.BinaryCounter.value, ih hq, Nat.pow_succ, Nat.mul_assoc]
    · have hn := pow2heap_ne_nil ht
      simp only [mass_cons, pow2heap_numNodes ht, occupancy_cons,
        (occupied_eq_true t).mpr hn, Resources.BinaryCounter.value, ih hq,
        Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

theorem mass_lt_pow_length {q : Queue K} (hq : priq q) : mass q < 2 ^ q.length := by
  have h := Resources.BinaryCounter.value_lt_two_pow_length (occupancy q)
  simpa [mass_eq_value hq] using h

theorem size_mass_le_length {q : Queue K} (hq : priq q) : (mass q).size ≤ q.length :=
  Nat.size_le.mpr (mass_lt_pow_length hq)

theorem canonical_mass_lower {q : Queue K} (hq : priq q) (hc : Canonical q) (hn : q ≠ []) :
    2 ^ (q.length - 1) ≤ mass q := by
  obtain ⟨p, t, rfl, ht⟩ := (canonical_iff q).mp hc |>.resolve_left hn
  have hv := ((priqFrom_append 0 p [t]).mp hq).2.1
  have hv' : pow2heap p.length t := by simpa using hv.resolve_left ht
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    mass_append, mass_cons, mass_nil, Nat.add_zero, pow2heap_numNodes hv']
  omega

theorem canonical_length {q : Queue K} (hq : priq q) (hc : Canonical q) :
    q.length = (mass q).size := by
  have upper := size_mass_le_length hq
  by_cases hn : q = []
  · subst q; rfl
  · have lower := Nat.lt_size.mpr (canonical_mass_lower hq hc hn)
    have hp : 0 < q.length := Nat.pos_of_ne_zero (fun he => hn (List.length_eq_zero_iff.mp he))
    omega

theorem canonical_log_length {q : Queue K} (hq : priq q) (hc : Canonical q) (hn : q ≠ []) :
    q.length = Nat.log 2 (mass q) + 1 := by
  have hp : 0 < q.length := Nat.pos_of_ne_zero (fun he => hn (List.length_eq_zero_iff.mp he))
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow (canonical_mass_lower hq hc hn)
    (by simpa [Nat.sub_add_cancel hp] using mass_lt_pow_length hq)
  omega

theorem replicate_nil_valid (i n : Nat) : priqFrom i (List.replicate n (.nil : BinaryTree K)) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih => exact ⟨Or.inl rfl, ih (i + 1)⟩

omit [LE K] in
theorem replicate_nil_mass (n : Nat) : mass (List.replicate n (.nil : BinaryTree K)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

end Mass

section OrderedLength
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable (greater : K → K → Bool)
variable (hgreater : ∀ x y, greater x y = true ↔ ¬ x ≤ y)
include hgreater

theorem insert_length (k : K) (q : Queue K) (hq : priq q) :
    (insert greater k q).length = max q.length (mass q + 1).size := by
  have hv := insert_priq greater hgreater k q hq
  have hlo := (carry_length_bounds greater q (.node k .nil .nil)).1
  have hsize := size_mass_le_length hv
  rw [insert_mass greater k q hq] at hsize
  by_cases hgrow : q.length < (insert greater k q).length
  · have hc := carry_growth_canonical greater q (.node k .nil .nil) hgrow
    have heq := canonical_length hv hc
    rw [insert_mass greater k q hq] at heq
    omega
  · change q.length ≤ (insert greater k q).length at hlo
    omega

theorem merge_length (p q : Queue K) (hp : priq p) (hq : priq q) :
    (merge greater p q).length =
      max (max p.length q.length) (mass p + mass q).size := by
  have hv := merge_priq greater hgreater p q hp hq
  have hlo := (join_length_bounds greater p q .nil).1
  have hsize := size_mass_le_length hv
  rw [merge_mass greater p q hp hq] at hsize
  by_cases hgrow : max p.length q.length < (merge greater p q).length
  · have hc := join_growth_canonical greater p q .nil hgrow
    have heq := canonical_length hv hc
    rw [merge_mass greater p q hp hq] at heq
    omega
  · change max p.length q.length ≤ (merge greater p q).length at hlo
    omega

end OrderedLength

end Search.BinomialQueue

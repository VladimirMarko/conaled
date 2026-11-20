import Applications.Search.OrderedMap.Basic
import Applications.Search.OrderedTree.Comparison
import Applications.Resources.Growth

/-!
# The executed search and insertion paths

The observation pair is `(nonempty node visits, comparator work)`. A measured
Boolean comparator is actually executed in source order: query/root first,
then root/query only when the first answer is false. Only the selected child
runs. Insertion binds its actual recursive answer into the reconstructed tree.
Unit comparators count calls, independently of their internal implementation.
Weighted bounds instead assume a bound on each executed measured comparator,
stated locally for the finite input tree. Logarithmic bounds require an explicit
height contract; ordinary unbalanced insertion provides none.

Nil contributes zero to the primary pair. `lookupInspections` adds the terminal
nil inspection exactly on a missing lookup. These are abstract observations,
not assertions about compiled Nat comparison, heap allocation, or elapsed time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SearchTree
universe u v
variable {κ : Type u} {ν : Type v}

/-- Actual short-circuit search, with comparator work lifted into the second
component and one nonempty visit posted at each reached node. -/
def lookupWithRun (ltRun : κ → κ → Measured Bool Nat) (query : κ) :
    BinaryTree (κ × ν) → Measured (Option ν) (Nat × Nat)
  | .nil => (none, (0, 0))
  | .node binding left right =>
      let body := bind (reweight (fun c => (0, c)) (ltRun query binding.1)) fun less =>
        if less then lookupWithRun ltRun query left
        else bind (reweight (fun c => (0, c)) (ltRun binding.1 query)) fun greater =>
          if greater then lookupWithRun ltRun query right
          else (some binding.2, (0, 0))
      (body.1, body.2 + (1, 0))

/-- Insertion uses precisely the same comparisons and selected path. The
returned recursive tree is used, not replaced by an unrelated unmeasured run. -/
def insertWithRun (ltRun : κ → κ → Measured Bool Nat) (key : κ) (value : ν) :
    BinaryTree (κ × ν) → Measured (BinaryTree (κ × ν)) (Nat × Nat)
  | .nil => (.node (key, value) .nil .nil, (0, 0))
  | .node binding left right =>
      let body := bind (reweight (fun c => (0, c)) (ltRun key binding.1)) fun less =>
        if less then
          bind (insertWithRun ltRun key value left) fun result =>
            pure (.node binding result right)
        else bind (reweight (fun c => (0, c)) (ltRun binding.1 key)) fun greater =>
          if greater then
            bind (insertWithRun ltRun key value right) fun result =>
              pure (.node binding left result)
          else (.node (key, value) left right, (0, 0))
      (body.1, body.2 + (1, 0))

@[simp] theorem lookupWithRun_nil (ltRun : κ → κ → Measured Bool Nat) (q : κ) :
    lookupWithRun (ν := ν) ltRun q .nil = (none, (0, 0)) := rfl

@[simp] theorem insertWithRun_nil (ltRun : κ → κ → Measured Bool Nat) (k : κ) (v : ν) :
    insertWithRun ltRun k v .nil = (.node (k, v) .nil .nil, (0, 0)) := rfl

theorem lookupWithRun_node (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (b : κ × ν) (l r : BinaryTree (κ × ν)) :
    lookupWithRun ltRun q (.node b l r) =
      if (ltRun q b.1).1 then
        ((lookupWithRun ltRun q l).1,
          ((lookupWithRun ltRun q l).2.1 + 1,
            (ltRun q b.1).2 + (lookupWithRun ltRun q l).2.2))
      else if (ltRun b.1 q).1 then
        ((lookupWithRun ltRun q r).1,
          ((lookupWithRun ltRun q r).2.1 + 1,
            (ltRun q b.1).2 + (ltRun b.1 q).2 + (lookupWithRun ltRun q r).2.2))
      else (some b.2, (1, (ltRun q b.1).2 + (ltRun b.1 q).2)) := by
  simp only [lookupWithRun, bind, reweight]
  split <;> simp_all [Prod.add_def, Nat.add_assoc]
  split <;> simp_all

theorem insertWithRun_node (ltRun : κ → κ → Measured Bool Nat) (k : κ) (v : ν)
    (b : κ × ν) (l r : BinaryTree (κ × ν)) :
    insertWithRun ltRun k v (.node b l r) =
      if (ltRun k b.1).1 then
        (.node b (insertWithRun ltRun k v l).1 r,
          ((insertWithRun ltRun k v l).2.1 + 1,
            (ltRun k b.1).2 + (insertWithRun ltRun k v l).2.2))
      else if (ltRun b.1 k).1 then
        (.node b l (insertWithRun ltRun k v r).1,
          ((insertWithRun ltRun k v r).2.1 + 1,
            (ltRun k b.1).2 + (ltRun b.1 k).2 + (insertWithRun ltRun k v r).2.2))
      else (.node (k, v) l r, (1, (ltRun k b.1).2 + (ltRun b.1 k).2)) := by
  simp only [insertWithRun, bind, reweight, pure]
  split <;> simp_all [Prod.add_def, Nat.add_assoc]
  split <;> simp_all

/-- Both operations execute the same path on the same old tree. -/
theorem insertWithRun_work (ltRun : κ → κ → Measured Bool Nat) (k : κ) (v : ν)
    (t : BinaryTree (κ × ν)) :
    (insertWithRun ltRun k v t).2 = (lookupWithRun ltRun k t).2 := by
  induction t with
  | nil => rfl
  | node b l r ihl ihr =>
      rw [insertWithRun_node, lookupWithRun_node]
      split
      · simp only [ihl]
      · split <;> simp only [ihr]

theorem lookupWithRun_visits_le_height (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν)) : (lookupWithRun ltRun q t).2.1 ≤ t.height := by
  induction t with
  | nil => exact Nat.le_refl 0
  | node b l r ihl ihr =>
      rw [lookupWithRun_node]
      have hl := Nat.le_max_left l.height r.height
      have hr := Nat.le_max_right l.height r.height
      split
      · simp only [BinaryTree.height]; omega
      · split <;> simp only [BinaryTree.height] <;> omega

/-- Local comparator bounds refer only to labels present in this finite input,
and allow zero cost. No ordering or correctness premise is needed for the bound. -/
theorem lookupWithRun_work_le_visits (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν)) (K : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ K ∧ (ltRun b.1 q).2 ≤ K) t) :
    (lookupWithRun ltRun q t).2.2 ≤ 2 * K * (lookupWithRun ltRun q t).2.1 := by
  induction t with
  | nil => exact Nat.le_refl 0
  | node b l r ihl ihr =>
      rcases local_bound with ⟨⟨hfirst, hsecond⟩, hl, hr⟩
      have hleft := ihl hl
      have hright := ihr hr
      rw [lookupWithRun_node]
      split
      · dsimp; nlinarith
      · split <;> dsimp <;> nlinarith

theorem lookupWithRun_work_le_height (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν)) (K : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ K ∧ (ltRun b.1 q).2 ≤ K) t) :
    (lookupWithRun ltRun q t).2.2 ≤ 2 * K * t.height :=
  (lookupWithRun_work_le_visits ltRun q t K local_bound).trans
    (Nat.mul_le_mul_left (2 * K) (lookupWithRun_visits_le_height ltRun q t))

theorem insertWithRun_visits_le_height (ltRun : κ → κ → Measured Bool Nat)
    (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    (insertWithRun ltRun k v t).2.1 ≤ t.height := by
  rw [insertWithRun_work]
  exact lookupWithRun_visits_le_height ltRun k t

theorem insertWithRun_work_le_height (ltRun : κ → κ → Measured Bool Nat)
    (k : κ) (v : ν) (t : BinaryTree (κ × ν)) (K : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun k b.1).2 ≤ K ∧ (ltRun b.1 k).2 ≤ K) t) :
    (insertWithRun ltRun k v t).2.2 ≤ 2 * K * t.height := by
  rw [insertWithRun_work]
  exact lookupWithRun_work_le_height ltRun k t K local_bound

/-- Add a chosen price per reached nonempty node to the actual comparator work.
The displayed bound does not include empty inspection or allocation. -/
theorem lookupWithRun_weighted_bound (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν)) (K visitPrice : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ K ∧ (ltRun b.1 q).2 ≤ K) t) :
    visitPrice * (lookupWithRun ltRun q t).2.1 + (lookupWithRun ltRun q t).2.2 ≤
      (visitPrice + 2 * K) * t.height := by
  have hv := Nat.mul_le_mul_left visitPrice (lookupWithRun_visits_le_height ltRun q t)
  have hw := lookupWithRun_work_le_height ltRun q t K local_bound
  nlinarith

/-- Logarithmic work is conditional on both a comparator bound and a separately
supplied logarithmic height bound. It is not a property of arbitrary BSTs. -/
theorem lookupWithRun_log_bound (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν)) (K H : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun q b.1).2 ≤ K ∧ (ltRun b.1 q).2 ≤ K) t)
    (height_bound : t.height ≤ H * Nat.clog 2 (t.numNodes + 1)) :
    (lookupWithRun ltRun q t).2.2 ≤ (2 * K * H) * Nat.clog 2 (t.numNodes + 1) := by
  calc
    (lookupWithRun ltRun q t).2.2 ≤ 2 * K * t.height :=
      lookupWithRun_work_le_height ltRun q t K local_bound
    _ ≤ 2 * K * (H * Nat.clog 2 (t.numNodes + 1)) :=
      Nat.mul_le_mul_left _ height_bound
    _ = (2 * K * H) * Nat.clog 2 (t.numNodes + 1) := by ring

theorem insertWithRun_log_bound (ltRun : κ → κ → Measured Bool Nat)
    (k : κ) (v : ν) (t : BinaryTree (κ × ν)) (K H : Nat)
    (local_bound : Search.OrderedTree.All
      (fun b => (ltRun k b.1).2 ≤ K ∧ (ltRun b.1 k).2 ≤ K) t)
    (height_bound : t.height ≤ H * Nat.clog 2 (t.numNodes + 1)) :
    (insertWithRun ltRun k v t).2.2 ≤ (2 * K * H) * Nat.clog 2 (t.numNodes + 1) := by
  rw [insertWithRun_work]
  exact lookupWithRun_log_bound ltRun k t K H local_bound height_bound

/-- A family version uses the ordinary real logarithm. The finite-input
comparator premises and the height contract remain explicit at every index. -/
theorem lookupWithRun_isBigO (ltRun : κ → κ → Measured Bool Nat)
    (queries : Nat → κ) (family : Nat → BinaryTree (κ × ν)) (K H : Nat)
    (sizes : ∀ n, (family n).numNodes = n)
    (local_bounds : ∀ n, Search.OrderedTree.All
      (fun b => (ltRun (queries n) b.1).2 ≤ K ∧ (ltRun b.1 (queries n)).2 ≤ K) (family n))
    (heights : ∀ n, (family n).height ≤ H * Nat.clog 2 (n + 1)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((lookupWithRun ltRun (queries n) (family n)).2.2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * ((2 * K * H : Nat) : ℝ),
    Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
  have hnat := lookupWithRun_log_bound ltRun (queries n) (family n) K H
    (local_bounds n) (by simpa only [sizes n] using heights n)
  rw [sizes n] at hnat
  have hb : ((lookupWithRun ltRun (queries n) (family n)).2.2 : ℝ) ≤
      ((2 * K * H : Nat) : ℝ) * (Nat.clog 2 (n + 1) : ℝ) := by exact_mod_cast hnat
  have hlog : 0 ≤ Real.logb 2 (n + 1 : Nat) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  rw [Real.norm_natCast, Real.norm_of_nonneg hlog]
  calc
    ((lookupWithRun ltRun (queries n) (family n)).2.2 : ℝ) ≤
        ((2 * K * H : Nat) : ℝ) * (Nat.clog 2 (n + 1) : ℝ) := hb
    _ ≤ ((2 * K * H : Nat) : ℝ) * (2 * Real.logb 2 (n + 1 : Nat)) :=
      mul_le_mul_of_nonneg_left (clog_two_cast_le_two_logb (n + 1) (by omega))
        (Nat.cast_nonneg _)
    _ = 2 * ((2 * K * H : Nat) : ℝ) * Real.logb 2 (n + 1 : Nat) := by ring

theorem insertWithRun_isBigO (ltRun : κ → κ → Measured Bool Nat)
    (keys : Nat → κ) (values : Nat → ν) (family : Nat → BinaryTree (κ × ν)) (K H : Nat)
    (sizes : ∀ n, (family n).numNodes = n)
    (local_bounds : ∀ n, Search.OrderedTree.All
      (fun b => (ltRun (keys n) b.1).2 ≤ K ∧ (ltRun b.1 (keys n)).2 ≤ K) (family n))
    (heights : ∀ n, (family n).height ≤ H * Nat.clog 2 (n + 1)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((insertWithRun ltRun (keys n) (values n) (family n)).2.2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  simp only [insertWithRun_work]
  exact lookupWithRun_isBigO ltRun keys family K H sizes local_bounds heights

section Ordered
variable [LinearOrder κ]

/-- Comparator correctness is needed only for the two query orientations at
labels in this input tree; unreachable labels may be included harmlessly. -/
theorem lookupWithRun_value (ltRun : κ → κ → Measured Bool Nat) (q : κ)
    (t : BinaryTree (κ × ν))
    (local_value : Search.OrderedTree.All (fun b =>
      (ltRun q b.1).1 = decide (q < b.1) ∧
      (ltRun b.1 q).1 = decide (b.1 < q)) t) :
    (lookupWithRun ltRun q t).1 = Search.OrderedMap.lookup q t := by
  induction t with
  | nil => rfl
  | node b l r ihl ihr =>
      rcases local_value with ⟨⟨hfirst, hsecond⟩, hl, hr⟩
      rw [lookupWithRun_node]
      simp only [hfirst, hsecond, decide_eq_true_eq, Search.OrderedMap.lookup]
      split
      · exact ihl hl
      · split
        · exact ihr hr
        · rfl

theorem insertWithRun_value (ltRun : κ → κ → Measured Bool Nat) (k : κ) (v : ν)
    (t : BinaryTree (κ × ν))
    (local_value : Search.OrderedTree.All (fun b =>
      (ltRun k b.1).1 = decide (k < b.1) ∧
      (ltRun b.1 k).1 = decide (b.1 < k)) t) :
    (insertWithRun ltRun k v t).1 = Search.OrderedMap.bind k v t := by
  induction t with
  | nil => rfl
  | node b l r ihl ihr =>
      rcases local_value with ⟨⟨hfirst, hsecond⟩, hl, hr⟩
      rw [insertWithRun_node]
      simp only [hfirst, hsecond, decide_eq_true_eq, Search.OrderedMap.bind]
      split
      · rw [ihl hl]
      · split
        · rw [ihr hr]
        · rfl

/-- One abstract call charge for each executed strict comparison. -/
def lookupRun (q : κ) (t : BinaryTree (κ × ν)) : Measured (Option ν) (Nat × Nat) :=
  lookupWithRun (fun a b => (decide (a < b), 1)) q t

def insertRun (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    Measured (BinaryTree (κ × ν)) (Nat × Nat) :=
  insertWithRun (fun a b => (decide (a < b), 1)) k v t

@[simp] theorem lookupRun_nil (q : κ) :
    lookupRun q (.nil : BinaryTree (κ × ν)) = (none, (0, 0)) := rfl

@[simp] theorem insertRun_nil (k : κ) (v : ν) :
    insertRun k v .nil = (.node (k, v) .nil .nil, (0, 0)) := rfl

theorem lookupRun_node (q : κ) (b : κ × ν) (l r : BinaryTree (κ × ν)) :
    lookupRun q (.node b l r) =
      if q < b.1 then
        ((lookupRun q l).1, ((lookupRun q l).2.1 + 1, (lookupRun q l).2.2 + 1))
      else if b.1 < q then
        ((lookupRun q r).1, ((lookupRun q r).2.1 + 1, (lookupRun q r).2.2 + 2))
      else (some b.2, (1, 2)) := by
  simpa only [lookupRun, decide_eq_true_eq, Nat.add_comm] using
    lookupWithRun_node (fun a b : κ => (decide (a < b), 1)) q b l r

theorem insertRun_node (k : κ) (v : ν) (b : κ × ν) (l r : BinaryTree (κ × ν)) :
    insertRun k v (.node b l r) =
      if k < b.1 then
        (.node b (insertRun k v l).1 r,
          ((insertRun k v l).2.1 + 1, (insertRun k v l).2.2 + 1))
      else if b.1 < k then
        (.node b l (insertRun k v r).1,
          ((insertRun k v r).2.1 + 1, (insertRun k v r).2.2 + 2))
      else (.node (k, v) l r, (1, 2)) := by
  simpa only [insertRun, decide_eq_true_eq, Nat.add_comm] using
    insertWithRun_node (fun a b : κ => (decide (a < b), 1)) k v b l r

/-- A comparator that really posts the constant work `K` has exactly `K`
times the unit call count, on the same returned value and path. -/
theorem lookupWithRun_constant (q : κ) (t : BinaryTree (κ × ν)) (K : Nat) :
    lookupWithRun (fun a b => (decide (a < b), K)) q t =
      ((lookupRun q t).1, ((lookupRun q t).2.1, K * (lookupRun q t).2.2)) := by
  induction t with
  | nil => rfl
  | node b l r ihl ihr =>
      rw [lookupWithRun_node, lookupRun_node]
      by_cases hleft : q < b.1
      · simp [hleft, ihl, Nat.mul_add]
        omega
      · by_cases hright : b.1 < q
        · simp [hleft, hright, ihr, Nat.mul_succ]
          omega
        · simp [hleft, hright, Nat.mul_succ]

theorem lookupRun_value (q : κ) (t : BinaryTree (κ × ν)) :
    (lookupRun q t).1 = Search.OrderedMap.lookup q t := by
  apply lookupWithRun_value
  exact (Search.OrderedTree.all_iff _ _).2 (fun _ _ => ⟨rfl, rfl⟩)

theorem insertRun_value (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    (insertRun k v t).1 = Search.OrderedMap.bind k v t := by
  apply insertWithRun_value
  exact (Search.OrderedTree.all_iff _ _).2 (fun _ _ => ⟨rfl, rfl⟩)

theorem insertRun_work (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    (insertRun k v t).2 = (lookupRun k t).2 :=
  insertWithRun_work _ k v t

theorem lookupRun_visits_le_height (q : κ) (t : BinaryTree (κ × ν)) :
    (lookupRun q t).2.1 ≤ t.height := lookupWithRun_visits_le_height _ q t

theorem lookupRun_comparisons_le_twice_visits (q : κ) (t : BinaryTree (κ × ν)) :
    (lookupRun q t).2.2 ≤ 2 * (lookupRun q t).2.1 := by
  have h := lookupWithRun_work_le_visits (fun a b : κ => (decide (a < b), 1)) q t 1
    ((Search.OrderedTree.all_iff _ _).2 (fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩))
  simpa only [lookupRun, Nat.mul_one] using h

theorem lookupRun_comparisons_le_height (q : κ) (t : BinaryTree (κ × ν)) :
    (lookupRun q t).2.2 ≤ 2 * t.height :=
  (lookupRun_comparisons_le_twice_visits q t).trans
    (Nat.mul_le_mul_left 2 (lookupRun_visits_le_height q t))

theorem insertRun_visits_le_height (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    (insertRun k v t).2.1 ≤ t.height := by
  rw [insertRun_work]
  exact lookupRun_visits_le_height k t

theorem insertRun_comparisons_le_height (k : κ) (v : ν) (t : BinaryTree (κ × ν)) :
    (insertRun k v t).2.2 ≤ 2 * t.height := by
  rw [insertRun_work]
  exact lookupRun_comparisons_le_height k t

/-- A failed search inspects its final nil; a successful search stops at the
matching nonempty node. The bit comes from the actual returned option. -/
def lookupInspections (q : κ) (t : BinaryTree (κ × ν)) : Nat :=
  (lookupRun q t).2.1 + if (lookupRun q t).1.isNone then 1 else 0

@[simp] theorem lookupInspections_nil (q : κ) :
    lookupInspections q (.nil : BinaryTree (κ × ν)) = 1 := rfl

theorem lookupInspections_node (q : κ) (b : κ × ν) (l r : BinaryTree (κ × ν)) :
    lookupInspections q (.node b l r) =
      if q < b.1 then lookupInspections q l + 1
      else if b.1 < q then lookupInspections q r + 1 else 1 := by
  unfold lookupInspections
  rw [lookupRun_node]
  split
  · dsimp; omega
  · split
    · dsimp; omega
    · rfl

theorem lookupInspections_le (q : κ) (t : BinaryTree (κ × ν)) :
    lookupInspections q t ≤ t.height + 1 := by
  have h := lookupRun_visits_le_height q t
  unfold lookupInspections
  split <;> omega

end Ordered

/-- Reuse the established increasing right spine, attaching any payload type. -/
def rightSpine (value : ν) (start n : Nat) : BinaryTree (Nat × ν) :=
  (Search.OrderedTree.rightSpine start n).map (fun k => (k, value))

theorem rightSpine_ordered (value : ν) (start n : Nat) :
    Search.OrderedTree.OrderedBy Prod.fst (rightSpine value start n) := by
  rw [Search.OrderedTree.orderedBy_iff_map]
  rw [rightSpine, ← BinaryTree.comp_map]
  change Search.OrderedTree.Ordered ((Search.OrderedTree.rightSpine start n).map id)
  rw [BinaryTree.id_map]
  exact Search.OrderedTree.rightSpine_ordered start n

theorem rightSpine_size (value : ν) (start n : Nat) :
    (rightSpine value start n).numNodes = n := by
  rw [rightSpine, Trees.numNodes_map, Search.OrderedTree.rightSpine_numNodes]

theorem rightSpine_height (value : ν) (start n : Nat) :
    (rightSpine value start n).height = n := by
  rw [rightSpine, Trees.height_map, Search.OrderedTree.rightSpine_height]

/-- Every node of this valid family is reached, with two calls per node. -/
theorem lookupRun_rightSpine (value : ν) (start n q : Nat) (above : start + n ≤ q) :
    lookupRun q (rightSpine value start n) = (none, (n, 2 * n)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      have hfirst : ¬ q < start := by omega
      have hsecond : start < q := by omega
      change lookupRun q (.node (start, value) .nil (rightSpine value (start + 1) n)) = _
      rw [lookupRun_node]
      simp only [hfirst, hsecond, ↓reduceIte, ih (start + 1) (by omega)]
      congr 1

theorem insertRun_rightSpine (old new : ν) (start n k : Nat) (above : start + n ≤ k) :
    insertRun k new (rightSpine old start n) =
      (Search.OrderedMap.bind k new (rightSpine old start n), (n, 2 * n)) := by
  apply Prod.ext
  · exact insertRun_value k new _
  · rw [insertRun_work, lookupRun_rightSpine old start n k above]

theorem rightSpine_linear_path (value : ν) (n : Nat) :
    Search.OrderedTree.OrderedBy Prod.fst (rightSpine value 0 n) ∧
    (rightSpine value 0 n).numNodes = n ∧
    (rightSpine value 0 n).height = n ∧
    lookupRun n (rightSpine value 0 n) = (none, (n, 2 * n)) ∧
    lookupInspections n (rightSpine value 0 n) = n + 1 := by
  refine ⟨rightSpine_ordered value 0 n, rightSpine_size value 0 n,
    rightSpine_height value 0 n, lookupRun_rightSpine value 0 n n (by omega), ?_⟩
  simp only [lookupInspections, lookupRun_rightSpine value 0 n n (by omega)]
  rfl

end Resources.SearchTree

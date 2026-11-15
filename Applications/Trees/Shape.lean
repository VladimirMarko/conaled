import Applications.Trees.BasicObservations
import Mathlib.Data.Nat.Log

/-! Minimum external-leaf height, completeness and sharp shape bounds on the
ordinary node-labelled tree. The discrete development is independent of real
analysis and of cached annotations. Source and statement assessment:
`docs/research/fdsa-tree-shape.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

/-- Distance to the nearest external empty leaf. Nil has distance zero. -/
def minHeight (t : BinaryTree α) : Nat :=
  fold 0 (fun l (_ : α) r => min l r + 1) t

@[simp] theorem minHeight_nil : minHeight (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem minHeight_node (a : α) (l r : BinaryTree α) :
    minHeight (.node a l r) = min (minHeight l) (minHeight r) + 1 := rfl

theorem minHeight_map (label : α → β) (t : BinaryTree α) :
    minHeight (t.map label) = minHeight t :=
  fold_map 0 (fun l (_ : β) r => min l r + 1) label t

theorem minHeight_le_height (t : BinaryTree α) : minHeight t ≤ t.height := by
  induction t with
  | nil => exact Nat.le_refl 0
  | node a l r ihl ihr =>
      simp only [minHeight_node, BinaryTree.height]
      exact Nat.add_le_add_right
        ((min_le_left _ _).trans (ihl.trans (le_max_left _ _))) 1

/-- Source completeness: both children are complete with equal heights.
This is the perfect-tree convention, with nil also complete. -/
def Complete : BinaryTree α → Prop
  | .nil => True
  | .node _ l r => l.height = r.height ∧ Complete l ∧ Complete r

@[simp] theorem complete_nil : Complete (.nil : BinaryTree α) := True.intro

@[simp] theorem complete_node (a : α) (l r : BinaryTree α) :
    Complete (.node a l r) ↔ l.height = r.height ∧ Complete l ∧ Complete r := Iff.rfl

theorem complete_iff_minHeight_eq_height (t : BinaryTree α) :
    Complete t ↔ minHeight t = t.height := by
  induction t with
  | nil => simp [BinaryTree.height]
  | node a l r ihl ihr =>
      have hl := minHeight_le_height l
      have hr := minHeight_le_height r
      simp only [complete_node, minHeight_node, BinaryTree.height, ihl, ihr]
      omega

theorem complete_map (label : α → β) (t : BinaryTree α) :
    Complete (t.map label) ↔ Complete t := by
  simp only [complete_iff_minHeight_eq_height, minHeight_map, height_map]

/-- Every whole rooted descendant of a complete tree is complete. -/
theorem complete_of_subtree {s t : BinaryTree α} (hst : Subtree s t) :
    Complete t → Complete s := by
  induction hst with
  | refl => exact id
  | left a _ ih =>
      intro ht
      exact ih ((complete_node a _ _).mp ht).2.1
  | right a _ ih =>
      intro ht
      exact ih ((complete_node a _ _).mp ht).2.2

/-- External leaves occupy at most two adjacent depths. No left packing is
required; the additive form avoids truncated subtraction in later proofs. -/
def AlmostComplete (t : BinaryTree α) : Prop := t.height ≤ minHeight t + 1

@[simp] theorem almostComplete_nil : AlmostComplete (.nil : BinaryTree α) := by
  exact Nat.zero_le 1

theorem almostComplete_iff_sub (t : BinaryTree α) :
    AlmostComplete t ↔ t.height - minHeight t ≤ 1 := by
  unfold AlmostComplete
  omega

theorem complete_almostComplete (t : BinaryTree α) (ht : Complete t) :
    AlmostComplete t := by
  have h := (complete_iff_minHeight_eq_height t).1 ht
  unfold AlmostComplete
  omega

theorem almostComplete_children (a : α) (l r : BinaryTree α)
    (ht : AlmostComplete (.node a l r)) : AlmostComplete l ∧ AlmostComplete r := by
  simp only [AlmostComplete, BinaryTree.height, minHeight_node] at ht ⊢
  omega

/-- Almost completeness passes to every structural descendant, including
the empty tree and the original tree itself. -/
theorem almostComplete_of_subtree {s t : BinaryTree α} (hst : Subtree s t) :
    AlmostComplete t → AlmostComplete s := by
  induction hst with
  | refl => exact id
  | left a _ ih =>
      intro ht
      exact ih (almostComplete_children a _ _ ht).1
  | right a _ ih =>
      intro ht
      exact ih (almostComplete_children a _ _ ht).2

theorem almostComplete_map (label : α → β) (t : BinaryTree α) :
    AlmostComplete (t.map label) ↔ AlmostComplete t := by
  simp only [AlmostComplete, height_map, minHeight_map]

/-- The shortest external-leaf depth gives a lower capacity bound. -/
theorem pow_minHeight_le_numLeaves (t : BinaryTree α) :
    2 ^ minHeight t ≤ t.numLeaves := by
  induction t with
  | nil => exact Nat.le_refl 1
  | node a l r ihl ihr =>
      have hl : 2 ^ min (minHeight l) (minHeight r) ≤ l.numLeaves :=
        (Nat.pow_le_pow_right (by decide : 0 < 2) (min_le_left _ _)).trans ihl
      have hr : 2 ^ min (minHeight l) (minHeight r) ≤ r.numLeaves :=
        (Nat.pow_le_pow_right (by decide : 0 < 2) (min_le_right _ _)).trans ihr
      simp only [minHeight_node, BinaryTree.numLeaves, Nat.pow_succ]
      omega

/-- Maximum external-leaf depth gives an upper capacity bound. -/
theorem numLeaves_le_pow_height (t : BinaryTree α) :
    t.numLeaves ≤ 2 ^ t.height := by
  induction t with
  | nil => exact Nat.le_refl 1
  | node a l r ihl ihr =>
      have hl : l.numLeaves ≤ 2 ^ max l.height r.height :=
        ihl.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left _ _))
      have hr : r.numLeaves ≤ 2 ^ max l.height r.height :=
        ihr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _))
      simp only [BinaryTree.numLeaves, BinaryTree.height, Nat.pow_succ]
      omega

theorem numLeaves_eq_pow_height (t : BinaryTree α) :
    Complete t → t.numLeaves = 2 ^ t.height := by
  induction t with
  | nil => intro _; rfl
  | node a l r ihl ihr =>
      rintro ⟨h, hl, hr⟩
      simp only [BinaryTree.numLeaves, BinaryTree.height, ihl hl, ihr hr,
        h, max_self, Nat.pow_succ]
      omega

theorem numLeaves_eq_pow_minHeight (t : BinaryTree α) (ht : Complete t) :
    t.numLeaves = 2 ^ minHeight t := by
  rw [(complete_iff_minHeight_eq_height t).1 ht]
  exact numLeaves_eq_pow_height t ht

/-- Incompleteness makes the maximum-height capacity bound strict. -/
theorem numLeaves_lt_pow_height (t : BinaryTree α) :
    ¬ Complete t → t.numLeaves < 2 ^ t.height := by
  classical
  induction t with
  | nil =>
      intro ht
      exact False.elim (ht complete_nil)
  | node a l r ihl ihr =>
      intro ht
      have hl := numLeaves_le_pow_height l
      have hr := numLeaves_le_pow_height r
      rcases lt_trichotomy l.height r.height with hlt | heq | hgt
      · have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
        simp only [BinaryTree.numLeaves, BinaryTree.height,
          max_eq_right (le_of_lt hlt), Nat.pow_succ]
        omega
      · by_cases hcl : Complete l
        · have hcr : ¬ Complete r := fun hcr => ht ⟨heq, hcl, hcr⟩
          have hs := ihr hcr
          have hl' : l.numLeaves ≤ 2 ^ r.height := by simpa only [heq] using hl
          simp only [BinaryTree.numLeaves, BinaryTree.height, heq, max_self,
            Nat.pow_succ]
          omega
        · have hs : l.numLeaves < 2 ^ r.height := by simpa only [heq] using ihl hcl
          simp only [BinaryTree.numLeaves, BinaryTree.height, heq, max_self,
            Nat.pow_succ]
          omega
      · have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hgt
        simp only [BinaryTree.numLeaves, BinaryTree.height,
          max_eq_left (le_of_lt hgt), Nat.pow_succ]
        omega

/-- Incompleteness also makes the minimum-height capacity bound strict. -/
theorem pow_minHeight_lt_numLeaves (t : BinaryTree α) :
    ¬ Complete t → 2 ^ minHeight t < t.numLeaves := by
  classical
  induction t with
  | nil =>
      intro ht
      exact False.elim (ht complete_nil)
  | node a l r ihl ihr =>
      intro ht
      have hl := pow_minHeight_le_numLeaves l
      have hr := pow_minHeight_le_numLeaves r
      rcases lt_trichotomy (minHeight l) (minHeight r) with hlt | heq | hgt
      · have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
        simp only [minHeight_node, BinaryTree.numLeaves,
          min_eq_left (le_of_lt hlt), Nat.pow_succ]
        omega
      · by_cases hcl : Complete l
        · have hcr : ¬ Complete r := by
            intro hcr
            have hml := (complete_iff_minHeight_eq_height l).1 hcl
            have hmr := (complete_iff_minHeight_eq_height r).1 hcr
            exact ht ⟨by omega, hcl, hcr⟩
          have hs := ihr hcr
          have hl' : 2 ^ minHeight r ≤ l.numLeaves := by simpa only [heq] using hl
          simp only [minHeight_node, BinaryTree.numLeaves, heq, min_self,
            Nat.pow_succ]
          omega
        · have hs : 2 ^ minHeight r < l.numLeaves := by simpa only [heq] using ihl hcl
          simp only [minHeight_node, BinaryTree.numLeaves, heq, min_self,
            Nat.pow_succ]
          omega
      · have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hgt
        simp only [minHeight_node, BinaryTree.numLeaves,
          min_eq_right (le_of_lt hgt), Nat.pow_succ]
        omega

theorem complete_iff_numLeaves_eq_pow_height (t : BinaryTree α) :
    Complete t ↔ t.numLeaves = 2 ^ t.height := by
  constructor
  · exact numLeaves_eq_pow_height t
  · intro h
    by_contra ht
    exact (ne_of_lt (numLeaves_lt_pow_height t ht)) h

theorem complete_iff_numLeaves_eq_pow_minHeight (t : BinaryTree α) :
    Complete t ↔ t.numLeaves = 2 ^ minHeight t := by
  constructor
  · exact numLeaves_eq_pow_minHeight t
  · intro h
    by_contra ht
    exact (ne_of_lt (pow_minHeight_lt_numLeaves t ht)) h.symm

theorem minHeight_le_log_numLeaves (t : BinaryTree α) :
    minHeight t ≤ Nat.log 2 t.numLeaves :=
  Nat.le_log_of_pow_le (by decide : 1 < 2) (pow_minHeight_le_numLeaves t)

theorem clog_numLeaves_le_height (t : BinaryTree α) :
    Nat.clog 2 t.numLeaves ≤ t.height :=
  Nat.clog_le_of_le_pow (numLeaves_le_pow_height t)

/-- The lower rounded logarithm is exact on almost-complete trees, including nil. -/
theorem minHeight_eq_log_numLeaves (t : BinaryTree α) (ht : AlmostComplete t) :
    minHeight t = Nat.log 2 t.numLeaves := by
  classical
  by_cases hc : Complete t
  · rw [numLeaves_eq_pow_height t hc, Nat.log_pow (by decide : 1 < 2)]
    exact (complete_iff_minHeight_eq_height t).1 hc
  · have hle := minHeight_le_height t
    have hne : minHeight t ≠ t.height :=
      fun h => hc ((complete_iff_minHeight_eq_height t).2 h)
    have hheight : t.height = minHeight t + 1 := by
      unfold AlmostComplete at ht
      omega
    have hupper : t.numLeaves < 2 ^ (minHeight t + 1) := by
      simpa only [hheight] using numLeaves_lt_pow_height t hc
    exact (Nat.log_eq_of_pow_le_of_lt_pow
      (pow_minHeight_le_numLeaves t) hupper).symm

/-- The upper rounded logarithm is exact on almost-complete trees, including nil. -/
theorem height_eq_clog_numLeaves (t : BinaryTree α) (ht : AlmostComplete t) :
    t.height = Nat.clog 2 t.numLeaves := by
  classical
  by_cases hc : Complete t
  · rw [numLeaves_eq_pow_height t hc,
      Nat.clog_pow 2 t.height (by decide : 1 < 2)]
  · have hlow : minHeight t < Nat.clog 2 t.numLeaves :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2
        (pow_minHeight_lt_numLeaves t hc)
    have hupp := clog_numLeaves_le_height t
    unfold AlmostComplete at ht
    omega

/-- Almost-complete trees minimize height under a node-count comparison.
The compared tree can have any shape and an unrelated payload universe. -/
theorem height_optimal (s : BinaryTree α) (t : BinaryTree β)
    (hs : AlmostComplete s) (hsize : s.numNodes ≤ t.numNodes) :
    s.height ≤ t.height := by
  have hleaves : s.numLeaves ≤ t.numLeaves := by
    simpa only [BinaryTree.numLeaves_eq_numNodes_succ] using
      Nat.add_le_add_right hsize 1
  rw [height_eq_clog_numLeaves s hs]
  exact Nat.clog_le_of_le_pow (hleaves.trans (numLeaves_le_pow_height t))

/-- A leaf-count comparison bounds one almost-complete tree's maximum depth
by the other tree's minimum depth, even across unrelated payload types. -/
theorem height_le_minHeight_add_one_of_numLeaves_le
    (s : BinaryTree α) (t : BinaryTree β)
    (hs : AlmostComplete s) (ht : AlmostComplete t)
    (hleaves : s.numLeaves ≤ t.numLeaves + 1) :
    s.height ≤ minHeight t + 1 := by
  rw [height_eq_clog_numLeaves s hs, minHeight_eq_log_numLeaves t ht]
  apply Nat.clog_le_of_le_pow
  exact hleaves.trans (Nat.succ_le_of_lt
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) t.numLeaves))

/-- Almost-complete children with leaf counts differing by at most one give
an almost-complete parent. This is a sufficient criterion, not a converse. -/
theorem almostComplete_node_of_numLeaves (a : α) (l r : BinaryTree α)
    (hl : AlmostComplete l) (hr : AlmostComplete r)
    (hlr : l.numLeaves ≤ r.numLeaves + 1) (hrl : r.numLeaves ≤ l.numLeaves + 1) :
    AlmostComplete (.node a l r) := by
  have hcrosslr := height_le_minHeight_add_one_of_numLeaves_le l r hl hr hlr
  have hcrossrl := height_le_minHeight_add_one_of_numLeaves_le r l hr hl hrl
  simp only [AlmostComplete, BinaryTree.height, minHeight_node] at hl hr ⊢
  omega

end Trees

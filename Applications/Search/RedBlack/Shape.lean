import Applications.Search.RedBlack.Basic
import Batteries.Recycling.RBTree.WF

/-!
# Source red-black shape invariants

`RB` uses the textbook's parent color. The provider's `Balanced` uses the
root color, so the red-parent case requires a black root and the black-parent
case permits either root color. The empty tree is black in the provider.

`NearlyRB` retains the source's nonempty requirement while using the provider's
temporary root red-red invariant. These structural properties have no ordering
or comparator-law premise.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

open RBTree RBTree.RBColor RBTree.RBNode

universe u v
variable {κ : Type u} {ν : Type v}

/-- The source invariant, indexed by the hypothetical parent's color. -/
def RB (t : Tree κ ν) : RBColor → Nat → Prop
  | red, n => t.Balanced black n
  | black, n => ∃ root, t.Balanced root n

/-- A nonempty tree whose only possible red-red violation is at its root. -/
def NearlyRB (t : Tree κ ν) (n : Nat) : Prop :=
  t ≠ .nil ∧ t.RedRed True n

@[simp] theorem rb_red_iff {t : Tree κ ν} {n : Nat} :
    RB t red n ↔ t.Balanced black n := Iff.rfl

@[simp] theorem rb_black_iff {t : Tree κ ν} {n : Nat} :
    RB t black n ↔ ∃ root, t.Balanced root n := Iff.rfl

theorem RB.balanced {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : ∃ root, t.Balanced root n := by
  cases parent with
  | red => exact ⟨black, h⟩
  | black => exact h

/-- The source leaf rule works for either hypothetical parent color. -/
theorem RB.nil (parent : RBColor) : RB (.nil : Tree κ ν) parent 0 := by
  cases parent with
  | red => exact RBNode.Balanced.nil
  | black => exact ⟨black, RBNode.Balanced.nil⟩

@[simp] theorem rb_nil_iff (parent : RBColor) (n : Nat) :
    RB (.nil : Tree κ ν) parent n ↔ n = 0 := by
  constructor
  · intro h
    obtain ⟨root, h⟩ := h.balanced
    cases h
    rfl
  · rintro rfl
    exact RB.nil parent

/-- A red node is permitted only under a black parent. -/
theorem RB.red {l r : Tree κ ν} {n : Nat} (key : κ) (value : ν)
    (hl : RB l red n) (hr : RB r red n) :
    RB (.node red l (key, value) r) black n :=
  ⟨RBColor.red, RBNode.Balanced.red hl hr⟩

@[simp] theorem rb_red_node_iff {l r : Tree κ ν} {key : κ} {value : ν}
    {parent : RBColor} {n : Nat} :
    RB (.node red l (key, value) r) parent n ↔
      parent = black ∧ RB l red n ∧ RB r red n := by
  constructor
  · intro h
    cases parent with
    | red => cases h
    | black =>
        obtain ⟨root, h⟩ := h
        cases h with
        | red hl hr => exact ⟨rfl, hl, hr⟩
  · rintro ⟨rfl, hl, hr⟩
    exact RB.red key value hl hr

/-- A black node adds one black node on every path and allows either parent. -/
theorem RB.black {l r : Tree κ ν} {n : Nat} (parent : RBColor)
    (key : κ) (value : ν) (hl : RB l black n) (hr : RB r black n) :
    RB (.node black l (key, value) r) parent (n + 1) := by
  obtain ⟨cl, hl⟩ := hl
  obtain ⟨cr, hr⟩ := hr
  cases parent with
  | red => exact RBNode.Balanced.black hl hr
  | black => exact ⟨RBColor.black, RBNode.Balanced.black hl hr⟩

@[simp] theorem rb_black_node_iff {l r : Tree κ ν} {key : κ} {value : ν}
    {parent : RBColor} {m : Nat} :
    RB (.node black l (key, value) r) parent m ↔
      ∃ n, m = n + 1 ∧ RB l black n ∧ RB r black n := by
  constructor
  · intro h
    obtain ⟨root, h⟩ := h.balanced
    cases h with
    | @black _ cl n _ cr _ hl hr => exact ⟨n, rfl, ⟨cl, hl⟩, ⟨cr, hr⟩⟩
  · rintro ⟨n, rfl, hl, hr⟩
    exact RB.black parent key value hl hr

/-- Changing only the hypothetical parent leaves the tree and height unchanged. -/
theorem rb_blacken_parent {t : Tree κ ν} {n : Nat} (h : RB t red n) :
    RB t black n := ⟨black, h⟩

theorem nearlyRB_iff {t : Tree κ ν} {n : Nat} :
    NearlyRB t n ↔ t ≠ .nil ∧ t.RedRed True n := Iff.rfl

@[simp] theorem not_nearlyRB_nil (n : Nat) :
    ¬ NearlyRB (.nil : Tree κ ν) n := fun h => h.1 rfl

/-- The source red constructor allows both children to have either root color. -/
theorem NearlyRB.red {l r : Tree κ ν} {n : Nat} (key : κ) (value : ν)
    (hl : RB l black n) (hr : RB r black n) :
    NearlyRB (.node red l (key, value) r) n := by
  obtain ⟨cl, hl⟩ := hl
  obtain ⟨cr, hr⟩ := hr
  refine ⟨?_, RBNode.RedRed.redred trivial hl hr⟩
  intro h
  cases h

@[simp] theorem nearlyRB_red_node_iff {l r : Tree κ ν} {key : κ} {value : ν}
    {n : Nat} :
    NearlyRB (.node red l (key, value) r) n ↔ RB l black n ∧ RB r black n := by
  constructor
  · intro h
    obtain ⟨cl, cr, hl, hr⟩ := h.2.of_red
    exact ⟨⟨cl, hl⟩, ⟨cr, hr⟩⟩
  · rintro ⟨hl, hr⟩
    exact NearlyRB.red key value hl hr

/-- The source black constructor increments the common children's height. -/
theorem NearlyRB.black {l r : Tree κ ν} {n : Nat} (key : κ) (value : ν)
    (hl : RB l black n) (hr : RB r black n) :
    NearlyRB (.node black l (key, value) r) (n + 1) := by
  obtain ⟨cl, hl⟩ := hl
  obtain ⟨cr, hr⟩ := hr
  refine ⟨?_, RBNode.RedRed.balanced (RBNode.Balanced.black hl hr)⟩
  intro h
  cases h

@[simp] theorem nearlyRB_black_node_iff {l r : Tree κ ν} {key : κ} {value : ν}
    {m : Nat} :
    NearlyRB (.node black l (key, value) r) m ↔
      ∃ n, m = n + 1 ∧ RB l black n ∧ RB r black n := by
  constructor
  · intro h
    have .balanced hb := h.2
    cases hb with
    | @black _ cl n _ cr _ hl hr => exact ⟨n, rfl, ⟨cl, hl⟩, ⟨cr, hr⟩⟩
  · rintro ⟨n, rfl, hl, hr⟩
    exact NearlyRB.black key value hl hr

theorem NearlyRB.of_rb {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) (nonempty : t ≠ .nil) : NearlyRB t n := by
  obtain ⟨root, h⟩ := h.balanced
  exact ⟨nonempty, .balanced h⟩

private theorem balance_redRed_left {l r : Tree κ ν} {root : RBColor} {n : Nat}
    (key : κ) (value : ν) (hl : l.RedRed True n) (hr : r.Balanced root n) :
    ∃ resultRoot, (balance black l key value r).Balanced resultRoot (n + 1) := by
  simp only [balance]
  split
  · have .redred _ (.red ha hb) hc := hl
    exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · have .redred _ ha (.red hb hc) := hl
    exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · next hll hlr =>
    split
    · nomatch hr
    · nomatch hr
    · match hl with
      | .balanced hl => exact ⟨_, .black hl hr⟩
      | .redred _ (c₁ := black) (c₂ := black) ha hb =>
          exact ⟨_, .black (.red ha hb) hr⟩
      | .redred _ (c₁ := red) (.red ..) _ => cases hll _ _ _ _ _ rfl
      | .redred _ (c₂ := red) _ (.red ..) => cases hlr _ _ _ _ _ rfl

private theorem balance_redRed_right {l r : Tree κ ν} {root : RBColor} {n : Nat}
    (key : κ) (value : ν) (hl : l.Balanced root n) (hr : r.RedRed True n) :
    ∃ resultRoot, (balance black l key value r).Balanced resultRoot (n + 1) := by
  simp only [balance]
  split
  · nomatch hl
  · nomatch hl
  · split
    · have .redred _ (.red hb hc) hd := hr
      exact ⟨_, .red (.black hl hb) (.black hc hd)⟩
    · have .redred _ hb (.red hc hd) := hr
      exact ⟨_, .red (.black hl hb) (.black hc hd)⟩
    · next hrl hrr =>
      match hr with
      | .balanced hr => exact ⟨_, .black hl hr⟩
      | .redred _ (c₁ := black) (c₂ := black) hb hc =>
          exact ⟨_, .black hl (.red hb hc)⟩
      | .redred _ (c₁ := red) (.red ..) _ => cases hrl _ _ _ _ _ rfl
      | .redred _ (c₂ := red) _ (.red ..) => cases hrr _ _ _ _ _ rfl

/-- The source matcher repairs a temporary exception in the left subtree. -/
theorem balance_black_left {l r : Tree κ ν} {n : Nat} (key : κ) (value : ν)
    (hl : NearlyRB l n) (hr : RB r black n) :
    RB (balance black l key value r) black (n + 1) := by
  obtain ⟨root, hr⟩ := hr
  exact balance_redRed_left key value hl.2 hr

/-- This proof uses the source's right-left case before its right-right case. -/
theorem balance_black_right {l r : Tree κ ν} {n : Nat} (key : κ) (value : ν)
    (hl : RB l black n) (hr : NearlyRB r n) :
    RB (balance black l key value r) black (n + 1) := by
  obtain ⟨root, hl⟩ := hl
  exact balance_redRed_right key value hl hr.2

private theorem ins_redRed (ltb : κ → κ → Bool) (key : κ) (value : ν)
    {t : Tree κ ν} {root : RBColor} {n : Nat} (h : t.Balanced root n) :
    (ins ltb key value t).RedRed (t.isRed = red) n := by
  induction h with
  | nil =>
      simp only [ins_nil]
      exact .balanced (.red .nil .nil)
  | @red l n r binding hl hr ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      simp only [ins_node]
      split
      · simp only [balance]
        obtain ⟨root, h⟩ := ihl.of_false (by cases hl <;> simp [RBNode.isRed])
        exact .redred rfl h hr
      · split
        · simp only [balance]
          obtain ⟨root, h⟩ := ihr.of_false (by cases hr <;> simp [RBNode.isRed])
          exact .redred rfl hl h
        · exact .balanced (.red hl hr)
  | @black l cl n r cr binding hl hr ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      simp only [ins_node]
      split
      · obtain ⟨root, h⟩ :=
          balance_redRed_left old previous (ihl.imp fun _ => trivial) hr
        exact .balanced h
      · split
        · obtain ⟨root, h⟩ :=
            balance_redRed_right old previous hl (ihr.imp fun _ => trivial)
          exact .balanced h
        · exact .balanced (.black hl hr)

/-- The simultaneous source invariant, for arbitrary Boolean branch tests. -/
theorem ins_rb (ltb : κ → κ → Bool) (key : κ) (value : ν) (t : Tree κ ν) (n : Nat) :
    (RB t black n → NearlyRB (ins ltb key value t) n) ∧
      (RB t red n → RB (ins ltb key value t) black n) := by
  constructor
  · intro h
    obtain ⟨root, h⟩ := h
    exact ⟨ins_ne_nil ltb key value t, (ins_redRed ltb key value h).imp fun _ => trivial⟩
  · intro h
    have result := ins_redRed ltb key value (show t.Balanced black n from h)
    exact result.of_false (by cases h <;> simp [RBNode.isRed])

theorem ins_red (ltb : κ → κ → Bool) (key : κ) (value : ν)
    {t : Tree κ ν} {n : Nat} (h : RB t red n) :
    RB (ins ltb key value t) black n := (ins_rb ltb key value t n).2 h

/-- Root recoloring may increase black height; the source only promises a new one. -/
theorem rb_blacken_root {t : Tree κ ν} {n : Nat} (h : RB t black n) :
    ∃ n', RB (makeBlack t) red n' := by
  obtain ⟨root, h⟩ := h
  exact h.setBlack

/-- Public source insertion restores a black root with some black height. -/
theorem insert_rb (ltb : κ → κ → Bool) (key : κ) (value : ν)
    {t : Tree κ ν} {n : Nat} (h : RB t red n) :
    ∃ n', RB (insert ltb key value t) red n' := by
  rw [insert_eq_makeBlack_ins]
  exact rb_blacken_root (ins_red ltb key value h)

end Search.RedBlack

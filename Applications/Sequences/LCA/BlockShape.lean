import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Range
import Mathlib.Tactic

/-! Relative ±1 block shapes discard absolute height while preserving all
within-block comparisons, including ties. The classifier reads adjacent depths;
it does not assume an oracle for observational equivalence. -/
namespace Sequences.LCA

abbrev Shape (steps : Nat) := Fin steps → Bool

def classify (steps : Nat) (depth : Nat → Int) : Shape steps :=
  fun i => decide (depth i.val < depth (i.val + 1))

def UnitSteps (steps : Nat) (depth : Nat → Int) : Prop :=
  ∀ i, i < steps → depth (i + 1) = depth i + 1 ∨ depth (i + 1) = depth i - 1

def relative (shape : Shape steps) : Nat → Int
  | 0 => 0
  | i + 1 => relative shape i + if h : i < steps then
      (if shape ⟨i, h⟩ then 1 else -1) else 0

theorem relative_classify (depth : Nat → Int) (h : UnitSteps steps depth)
    (i : Nat) (hi : i ≤ steps) :
    relative (classify steps depth) i = depth i - depth 0 := by
  induction i with
  | zero => simp [relative]
  | succ i ih =>
    have hib : i < steps := by omega
    rw [relative, ih (by omega)]
    simp only [hib, dite_true, classify, decide_eq_true_eq]
    rcases h i hib with up | down
    · simp [up]
      omega
    · simp [down]
      omega

theorem same_shape_difference (a b : Nat → Int)
    (ha : UnitSteps steps a) (hb : UnitSteps steps b)
    (hs : classify steps a = classify steps b) (i : Nat) (hi : i ≤ steps) :
    a i - a 0 = b i - b 0 := by
  rw [← relative_classify a ha i hi, ← relative_classify b hb i hi, hs]

theorem same_shape_order (a b : Nat → Int)
    (ha : UnitSteps steps a) (hb : UnitSteps steps b)
    (hs : classify steps a = classify steps b)
    (i j : Nat) (hi : i ≤ steps) (hj : j ≤ steps) :
    (a i ≤ a j ↔ b i ≤ b j) := by
  have h₁ := same_shape_difference a b ha hb hs i hi
  have h₂ := same_shape_difference a b ha hb hs j hj
  omega

/-- An independent specification retaining the leftmost witness, not only its
minimum value. The interval is inclusive. -/
def LeftmostMinimum (depth : Nat → Int) (lo hi answer : Nat) : Prop :=
  lo ≤ answer ∧ answer ≤ hi ∧
  ∀ j, lo ≤ j → j ≤ hi → depth answer ≤ depth j ∧
    (depth answer = depth j → answer ≤ j)

theorem leftmostMinimum_unique (depth : Nat → Int)
    (ha : LeftmostMinimum depth lo hi a) (hb : LeftmostMinimum depth lo hi b) :
    a = b := by
  obtain ⟨hal, hah, ham⟩ := ha
  obtain ⟨hbl, hbh, hbm⟩ := hb
  have h₁ := ham b hbl hbh
  have h₂ := hbm a hal hah
  have he : depth a = depth b := le_antisymm h₁.1 h₂.1
  exact Nat.le_antisymm (h₁.2 he) (h₂.2 he.symm)

theorem same_shape_minimum (a b : Nat → Int)
    (ha : UnitSteps steps a) (hb : UnitSteps steps b)
    (hs : classify steps a = classify steps b) (hh : hi ≤ steps) :
    LeftmostMinimum a lo hi answer ↔ LeftmostMinimum b lo hi answer := by
  have transfer : ∀ (a b : Nat → Int), UnitSteps steps a → UnitSteps steps b →
      classify steps a = classify steps b →
      LeftmostMinimum a lo hi answer → LeftmostMinimum b lo hi answer := by
    intro a b ha hb hs hm
    refine ⟨hm.1, hm.2.1, ?_⟩
    intro j hjl hjh
    have hah := hm.2.1
    have ho := same_shape_order a b ha hb hs answer j (by omega) (by omega)
    have hr := same_shape_order a b ha hb hs j answer (by omega) (by omega)
    have hd := hm.2.2 j hjl hjh
    refine ⟨ho.mp hd.1, ?_⟩
    intro he
    exact hd.2 (le_antisymm hd.1 (hr.mpr (le_of_eq he.symm)))
  exact ⟨transfer a b ha hb hs, transfer b a hb ha hs.symm⟩

theorem shape_count (steps : Nat) : Fintype.card (Shape steps) = 2 ^ steps := by
  simp [Shape]

/-- Duplicate minima retain the first position after translation. -/
example : LeftmostMinimum (fun i => if i = 1 then (4 : Int) else 3) 0 2 0 := by
  refine ⟨by omega, by omega, ?_⟩
  intro j hj hj'
  simp only [show (0 : Nat) ≠ 1 by omega, ↓reduceIte]
  split_ifs <;> omega

/-- A comparison fold used to generate within-block tables. Its candidate order
is retained, so ties choose the earliest candidate in that order. -/
def select (depth : Fin (steps + 1) → Int)
    (candidates : List (Fin (steps + 1))) (fallback : Fin (steps + 1)) :
    Fin (steps + 1) :=
  candidates.foldr (fun a b => if depth a ≤ depth b then a else b) fallback

theorem select_congr (a b : Fin (steps + 1) → Int)
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j)
    (candidates : List (Fin (steps + 1))) (fallback : Fin (steps + 1)) :
    select a candidates fallback = select b candidates fallback := by
  induction candidates with
  | nil => rfl
  | cons i rest ih =>
    simp only [select, List.foldr_cons] at *
    rw [ih]
    simp only [h]

theorem same_shape_select (a b : Nat → Int)
    (ha : UnitSteps steps a) (hb : UnitSteps steps b)
    (hs : classify steps a = classify steps b)
    (candidates : List (Fin (steps + 1))) (fallback : Fin (steps + 1)) :
    select (fun i => a i.val) candidates fallback =
      select (fun i => b i.val) candidates fallback := by
  apply select_congr
  intro i j
  exact same_shape_order a b ha hb hs i j (by omega) (by omega)

/-- A finite integer class address, constructed from the change bits. -/
def shapeCode : {steps : Nat} → Shape steps → Nat
  | 0, _ => 0
  | k + 1, shape => (if shape 0 then 1 else 0) +
      2 * shapeCode (fun i : Fin k => shape i.succ)

theorem shapeCode_lt (shape : Shape steps) : shapeCode shape < 2 ^ steps := by
  induction steps with
  | zero => simp [shapeCode]
  | succ k ih =>
    have ht := ih (fun i : Fin k => shape i.succ)
    simp only [shapeCode, pow_succ]
    split <;> omega

def decodeShape : (steps : Nat) → Nat → Shape steps
  | 0, _ => Fin.elim0
  | k + 1, code => Fin.cases (decide (code % 2 = 1)) (decodeShape k (code / 2))

theorem decode_shapeCode (shape : Shape steps) :
    decodeShape steps (shapeCode shape) = shape := by
  induction steps with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases h : shape 0 <;> simp [decodeShape, shapeCode, h]
    · have hi := congrFun (ih (fun j : Fin k => shape j.succ)) j
      have hd : (1 + 2 * shapeCode (fun j : Fin k => shape j.succ)) / 2 =
          shapeCode (fun j : Fin k => shape j.succ) := by omega
      cases h : shape 0 <;> simpa [decodeShape, shapeCode, h, hd] using hi

theorem shapeCode_injective : Function.Injective (@shapeCode steps) := by
  intro a b h
  rw [← decode_shapeCode a, ← decode_shapeCode b, h]

/-- Integer addresses, not equality testing on shape functions, distinguish
all classes. No table for different absolute starting heights is needed. -/
def classAddress (steps : Nat) (depth : Nat → Int) : Fin (2 ^ steps) :=
  ⟨shapeCode (classify steps depth), shapeCode_lt _⟩

theorem same_address_minimum (a b : Nat → Int)
    (ha : UnitSteps steps a) (hb : UnitSteps steps b)
    (hs : classAddress steps a = classAddress steps b) (hh : hi ≤ steps) :
    LeftmostMinimum a lo hi answer ↔ LeftmostMinimum b lo hi answer := by
  apply same_shape_minimum a b ha hb _ hh
  apply shapeCode_injective
  exact congrArg Fin.val hs

/-- Two blocks at different absolute depths share an address and preserve the
leftmost of their duplicate minima. -/
example : LeftmostMinimum (fun i => if i = 1 then (11 : Int) else 10) 0 2 0 := by
  let a : Nat → Int := fun i => if i = 1 then 4 else 3
  let b : Nat → Int := fun i => if i = 1 then 11 else 10
  have ha : UnitSteps 2 a := by
    intro i hi
    interval_cases i <;> decide
  have hb : UnitSteps 2 b := by
    intro i hi
    interval_cases i <;> decide
  have hs : classAddress 2 a = classAddress 2 b := by decide
  apply (same_address_minimum a b ha hb hs (by decide : 2 ≤ 2)).mp
  refine ⟨by omega, by omega, ?_⟩
  intro j hj hj'
  dsimp [a]
  split_ifs <;> omega

end Sequences.LCA

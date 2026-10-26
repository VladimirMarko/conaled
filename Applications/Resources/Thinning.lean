import Applications.Optimization.Thinning
import Applications.Resources.Measured

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Thinning
open Optimization.Thinning
universe u
variable {α : Type u}

/-- Execute the literal guards, counting relation calls in their source order. -/
def bumpRun (R : α → α → Prop) [DecidableRel R] (x : α) : List α → List α × Nat
  | [] => ([x], 0)
  | y :: ys =>
      if R x y then (x :: ys, 1)
      else if R y x then (y :: ys, 2) else (x :: y :: ys, 2)

def thinRun (R : α → α → Prop) [DecidableRel R] : List α → List α × Nat
  | [] => ([], 0)
  | x :: xs =>
      let tail := thinRun R xs
      let step := bumpRun R x tail.1
      (step.1, tail.2 + step.2)

theorem bumpRun_value (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    (bumpRun R x xs).1 = bump R x xs := by
  cases xs <;> simp only [bumpRun, bump]
  split
  · rfl
  · split <;> rfl

theorem bumpRun_bound (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    (bumpRun R x xs).2 ≤ 2 := by
  cases xs <;> simp only [bumpRun]
  · omega
  · split
    · omega
    · split <;> omega

theorem thinRun_value (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    (thinRun R xs).1 = thinBy R xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [thinRun, bumpRun_value, ih, thinBy, List.foldr_cons]

theorem thinRun_bound (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    (thinRun R xs).2 ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [thinRun]
  | cons x xs ih =>
      have hs := bumpRun_bound R x (thinRun R xs).1
      simp only [thinRun, List.length_cons]
      omega

/-- Unit events: one list case, each guard, and each constructed cons.
The second guard's retained head is charged as a cons as printed in the source. -/
def bumpWorkRun (R : α → α → Prop) [DecidableRel R] (x : α) : List α → List α × Nat
  | [] => ([x], 2)
  | y :: ys =>
      if R x y then (x :: ys, 3)
      else if R y x then (y :: ys, 4) else (x :: y :: ys, 5)

/-- In addition to bump's events, charge one visit per fold constructor,
including its terminal empty case. Relation evaluation is unit-cost here. -/
def thinWorkRun (R : α → α → Prop) [DecidableRel R] : List α → List α × Nat
  | [] => ([], 1)
  | x :: xs =>
      let tail := thinWorkRun R xs
      let step := bumpWorkRun R x tail.1
      (step.1, tail.2 + step.2 + 1)

theorem bumpWorkRun_value (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    (bumpWorkRun R x xs).1 = bump R x xs := by
  cases xs <;> simp only [bumpWorkRun, bump]
  split
  · rfl
  · split <;> rfl

theorem bumpWorkRun_bound (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    (bumpWorkRun R x xs).2 ≤ 5 := by
  cases xs <;> simp only [bumpWorkRun]
  · omega
  · split
    · omega
    · split <;> omega

theorem thinWorkRun_value (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    (thinWorkRun R xs).1 = thinBy R xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [thinWorkRun, bumpWorkRun_value, ih, thinBy, List.foldr_cons]

theorem thinWorkRun_bound (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    (thinWorkRun R xs).2 ≤ 6 * xs.length + 1 := by
  induction xs with
  | nil => simp [thinWorkRun]
  | cons x xs ih =>
      have hs := bumpWorkRun_bound R x (thinWorkRun R xs).1
      simp only [thinWorkRun, List.length_cons]
      omega

theorem thinWorkRun_lower (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    xs.length + 1 ≤ (thinWorkRun R xs).2 := by
  induction xs with
  | nil => simp [thinWorkRun]
  | cons x xs ih => simp only [thinWorkRun, List.length_cons]; omega

/-- One execution records relation calls and richer source work together.
The first guard short-circuits the reverse guard, exactly as in `bump`. -/
def bumpMeasured (R : α → α → Prop) [DecidableRel R] (x : α) :
    List α → Measured (List α) (Nat × Nat)
  | [] => ([x], (0, 2))
  | y :: ys => if R x y then (x :: ys, (1, 3))
    else if R y x then (y :: ys, (2, 4)) else (x :: y :: ys, (2, 5))

def thinMeasured (R : α → α → Prop) [DecidableRel R] :
    List α → Measured (List α) (Nat × Nat)
  | [] => ([], (0, 1))
  | x :: xs => bind (thinMeasured R xs) fun tail =>
      bind (bumpMeasured R x tail) fun out => (out, (0, 1))

theorem bumpMeasured_calls (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    reweight Prod.fst (bumpMeasured R x xs) = bumpRun R x xs := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    by_cases h : R x y
    · simp [bumpMeasured, bumpRun, reweight, h]
    · by_cases h2 : R y x <;> simp [bumpMeasured, bumpRun, reweight, h, h2]

theorem bumpMeasured_work (R : α → α → Prop) [DecidableRel R] (x : α) (xs : List α) :
    reweight Prod.snd (bumpMeasured R x xs) = bumpWorkRun R x xs := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    by_cases h : R x y
    · simp [bumpMeasured, bumpWorkRun, reweight, h]
    · by_cases h2 : R y x <;> simp [bumpMeasured, bumpWorkRun, reweight, h, h2]

theorem thinMeasured_calls (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    reweight Prod.fst (thinMeasured R xs) = thinRun R xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hb := bumpMeasured_calls R x (thinMeasured R xs).1
    have hv := congrArg Prod.fst ih
    have hc := congrArg Prod.snd ih
    have bv := congrArg Prod.fst hb
    have bc := congrArg Prod.snd hb
    simp only [reweight] at hv hc bv bc
    rw [hv] at bv bc
    simp only [thinMeasured, thinRun, bind, reweight, Prod.fst_add,
      Nat.add_zero, bv, bc, hv, hc]

theorem thinMeasured_work (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    reweight Prod.snd (thinMeasured R xs) = thinWorkRun R xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hb := bumpMeasured_work R x (thinMeasured R xs).1
    have hv := congrArg Prod.fst ih
    have hc := congrArg Prod.snd ih
    have bv := congrArg Prod.fst hb
    have bc := congrArg Prod.snd hb
    simp only [reweight] at hv hc bv bc
    rw [hv] at bv bc
    simp only [thinMeasured, thinWorkRun, bind, reweight, Prod.snd_add,
      bv, bc, hv, hc, Nat.add_assoc]

theorem thinMeasured_value (R : α → α → Prop) [DecidableRel R] (xs : List α) :
    (thinMeasured R xs).1 = thinBy R xs := by
  have he := congrArg Prod.fst (thinMeasured_calls R xs)
  exact he.trans (thinRun_value R xs)

end Resources.Thinning

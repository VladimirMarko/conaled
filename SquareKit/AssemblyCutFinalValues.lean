import SquareKit.AssemblyCutUnfold

/-! Extensional finite/full cut coalgebra equations. Tracking is supplied separately. -/
namespace Realizability.Assembly

def cutRollValue (t : Option (Option Nat)) : Option Nat := t.elim (some 0) (Option.map Nat.succ)

def cutUnrollValue : Option Nat → Option (Option Nat)
  | none => some none
  | some 0 => none
  | some (n + 1) => some (some n)

@[simp] theorem cutUnrollValue_roll (t : Option (Option Nat)) :
    cutUnrollValue (cutRollValue t) = t := by
  cases t with
  | none => rfl
  | some n => cases n <;> rfl

@[simp] theorem cutRollValue_unroll (n : Option Nat) :
    cutRollValue (cutUnrollValue n) = n := by
  cases n with
  | none => rfl
  | some n => cases n <;> rfl

@[simp] theorem cutRollValue_test_zero (t : Option (Option Nat)) :
    cutTest (cutRollValue t) 0 ↔ ∃ y, t = some y := by
  cases t with
  | none => simp [cutRollValue, cutTest]
  | some n => cases n <;> simp [cutRollValue, cutTest, Option.elim]

@[simp] theorem cutRollValue_test_succ (t : Option (Option Nat)) (k : Nat) :
    cutTest (cutRollValue t) (k + 1) ↔ ∃ y, t = some y ∧ cutTest y k := by
  cases t with
  | none => simp [cutRollValue, cutTest]
  | some n => cases n <;> simp [cutRollValue, cutTest, Option.elim]

theorem unfoldLength_roll {α : Type*} (c : α → Option α) (x : α) :
    unfoldLength c x = cutRollValue (Option.map (unfoldLength c) (c x)) := by
  apply cutTest_ext
  intro k
  rw [unfoldLength_test]
  cases k with
  | zero => simp [unfoldObserves, unfoldSteps]
  | succ k =>
    rw [cutRollValue_test_succ]
    cases hc : c x with
    | none => simp [unfoldObserves, unfoldSteps_succ_left, hc]
    | some y =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left']
      exact (show unfoldObserves c x (k + 1) ↔ unfoldObserves c y k by
        simp [unfoldObserves, unfoldSteps_succ_left, hc]).trans (unfoldLength_test c y k).symm

theorem unfoldLength_square {α : Type*} (c : α → Option α) (x : α) :
    cutUnrollValue (unfoldLength c x) = Option.map (unfoldLength c) (c x) := by
  rw [unfoldLength_roll, cutUnrollValue_roll]

theorem unfoldLength_unique {α : Type*} (c : α → Option α) (h : α → Option Nat)
    (hh : ∀ x, cutUnrollValue (h x) = Option.map h (c x)) : h = unfoldLength c := by
  have hr : ∀ x, h x = cutRollValue (Option.map h (c x)) := by
    intro x
    rw [← hh x, cutRollValue_unroll]
  have ht : ∀ k x, cutTest (h x) k ↔ unfoldObserves c x k := by
    intro k
    induction k with
    | zero => intro x; rw [hr, cutRollValue_test_zero]; simp [unfoldObserves, unfoldSteps]
    | succ k ih =>
      intro x
      rw [hr, cutRollValue_test_succ]
      cases hc : c x with
      | none => simp [unfoldObserves, unfoldSteps_succ_left, hc]
      | some y =>
        simp only [Option.map_some, Option.some.injEq, exists_eq_left']
        exact (ih y).trans (by simp [unfoldObserves, unfoldSteps_succ_left, hc])
  funext x
  exact cutTest_ext fun k => (ht k x).trans (unfoldLength_test c x k).symm

end Realizability.Assembly

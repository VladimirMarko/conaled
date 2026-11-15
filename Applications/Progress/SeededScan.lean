import Applications.Progress.Processors
import Applications.Progress.SpineObservations
import SquareKit.PartialSpine.Scan

/-!
# Lagged Mealy realization of seed-inclusive scan observations

The existing Mealy execution emits the current accumulator before updating it.
Its finite output is the ordinary scan without the final state; that state is
not silently flushed at end of input. Existing updated-accumulator scanners
retain their separate contracts. Delivery counts are the existing atomic model.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Progress.SeededScan

open SquareKit PartialSpine SpineObservations

universe u
variable {A B S : Type u}

/-- One existing Mealy step emits the old state and stores the updated state. -/
def lagged (f : B → A → B) : Mealy B A B := fun b a => (b, f b a)

theorem runList_lagged (f : B → A → B) (e : B) (xs : List A) :
    runList (lagged f) e xs = (xs.scanl f e).dropLast := by
  induction xs generalizing e with
  | nil => simp [runList]
  | cons a xs ih =>
    change e :: runList (lagged f) (f e a) xs = _
    rw [List.scanl_cons, List.dropLast_cons_of_ne_nil List.scanl_ne_nil, ih]

theorem runList_observation (f : B → A → B) (e : B) (xs : List A) :
    openPrefix (runList (lagged f) e xs) = PartialSpine.scanl f e (openPrefix xs) := by
  rw [runList_lagged, PartialSpine.scanl_openPrefix]

theorem runStream_lagged (f : B → A → B) (e : B) (σ : Stream' A) :
    runStream (lagged f) e σ = scanStates f e σ := by
  funext n
  induction n generalizing e σ with
  | zero => rfl
  | succ n ih =>
    change runStream (lagged f) (f e (σ 0)) (fun k => σ (k + 1)) n =
      scanStates f e σ (n + 1)
    rw [scanStates_shift]
    exact ih _ _

/-- The list machine also tests its empty tail, so its cost is n+1 transitions. -/
theorem finite_evaluates (f : B → A → B) (e : B) (xs : List A) :
    Evaluates (mealyStep (lagged f)) (e, xs, [])
      (xs.scanl f e).dropLast (xs.length + 1) := by
  simpa only [List.nil_append, runList_lagged] using mealy_evaluates (lagged f) e xs []

theorem unfold_lagged (f : B → A → B) (e : B) (input : Coalgebra S A)
    (s : S) (n : Nat) :
    unfold (mealyCoalgebra (lagged f) input) (e, s) n =
      (scanStates f e (Stream'.corec' input s)).take n := by
  rw [unfold_mealy, runList_lagged, unfold_eq_take_corec, scanStates_take_dropLast]

theorem corec_lagged (f : B → A → B) (e : B) (input : Coalgebra S A) (s : S) :
    Stream'.corec' (mealyCoalgebra (lagged f) input) (e, s) =
      scanStates f e (Stream'.corec' input s) := by
  apply Stream'.take_theorem
  intro n
  rw [← unfold_eq_take_corec, unfold_lagged]

/-- Existing observation adequacy transfers the actual guarded implementation. -/
theorem observations_guarded_scan (f : B → A → B) (e : B)
    (input : Coalgebra S A) (s : S) :
    observations (guarded (mealyCoalgebra (lagged f) input)) (e, s) =
      Observations.scanl f e (observations (guarded input) s) := by
  simp only [observations_guarded, corec_lagged, Observations.scanl_stream]

/-- Pausing preserves the ideal while retaining its distinct delivery witnesses. -/
theorem observations_paused_scan (f : B → A → B) (e : B)
    (input : Coalgebra S A) (s : S) :
    observations (paused (mealyCoalgebra (lagged f) input)) (false, (e, s)) =
      Observations.scanl f e (observations (paused input) (false, s)) := by
  simp only [observations_paused, corec_lagged, Observations.scanl_stream]

/-- Actual producer and finite-input machine witnesses share the independent
prefix-fold output. The final-state test is retained only on the list machine. -/
theorem lagged_realizations (f : B → A → B) (e : B)
    (input : Coalgebra S A) (s : S) (n : Nat) :
    Delivers (guarded (mealyCoalgebra (lagged f) input)) (e, s)
        ((scanStates f e (Stream'.corec' input s)).take n)
        (advance (mealyCoalgebra (lagged f) input) (e, s) n) n ∧
      Delivers (paused (mealyCoalgebra (lagged f) input)) (false, (e, s))
        ((scanStates f e (Stream'.corec' input s)).take n)
        (false, advance (mealyCoalgebra (lagged f) input) (e, s) n) (2 * n) ∧
      Evaluates (mealyStep (lagged f)) (e, unfold input s n, [])
        ((scanStates f e (Stream'.corec' input s)).take n) (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [unfold_lagged] using (mealy_realizations (lagged f) input e s n).1
  · simpa only [unfold_lagged] using
      paused_delivery (mealyCoalgebra (lagged f) input) (e, s) n
  · simpa only [unfold_lagged] using (mealy_realizations (lagged f) input e s n).2

/-- The pre-existing updated-state scan instead omits the initial seed. -/
theorem updated_scanList (f : B → A → B) (e : B) (xs : List A) :
    scanList f e xs = (xs.scanl f e).tail := by
  have full : ∀ (b : B) (ys : List A), ys.scanl f b = b :: scanList f b ys := by
    intro b ys
    induction ys generalizing b with
    | nil => simp [scanList]
    | cons a ys ih => simp [scanList, ih]
  rw [full]
  rfl

end Progress.SeededScan

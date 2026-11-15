import Applications.Progress.SeededScan
import Examples.PartialSpineLimits

/-!
# Seeded scan observations consumed by existing constructor budgets

The source's input-strict scan and the existing updated-state scan have different
first values. Independent finite/stream expectations below preserve that offset,
the completed-end flag, and the separate operational delivery counts.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineScans

open Order SquareKit PartialSpine Progress Progress.SpineObservations

universe u
variable {A B S : Type u}

/-- Every constructor-budget consumer sees the independently specified states. -/
theorem scan_allCuts_guarded (f : B → A → B) (e : B) (c : Coalgebra S A) (s : S) :
    PartialSpineLimits.allCuts (Observations.scanl f e (observations (guarded c) s)) =
      fun n => Ideal.principal (openPrefix ((scanStates f e (Stream'.corec' c s)).take n)) := by
  rw [← SeededScan.observations_guarded_scan, PartialSpineLimits.allCuts_guarded]
  funext n
  rw [SeededScan.unfold_lagged]

theorem scan_allCuts_paused (f : B → A → B) (e : B) (c : Coalgebra S A) (s : S) :
    PartialSpineLimits.allCuts (Observations.scanl f e (observations (paused c) (false, s))) =
      fun n => Ideal.principal (openPrefix ((scanStates f e (Stream'.corec' c s)).take n)) := by
  rw [← SeededScan.observations_paused_scan, PartialSpineLimits.allCuts_paused]
  funext n
  rw [SeededScan.unfold_lagged]

theorem finite_views :
    view (PartialSpine.scanl Nat.add 0 (ofList [4, 5, 6])) = ([0, 4, 9, 15], true) ∧
      view (PartialSpine.scanl Nat.add 0 (openPrefix [4, 5, 6])) = ([0, 4, 9], false) := by
  constructor <;> rw [view_scanl] <;> rfl

theorem finite_semantics :
    Observations.scanl Nat.add 0 (Ideal.principal (ofList [4, 5, 6])) =
        Ideal.principal (ofList [0, 4, 9, 15]) ∧
      Observations.scanl Nat.add 0 (Ideal.principal (openPrefix [4, 5, 6])) =
        Ideal.principal (openPrefix [0, 4, 9]) := by
  constructor
  · rw [Observations.scanl_ofList]
    rfl
  · rw [Observations.scanl_principal, PartialSpine.scanl_openPrefix]
    rfl

theorem constructor_distinctions (f : B → A → B) (e : B) (a : A) :
    Observations.scanl f e ⊥ = ⊥ ∧
      Observations.scanl f e (Ideal.principal .nil) =
        Observations.cons e (Ideal.principal .nil) ∧
      Observations.scanl f e (Observations.cons a ⊥) = Observations.cons e ⊥ := by
  refine ⟨Observations.scanl_bottom f e, Observations.scanl_nil f e, ?_⟩
  rw [Observations.scanl_cons, Observations.scanl_bottom]

/-- Existing once-then-silent observations expose only the initial seed. -/
theorem scan_once (f : B → A → B) (e : B) (a : A) :
    Observations.scanl f e (observations PartialSpineProgress.once (some a)) =
      Ideal.principal (.cons e .bottom) := by
  rw [PartialSpineProgress.once_observations, Observations.scanl_principal]
  rfl

/-- No finite evaluation of the silent input means no constructor and no seed. -/
theorem scan_silent (f : B → A → B) (e : B) (next : S → S) (s : S) :
    Observations.scanl f e
      (observations (fun x => .inr (next x) : Producer S A) s) = ⊥ := by
  rw [observations_silent, Observations.scanl_bottom]

theorem heterogeneous_scan :
    view (PartialSpine.scanl (fun xs b => xs ++ [if b then 1 else 0]) ([] : List Nat)
      (ofList [true, false, true])) =
      ([[], [1], [1, 0], [1, 0, 1]], true) := by
  rw [view_scanl]
  rfl

theorem count_scan_prefix :
    (scanStates Nat.add 0 (Stream'.corec' PartialSpineProgress.count 4)).take 3 =
      [0, 4, 9] := by
  rw [← scanStates_take_dropLast, ← unfold_eq_take_corec]
  rfl

theorem count_scan_observations :
    PartialSpineLimits.allCuts
        (Observations.scanl Nat.add 0 (observations (guarded PartialSpineProgress.count) 4)) 3 =
        Ideal.principal (openPrefix [0, 4, 9]) ∧
      PartialSpineLimits.allCuts
        (Observations.scanl Nat.add 0
          (observations (paused PartialSpineProgress.count) (false, 4))) 3 =
        Ideal.principal (openPrefix [0, 4, 9]) := by
  constructor
  · simp only [scan_allCuts_guarded, count_scan_prefix]
  · simp only [scan_allCuts_paused, count_scan_prefix]

/-- Three lagged values have 3/6 producer transitions, and 4 finite-machine
transitions. The machine does not claim the completed four-value scan. -/
theorem count_lagged_realizations :
    Delivers
        (guarded (mealyCoalgebra (SeededScan.lagged Nat.add) PartialSpineProgress.count))
        (0, 4) [0, 4, 9] (15, 7) 3 ∧
      Delivers
        (paused (mealyCoalgebra (SeededScan.lagged Nat.add) PartialSpineProgress.count))
        (false, (0, 4)) [0, 4, 9] (false, (15, 7)) 6 ∧
      Evaluates (mealyStep (SeededScan.lagged Nat.add))
        (0, [4, 5, 6], []) [0, 4, 9] 4 := by
  have h := SeededScan.lagged_realizations Nat.add 0 PartialSpineProgress.count 4 3
  rw [count_scan_prefix] at h
  simpa [advance, mealyCoalgebra, SeededScan.lagged, PartialSpineProgress.count, unfold] using h

theorem finite_machine_terminal_test :
    Evaluates (mealyStep (SeededScan.lagged Nat.add))
      (0, [4, 5, 6], []) [0, 4, 9] 4 := by
  simpa using SeededScan.finite_evaluates Nat.add 0 [4, 5, 6]

theorem existing_updated_coalgebra :
    unfold (scanCoalgebra Nat.add PartialSpineProgress.count) (0, 4) 3 = [4, 9, 15] := by
  rw [unfold_scan, SeededScan.updated_scanList]
  rfl

theorem existing_updated_processor :
    prefixOf ((scanProcessor Nat.add 0).meaning
      (Stream'.corec' PartialSpineProgress.count 4)) 3 = [4, 9, 15] := by
  change prefixOf
    (runStream (fun b a : Nat => (b + a, b + a)) 0
      (Stream'.corec' PartialSpineProgress.count 4)) 3 = _
  calc
    _ = runList (fun b a : Nat => (b + a, b + a)) 0
        (prefixOf (Stream'.corec' PartialSpineProgress.count 4) 3) :=
      runStream_prefix (fun b a : Nat => (b + a, b + a)) 0
        (Stream'.corec' PartialSpineProgress.count 4) 3
    _ = [4, 9, 15] := rfl

end PartialSpineScans

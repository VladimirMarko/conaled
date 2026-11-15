import SquareKit.PartialSpine.Concat
import Examples.PartialSpineAppend

/-!
# An emitted inner stream survives a silent outer continuation

The actual emit-once producer supplies an open outer singleton. Flattening its
observations can expose an entire inner counting stream even though the outer
producer is nonproductive. Existing first/allCuts consumers observe the result;
existing input-delivery witnesses do not become a flattening runtime theorem.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineConcat

open Order SquareKit PartialSpine Progress Progress.SpineObservations
open PartialSpineLimits

universe u
variable {α S : Type u}

/-- The actual outer producer leaves an unknown end after its one inner value. -/
theorem concat_once (xs : Observations α) :
    Observations.concat (observations PartialSpineProgress.once (some xs)) =
      Observations.append xs ⊥ := by
  rw [PartialSpineProgress.once_observations, ← Observations.cons_principal,
    Observations.concat_cons, PartialSpine.bottom_eq_bot, Ideal.principal_bot,
    Observations.concat_bottom]

theorem concat_once_guarded (c : Coalgebra S α) (s : S) :
    Observations.concat
      (observations PartialSpineProgress.once (some (observations (guarded c) s))) =
      observations (guarded c) s := by
  rw [concat_once, PartialSpineAppend.append_guarded]

theorem concat_once_paused (c : Coalgebra S α) (s : S) :
    Observations.concat
      (observations PartialSpineProgress.once (some (observations (paused c) (false, s)))) =
      observations (paused c) (false, s) := by
  rw [concat_once, PartialSpineAppend.append_paused]

/-- The first-output consumer uses the public fold/concat law with its nested algebra. -/
theorem first_concat (p : α → Prop) (xss : Observations (Observations α)) :
    first p (Observations.concat xss) =
      Observations.foldr (fun xs r => Observations.foldr (fun a (_ : Prop) => p a) r xs) False xss :=
  Observations.foldr_concat (fun a (_ : Prop) => p a) False
    (fun a => ScottContinuous.const (p a)) xss

/-- Fusion consumes an actual open singleton without requiring its completed end. -/
theorem first_concat_once (p : α → Prop) (xs : Observations α) :
    first p (Observations.concat (observations PartialSpineProgress.once (some xs))) =
      first p xs := by
  rw [first_concat, PartialSpineProgress.once_observations]
  rw [Observations.foldr_principal
    (fun ys (r : Prop) => Observations.foldr (fun a (_ : Prop) => p a) r ys) False
    (fun ys => (Observations.foldr_seed_continuous (fun a (_ : Prop) => p a)
      (fun a => ScottContinuous.const (p a)) ys).monotone)]
  rfl

theorem allCuts_once_guarded (c : Coalgebra S α) (s : S) :
    allCuts (Observations.concat
      (observations PartialSpineProgress.once (some (observations (guarded c) s)))) =
      fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  rw [concat_once_guarded, allCuts_guarded]

theorem allCuts_once_paused (c : Coalgebra S α) (s : S) :
    allCuts (Observations.concat
      (observations PartialSpineProgress.once (some (observations (paused c) (false, s))))) =
      fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  rw [concat_once_paused, allCuts_paused]

theorem counting_first (p : Nat → Prop) (s : Nat) :
    first p (Observations.concat (observations PartialSpineProgress.once
      (some (observations (guarded PartialSpineProgress.count) s)))) = p s ∧
      first p (Observations.concat (observations PartialSpineProgress.once
        (some (observations (paused PartialSpineProgress.count) (false, s))))) = p s := by
  constructor
  · rw [first_concat_once, first_guarded]
    rfl
  · rw [first_concat_once, first_paused]
    rfl

example (c : Coalgebra S α) (s : S) :
    ¬ Productive PartialSpineProgress.once (some (observations (guarded c) s)) ∧
      Observations.concat
        (observations PartialSpineProgress.once (some (observations (guarded c) s))) =
        observations (guarded c) s :=
  ⟨PartialSpineProgress.once_not_productive _, concat_once_guarded c s⟩

-- The counts are witnesses for the inner producers, not a nested flattening scheduler.
example :
    allCuts (Observations.concat (observations PartialSpineProgress.once
      (some (observations (guarded PartialSpineProgress.count) 4)))) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      allCuts (Observations.concat (observations PartialSpineProgress.once
        (some (observations (paused PartialSpineProgress.count) (false, 4))))) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6] 7 3 ∧
      Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6] (false, 7) 6 := by
  rw [allCuts_once_guarded, allCuts_once_paused]
  exact ⟨rfl, rfl, PartialSpineProgress.count_deliveries 4 3⟩

example (tail : Observations (Observations Nat)) :
    allCuts (Observations.concat
      (Observations.cons (observations (guarded PartialSpineProgress.count) 4) tail)) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) := by
  rw [observations_guarded, Observations.concat_infinite_first, allCuts_stream]
  rfl

example : Observations.concat (⊥ : Observations (Observations α)) = ⊥ ∧
    Observations.concat (Ideal.principal (.nil : PartialSpine (Observations α))) =
      Ideal.principal .nil ∧
    (Ideal.principal (.nil : PartialSpine α) : Observations α) ≠ ⊥ := by
  refine ⟨Observations.concat_bottom, Observations.concat_nil, ?_⟩
  intro same
  have finite := principal_injective same
  cases finite

example (a : α) : Observations.concat
    (Observations.cons (⊥ : Observations α)
      (Observations.cons (Ideal.principal (ofList [a])) (Ideal.principal .nil))) = ⊥ := by
  rw [Observations.concat_cons, Observations.append_bottom]

example : Observations.concat (Ideal.principal
    (ofList (([[], [1, 2], [], [3], []] : List (List Nat)).map
      fun xs => Ideal.principal (ofList xs)))) = Ideal.principal (ofList [1, 2, 3]) := by
  calc
    _ = Ideal.principal (ofList (([[], [1, 2], [], [3], []] : List (List Nat)).flatten)) :=
      Observations.concat_ofList _
    _ = _ := rfl

end PartialSpineConcat

import SquareKit.PartialSpine.TakeWhile
import Examples.PartialSpineLimits

/-!
# A failed input test completes an output prefix

Actual guarded and paused input producers supply the same counting observations.
False and undefined tests produce different output ends. The existing first and
all-cuts consumers expose that difference; input deliveries retain their own
operational meaning. No completed-output producer is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineTakeWhile

open Order SquareKit PartialSpine Progress Progress.SpineObservations
open PartialSpineLimits

universe u
variable {α S : Type u}

theorem takeWhile_guarded (p : α → Option Bool) (c : Coalgebra S α) (s : S)
    (accepted : ∀ n, p (Stream'.corec' c s n) = some true) :
    Observations.takeWhile p (observations (guarded c) s) = observations (guarded c) s := by
  rw [observations_guarded]
  exact Observations.takeWhile_stream p _ accepted

theorem takeWhile_paused (p : α → Option Bool) (c : Coalgebra S α) (s : S)
    (accepted : ∀ n, p (Stream'.corec' c s n) = some true) :
    Observations.takeWhile p (observations (paused c) (false, s)) =
      observations (paused c) (false, s) := by
  rw [observations_paused]
  exact Observations.takeWhile_stream p _ accepted

def belowSeven (n : Nat) : Option Bool := some (decide (n < 7))
def undefinedFromSeven (n : Nat) : Option Bool := if n < 7 then some true else none

private theorem belowSeven_prefix : ∀ n ∈ ([4, 5, 6] : List Nat), belowSeven n = some true := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;> rfl

private theorem undefinedFromSeven_prefix :
    ∀ n ∈ ([4, 5, 6] : List Nat), undefinedFromSeven n = some true := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;> rfl

private theorem counting_cons (s : Nat) :
    observations (guarded PartialSpineProgress.count) s =
      Observations.cons s (observations (guarded PartialSpineProgress.count) (s + 1)) := by
  calc
    _ = stream (Stream'.corec' PartialSpineProgress.count s) := observations_guarded _ s
    _ = stream (Stream'.cons s (Stream'.corec' PartialSpineProgress.count (s + 1))) :=
      congrArg stream (Stream'.corec'_eq PartialSpineProgress.count s)
    _ = Observations.cons s (stream (Stream'.corec' PartialSpineProgress.count (s + 1))) :=
      Observations.stream_cons _
    _ = _ := congrArg (Observations.cons s) (observations_guarded _ (s + 1)).symm

private theorem counting_boundary :
    observations (guarded PartialSpineProgress.count) 4 =
      Observations.append (Ideal.principal (ofList [4, 5, 6]))
        (Observations.cons 7 (observations (guarded PartialSpineProgress.count) 8)) := by
  rw [Observations.append_ofList_left]
  change observations (guarded PartialSpineProgress.count) 4 =
    Observations.cons 4 (Observations.cons 5 (Observations.cons 6
      (Observations.cons 7 (observations (guarded PartialSpineProgress.count) 8))))
  rw [counting_cons 4, counting_cons 5, counting_cons 6, counting_cons 7]

/-- The fourth observed input test seals a completed three-element output. -/
theorem counting_false :
    Observations.takeWhile belowSeven (observations (guarded PartialSpineProgress.count) 4) =
        Ideal.principal (ofList [4, 5, 6]) ∧
      Observations.takeWhile belowSeven
        (observations (paused PartialSpineProgress.count) (false, 4)) =
        Ideal.principal (ofList [4, 5, 6]) := by
  have result : Observations.takeWhile belowSeven
      (observations (guarded PartialSpineProgress.count) 4) =
      Ideal.principal (ofList [4, 5, 6]) := by
    rw [counting_boundary]
    exact Observations.takeWhile_stops belowSeven [4, 5, 6] 7 belowSeven_prefix rfl _
  refine ⟨result, ?_⟩
  rw [← guarded_paused_observations]
  exact result

/-- Undefined at the same boundary leaves exactly the same labels with an open end. -/
theorem counting_undefined :
    Observations.takeWhile undefinedFromSeven
        (observations (guarded PartialSpineProgress.count) 4) =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      Observations.takeWhile undefinedFromSeven
        (observations (paused PartialSpineProgress.count) (false, 4)) =
        Ideal.principal (openPrefix [4, 5, 6]) := by
  have result : Observations.takeWhile undefinedFromSeven
      (observations (guarded PartialSpineProgress.count) 4) =
      Ideal.principal (openPrefix [4, 5, 6]) := by
    rw [counting_boundary,
      Observations.takeWhile_undefined_after_prefix undefinedFromSeven [4, 5, 6] 7
        undefinedFromSeven_prefix rfl,
      Observations.append_ofList_left]
    change Observations.cons 4 (Observations.cons 5 (Observations.cons 6 ⊥)) =
      Ideal.principal (.cons 4 (.cons 5 (.cons 6 .bottom)))
    rw [Observations.cons_bottom, Observations.cons_principal, Observations.cons_principal]
  refine ⟨result, ?_⟩
  rw [← guarded_paused_observations]
  exact result

theorem counting_first (p : Nat → Prop) :
    first p (Observations.takeWhile belowSeven
      (observations (guarded PartialSpineProgress.count) 4)) = p 4 := by
  rw [counting_false.1]
  change first p (Ideal.principal (.cons 4 (ofList [5, 6]))) = p 4
  rw [← Observations.cons_principal, first_cons]

/-- A budget reaching the end distinguishes the two semantic results. -/
theorem counting_end_cuts :
    allCuts (Observations.takeWhile belowSeven
        (observations (guarded PartialSpineProgress.count) 4)) 4 =
        Ideal.principal (ofList [4, 5, 6]) ∧
      allCuts (Observations.takeWhile undefinedFromSeven
        (observations (paused PartialSpineProgress.count) (false, 4))) 4 =
        Ideal.principal (openPrefix [4, 5, 6]) := by
  rw [counting_false.1, counting_undefined.2, allCuts_apply, allCuts_apply,
    truncate_principal, truncate_principal]
  exact ⟨rfl, rfl⟩

example :
    (view (ofList ([4, 5, 6] : List Nat))).2 = true ∧
      (view (openPrefix ([4, 5, 6] : List Nat))).2 = false ∧
      Observations.takeWhile belowSeven
          (observations (guarded PartialSpineProgress.count) 4) ≠
        Observations.takeWhile undefinedFromSeven
          (observations (paused PartialSpineProgress.count) (false, 4)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [counting_false.1, counting_undefined.2]
  intro same
  have flags := congrArg (fun s => (view s).2) (principal_injective same)
  simp only [view_ofList, view_openPrefix] at flags
  cases flags

-- These are witnesses for available input tests, not a runtime theorem for takeWhile.
example :
    Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6, 7] 8 4 ∧
      Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6, 7] (false, 8) 8 := by
  simpa [unfold, advance, PartialSpineProgress.count] using PartialSpineProgress.count_deliveries 4 4

example :
    allCuts (Observations.takeWhile (fun _ : Nat => some true)
        (observations (guarded PartialSpineProgress.count) 4)) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      allCuts (Observations.takeWhile (fun _ : Nat => some true)
        (observations (paused PartialSpineProgress.count) (false, 4))) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) := by
  rw [takeWhile_guarded _ _ _ (fun _ => rfl), takeWhile_paused _ _ _ (fun _ => rfl),
    allCuts_guarded, allCuts_paused]
  exact ⟨rfl, rfl⟩

example (a : α) :
    Observations.takeWhile (fun _ => some true)
        (observations PartialSpineProgress.once (some a)) = Ideal.principal (.cons a .bottom) ∧
      Observations.takeWhile (fun _ => some false)
        (observations PartialSpineProgress.once (some a)) = Ideal.principal .nil ∧
      Observations.takeWhile (fun _ => none)
        (observations PartialSpineProgress.once (some a)) = ⊥ := by
  rw [PartialSpineProgress.once_observations, ← Observations.cons_principal]
  rw [Observations.takeWhile_cons_true _ a _ rfl,
    Observations.takeWhile_cons_false _ a _ rfl,
    Observations.takeWhile_cons_undefined _ a _ rfl]
  change Observations.cons a (Observations.takeWhile (fun _ => some true) ⊥) =
      Observations.cons a ⊥ ∧
    (Ideal.principal (.nil : PartialSpine α) : Observations α) = Ideal.principal .nil ∧
    (⊥ : Observations α) = ⊥
  rw [Observations.takeWhile_bottom, Observations.cons_bottom]
  exact ⟨rfl, rfl, rfl⟩

example (s : Nat) : Observations.takeWhile (fun _ : Nat => some false)
    (observations (fun n => .inr (n + 1) : Producer Nat Nat) s) = ⊥ := by
  rw [observations_silent, Observations.takeWhile_bottom]

example :
    Observations.takeWhile (fun _ : α => none) (Ideal.principal .nil) = Ideal.principal .nil ∧
      Observations.takeWhile (fun _ : α => none) ⊥ = ⊥ ∧
      (Ideal.principal (.nil : PartialSpine α) : Observations α) ≠ ⊥ := by
  refine ⟨Observations.takeWhile_nil _, Observations.takeWhile_bottom _, ?_⟩
  intro same
  have finite := principal_injective same
  cases finite

example : Observations.takeWhile belowSeven (Ideal.principal (openPrefix [4, 5, 6])) =
      Ideal.principal (openPrefix [4, 5, 6]) ∧
    Observations.takeWhile belowSeven (Ideal.principal (openPrefix [4, 5, 6])) ≠
      Ideal.principal (ofList [4, 5, 6]) := by
  rw [Observations.takeWhile_openPrefix belowSeven [4, 5, 6] belowSeven_prefix]
  refine ⟨rfl, ?_⟩
  intro same
  have flags := congrArg (fun s => (view s).2) (principal_injective same)
  simp only [view_openPrefix, view_ofList] at flags
  cases flags

example (suffix : Observations Nat) :
    Observations.takeWhile belowSeven (Observations.append (Ideal.principal (ofList [4, 5, 6]))
      (Observations.cons 7 suffix)) =
    Observations.takeWhile belowSeven (Observations.append (Ideal.principal (ofList [4, 5, 6]))
      (Observations.cons 7 (observations (guarded PartialSpineProgress.count) 8))) :=
  Observations.takeWhile_suffix_independent belowSeven [4, 5, 6] 7 belowSeven_prefix rfl _ _

example : Observations.takeWhile (fun n : Nat => some (decide (n < 7)))
    (Ideal.principal (ofList [4, 5, 6, 7, 0])) = Ideal.principal (ofList [4, 5, 6]) := by
  rw [Observations.takeWhile_ofList]
  rfl

/-- A completed result cannot be the ideal of a producer with no end transition. -/
theorem stopped_not_producer {T : Type} (step : Producer T Nat) (s : T) :
    Observations.takeWhile belowSeven (observations (guarded PartialSpineProgress.count) 4) ≠
      observations step s := by
  rw [counting_false.1]
  intro same
  apply ofList_not_mem step s [4, 5, 6]
  rw [← same]
  exact Ideal.mem_principal_self

end PartialSpineTakeWhile

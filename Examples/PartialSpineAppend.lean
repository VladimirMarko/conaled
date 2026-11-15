import SquareKit.PartialSpine.Append
import Examples.PartialSpineLimits

/-!
# Appended producer observations consumed through finite demands

Actual guarded and paused producers hide any appended suffix. Their observation
equalities feed the existing function-valued truncation and first-output
consumers. Input delivery counts remain separate from denotational append.
A completed finite prefix, unlike an open one, exposes the following stream.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineAppend

open Order SquareKit PartialSpine Progress Progress.SpineObservations
open PartialSpineLimits

universe u
variable {α S : Type u}

theorem append_guarded (c : Coalgebra S α) (s : S) (suffix : Observations α) :
    Observations.append (observations (guarded c) s) suffix = observations (guarded c) s := by
  rw [observations_guarded, Observations.append_stream]

theorem append_paused (c : Coalgebra S α) (s : S) (suffix : Observations α) :
    Observations.append (observations (paused c) (false, s)) suffix =
      observations (paused c) (false, s) := by
  rw [observations_paused, Observations.append_stream]

theorem allCuts_append_guarded (c : Coalgebra S α) (s : S) (suffix : Observations α) :
    allCuts (Observations.append (observations (guarded c) s) suffix) =
      fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  rw [append_guarded, allCuts_guarded]

theorem allCuts_append_paused (c : Coalgebra S α) (s : S) (suffix : Observations α) :
    allCuts (Observations.append (observations (paused c) (false, s)) suffix) =
      fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  rw [append_paused, allCuts_paused]

/-- Equal function-valued consumers retain the producer's distinct input witnesses. -/
theorem counting_allCuts_and_deliveries (s n : Nat) (suffix : Observations Nat) :
    allCuts (Observations.append (observations (guarded PartialSpineProgress.count) s) suffix) =
        (fun k => Ideal.principal (openPrefix (unfold PartialSpineProgress.count s k))) ∧
      allCuts (Observations.append
        (observations (paused PartialSpineProgress.count) (false, s)) suffix) =
        (fun k => Ideal.principal (openPrefix (unfold PartialSpineProgress.count s k))) ∧
      Delivers (guarded PartialSpineProgress.count) s (unfold PartialSpineProgress.count s n)
        (advance PartialSpineProgress.count s n) n ∧
      Delivers (paused PartialSpineProgress.count) (false, s) (unfold PartialSpineProgress.count s n)
        (false, advance PartialSpineProgress.count s n) (2 * n) :=
  ⟨allCuts_append_guarded _ s suffix, allCuts_append_paused _ s suffix,
    PartialSpineProgress.count_deliveries s n⟩

example (suffix : Observations Nat) :
    allCuts (Observations.append (observations (guarded PartialSpineProgress.count) 4) suffix) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      allCuts (Observations.append
        (observations (paused PartialSpineProgress.count) (false, 4)) suffix) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6] 7 3 ∧
      Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6] (false, 7) 6 := by
  obtain ⟨guardedCuts, pausedCuts, deliveries⟩ := counting_allCuts_and_deliveries 4 3 suffix
  rw [guardedCuts, pausedCuts]
  exact ⟨rfl, rfl, deliveries⟩

/-- The fold/append law passes the interpreted suffix to the existing first consumer. -/
theorem first_append (p : α → Prop) (xs ys : Observations α) :
    first p (Observations.append xs ys) =
      Observations.foldr (fun a _ => p a) (first p ys) xs :=
  Observations.foldr_append (fun a _ => p a) False (fun a => ScottContinuous.const (p a)) xs ys

theorem counting_first (p : Nat → Prop) (s : Nat) (suffix : Observations Nat) :
    first p (Observations.append (observations (guarded PartialSpineProgress.count) s) suffix) =
        p s ∧
      first p (Observations.append
        (observations (paused PartialSpineProgress.count) (false, s)) suffix) = p s := by
  rw [append_guarded, append_paused, first_guarded, first_paused]
  exact ⟨rfl, rfl⟩

/-- Prepending a completed finite list connects to the independent standard stream. -/
theorem allCuts_completed_guarded (pre : List α) (c : Coalgebra S α) (s : S) :
    allCuts (Observations.append (Ideal.principal (ofList pre)) (observations (guarded c) s)) =
      fun n => Ideal.principal
        (openPrefix (Stream'.take n (Stream'.appendStream' pre (Stream'.corec' c s)))) := by
  rw [observations_guarded, Observations.append_ofList_stream, allCuts_stream]

/-- Every budget sees only the fixed open prefix, whatever suffix follows it. -/
theorem allCuts_openPrefix (pre : List α) (suffix : Observations α) :
    allCuts (Observations.append (Ideal.principal (openPrefix pre)) suffix) =
      fun n => Ideal.principal (openPrefix (pre.take n)) := by
  funext n
  rw [Observations.append_openPrefix, allCuts_apply, truncate_principal, cut_openPrefix]

example :
    allCuts (Observations.append (Ideal.principal (ofList [1, 2]))
      (observations (guarded PartialSpineProgress.count) 4)) 4 =
        Ideal.principal (openPrefix [1, 2, 4, 5]) ∧
      allCuts (Observations.append (Ideal.principal (openPrefix [1, 2]))
        (observations (guarded PartialSpineProgress.count) 4)) 4 =
        Ideal.principal (openPrefix [1, 2]) := by
  rw [allCuts_completed_guarded, allCuts_openPrefix]
  exact ⟨rfl, rfl⟩

example (p : Nat → Prop) :
    first p (Observations.append (Ideal.principal .nil)
      (observations (paused PartialSpineProgress.count) (false, 4))) = p 4 := by
  rw [first_append]
  exact (Observations.foldr_nil (fun a (_ : Prop) => p a)
    (first p (observations (paused PartialSpineProgress.count) (false, 4)))
    (fun a => (ScottContinuous.const (p a)).monotone)).trans
      (first_paused p PartialSpineProgress.count 4)

example (a : α) :
    Observations.append (⊥ : Observations α) (Ideal.principal (ofList [a])) = ⊥ :=
  Observations.append_bottom _

example (a : α) :
    ScottContinuous (Observations.append (Ideal.principal (ofList [a]))) ∧
      Observations.append (Ideal.principal (ofList [a])) ⊥ ≠ ⊥ := by
  refine ⟨Observations.append_right_continuous _, ?_⟩
  rw [Observations.append_ofList_left]
  exact Observations.cons_not_strict a

end PartialSpineAppend

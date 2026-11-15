import Applications.Progress.SpineMaps
import Examples.PartialSpineLimits

/-!
# Mapped producers consumed through existing observations

The public map/fold laws connect the general head operation with the existing
first-output predicate. Constructor budgets consume the same mapped guarded
and paused streams; exact delivery witnesses retain their distinct transition
counts. Finite cases distinguish unknown ends from completed nil.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineMap

open Order SquareKit PartialSpine Progress Progress.SpineObservations PartialSpineLimits

universe u v
variable {α S : Type u} {β : Type v}

/-- The new operations recover the existing first-output consumer on every ideal. -/
theorem head_map_first (p : α → Prop) (I : Observations α) :
    Observations.head (Observations.map p I) = first p I :=
  Observations.foldr_map (fun (P : Prop) (_ : Prop) => P) p False
    (fun P => ScottContinuous.const P) I

section Producers

variable {A B : Type u}

theorem allCuts_map_guarded (f : A → B) (c : Coalgebra S A) (s : S) :
    allCuts (Observations.map f (observations (guarded c) s)) =
      fun n => Ideal.principal (openPrefix ((unfold c s n).map f)) := by
  rw [map_observations_guarded, allCuts_guarded]
  funext n
  rw [unfold_map]

theorem allCuts_map_paused (f : A → B) (c : Coalgebra S A) (s : S) :
    allCuts (Observations.map f (observations (paused c) (false, s))) =
      fun n => Ideal.principal (openPrefix ((unfold c s n).map f)) := by
  rw [map_observations_paused, allCuts_paused]
  funext n
  rw [unfold_map]

/-- The actual mapped guarded producer is consumed through map fusion and first. -/
theorem head_map_guarded (p : B → Prop) (f : A → B) (c : Coalgebra S A) (s : S) :
    Observations.head (Observations.map p (observations (guarded (mapCoalgebra f c)) s)) =
      p (f (c s).1) := by
  rw [← map_observations_guarded f c s, Observations.map_fusion, head_map_first, first_guarded]

theorem head_map_paused (p : B → Prop) (f : A → B) (c : Coalgebra S A) (s : S) :
    Observations.head
        (Observations.map p (observations (paused (mapCoalgebra f c)) (false, s))) =
      p (f (c s).1) := by
  rw [← map_observations_paused f c s, Observations.map_fusion, head_map_first, first_paused]

end Producers

/-- Semantic prefix consumption accompanies the mapped producers' existing costs. -/
theorem mapped_counting_truncations_and_costs (f : Nat → Nat) (s n : Nat) :
    truncate n (Observations.map f (observations (guarded PartialSpineProgress.count) s)) =
        Ideal.principal (openPrefix ((unfold PartialSpineProgress.count s n).map f)) ∧
      truncate n (Observations.map f
        (observations (paused PartialSpineProgress.count) (false, s))) =
        Ideal.principal (openPrefix ((unfold PartialSpineProgress.count s n).map f)) ∧
      Delivers (guarded (mapCoalgebra f PartialSpineProgress.count)) s
        ((unfold PartialSpineProgress.count s n).map f)
        (advance (mapCoalgebra f PartialSpineProgress.count) s n) n ∧
      Delivers (paused (mapCoalgebra f PartialSpineProgress.count)) (false, s)
        ((unfold PartialSpineProgress.count s n).map f)
        (false, advance (mapCoalgebra f PartialSpineProgress.count) s n) (2 * n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← allCuts_apply, allCuts_map_guarded]
  · rw [← allCuts_apply, allCuts_map_paused]
  · simpa only [unfold_map] using guarded_delivery (mapCoalgebra f PartialSpineProgress.count) s n
  · simpa only [unfold_map] using paused_delivery (mapCoalgebra f PartialSpineProgress.count) s n

example :
    truncate 3 (Observations.map (fun n => n + 10)
      (observations (guarded PartialSpineProgress.count) 4)) =
        Ideal.principal (openPrefix [14, 15, 16]) ∧
      truncate 3 (Observations.map (fun n => n + 10)
        (observations (paused PartialSpineProgress.count) (false, 4))) =
        Ideal.principal (openPrefix [14, 15, 16]) ∧
      Delivers (guarded (mapCoalgebra (fun n => n + 10) PartialSpineProgress.count))
        4 [14, 15, 16] 7 3 ∧
      Delivers (paused (mapCoalgebra (fun n => n + 10) PartialSpineProgress.count))
        (false, 4) [14, 15, 16] (false, 7) 6 := by
  simpa [unfold, advance, PartialSpineProgress.count, mapCoalgebra] using
    mapped_counting_truncations_and_costs (fun n => n + 10) 4 3

example (p : Nat → Prop) :
    Observations.head (Observations.map p (observations
      (guarded (mapCoalgebra (fun n => n + 10) PartialSpineProgress.count)) 4)) = p 14 ∧
      Observations.head (Observations.map p (observations
        (paused (mapCoalgebra (fun n => n + 10) PartialSpineProgress.count)) (false, 4))) = p 14 :=
  ⟨head_map_guarded p _ _ 4, head_map_paused p _ _ 4⟩

-- Add ten first, then double: the reversed composition would begin at eighteen.
example :
    allCuts (Observations.map (fun n => n * 2) (Observations.map (fun n => n + 10)
      (observations (guarded PartialSpineProgress.count) 4))) 3 =
        Ideal.principal (openPrefix [28, 30, 32]) := by
  rw [Observations.map_fusion, allCuts_map_guarded]
  rfl

/-- A finite producer can expose its mapped first label while leaving its end unknown. -/
theorem map_once (f : α → β) (a : α) :
    Observations.map f (observations PartialSpineProgress.once (some a)) =
      Ideal.principal (.cons (f a) .bottom) := by
  rw [PartialSpineProgress.once_observations, Observations.map_principal]
  rfl

example : Observations.map (fun n => n + 10)
      (observations PartialSpineProgress.once (some 4)) =
        Ideal.principal (.cons 14 .bottom) ∧
    Observations.map (fun n => n + 10) (Ideal.principal (ofList [4])) =
        Ideal.principal (.cons 14 .nil) := by
  constructor
  · exact map_once _ 4
  · rw [Observations.map_ofList]
    rfl

example (f : α → β) (a : α) :
    Observations.map f (Ideal.principal (openPrefix [a])) ≠
      Observations.map f (Ideal.principal (ofList [a])) := by
  rw [Observations.map_principal, Observations.map_principal,
    PartialSpine.map_openPrefix, PartialSpine.map_ofList]
  intro same
  have ends := congrArg (fun s => (view s).2) (principal_injective same)
  simp only [view_openPrefix, view_ofList] at ends
  cases ends

example [CompletePartialOrder β] (f : α → β) (a : α) (I : Observations α) :
    Observations.head (Observations.map f (Observations.cons a I)) = f a := by
  rw [Observations.map_cons, Observations.head_cons]

example [CompletePartialOrder α] :
    Observations.head (⊥ : Observations α) =
        Observations.head (Ideal.principal .nil) ∧
      (⊥ : Observations α) ≠ Ideal.principal .nil := by
  constructor
  · rw [Observations.head_bottom, Observations.head_nil]
  · intro same
    have finite := principal_injective same
    cases finite

-- A different standard CPO instantiates the finite refinement without an Option order.
example : Observations.head (Ideal.principal (ofList [({14} : Set Nat), {16}])) = {14} := by
  rw [Observations.head_ofList]
  rfl

end PartialSpineMap

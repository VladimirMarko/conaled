import Applications.Progress.SpineFilters
import Examples.PartialSpineMap

/-!
# Partial filter order and actual counting observations

The existing first/head-map consumers use public fold/filter fusion. Actual
deliveries distinguish five consumed inputs from a six-element underlying
prefix with the same filtered values. Partial test order and known end flags
remain separate from total producer behavior and productivity.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineFilter

open Order SquareKit PartialSpine Progress Progress.SpineObservations PartialSpineLimits

universe u
variable {α S A : Type u}

theorem first_filter (q : α → Prop) (p : α → Option Bool) (I : Observations α) :
    first q (Observations.filter p I) =
      Observations.foldr (Observations.filteredStep (fun a (_ : Prop) => q a) p) False I :=
  Observations.foldr_filter (fun a (_ : Prop) => q a) False
    (fun a => ScottContinuous.const (q a)) p I

/-- The first consumer reaches a kept constructor through the public fused fold. -/
theorem first_filter_cons_accept (q : α → Prop) (p : α → Option Bool) (a : α)
    (I : Observations α) (accepted : p a = some true) :
    first q (Observations.filter p (Observations.cons a I)) = q a := by
  rw [first_filter]
  let f : α → Prop → Prop := fun a _ => q a
  have continuous : ∀ b, ScottContinuous (Observations.filteredStep f p b) :=
    fun b => Observations.filteredStep_continuous f (fun a => ScottContinuous.const (q a)) p b
  change Observations.foldr (Observations.filteredStep f p) False (Observations.cons a I) = q a
  rw [Observations.foldr_cons (Observations.filteredStep f p) False
    (fun b => (continuous b).monotone) a (continuous a) I]
  simp only [Observations.filteredStep, accepted, f]

theorem first_filtered_producer (q : A → Prop) (p : A → Bool) (c : Coalgebra S A) (s : S) :
    first q (observations (filterProducer p c) s) =
      Observations.foldr
        (Observations.filteredStep (fun a (_ : Prop) => q a) (fun a => some (p a))) False
        (observations (guarded c) s) := by
  rw [observations_filterProducer, first_filter]

theorem head_map_filtered_producer (q : A → Prop) (p : A → Bool) (c : Coalgebra S A) (s : S) :
    Observations.head (Observations.map q (observations (filterProducer p c) s)) =
      Observations.foldr
        (Observations.filteredStep (fun a (_ : Prop) => q a) (fun a => some (p a))) False
        (observations (guarded c) s) := by
  rw [PartialSpineMap.head_map_first, first_filtered_producer]

theorem first_filter_guarded_accept (q : A → Prop) (p : A → Bool)
    (c : Coalgebra S A) (s : S) (accepted : p (c s).1 = true) :
    first q (observations (filterProducer p c) s) = q (c s).1 := by
  rw [observations_filterProducer, observations_guarded, Observations.stream_cons]
  apply first_filter_cons_accept
  change some (p (c s).1) = some true
  rw [accepted]

/-- A concrete total predicate for the existing counting coalgebra. -/
def even (n : Nat) : Bool := decide (n % 2 = 0)

/-- The last emission occurs at input eight; rejected nine is not consumed. -/
theorem even_counting_delivery :
    Delivers (filterProducer even PartialSpineProgress.count) 4 [4, 6, 8] 9 5 := by
  have first : Evaluates (filterProducer even PartialSpineProgress.count) 4 (4, 5) 1 :=
    .done rfl
  have second : Evaluates (filterProducer even PartialSpineProgress.count) 5 (6, 7) 2 :=
    .next rfl (.done rfl)
  have third : Evaluates (filterProducer even PartialSpineProgress.count) 7 (8, 9) 2 :=
    .next rfl (.done rfl)
  exact Delivers.cons first (Delivers.cons second (Delivers.cons third (.nil 9)))

theorem even_counting_not_six (t : Nat) :
    ¬ Delivers (filterProducer even PartialSpineProgress.count) 4 [4, 6, 8] t 6 := by
  intro delivery
  have cost := (even_counting_delivery.unique delivery).2
  omega

/-- The converse really needs its at-most bound when the input prefix ends in rejection. -/
theorem even_counting_six_prefix :
    (unfold PartialSpineProgress.count 4 6).filter even = [4, 6, 8] ∧
      (∃ k ≤ 6, Delivers (filterProducer even PartialSpineProgress.count) 4 [4, 6, 8]
        (advance PartialSpineProgress.count 4 k) k) ∧
      (∀ t, ¬ Delivers (filterProducer even PartialSpineProgress.count) 4 [4, 6, 8] t 6) := by
  refine ⟨rfl, ?_, even_counting_not_six⟩
  simpa [unfold, PartialSpineProgress.count, even] using
    filter_unfold_delivery even PartialSpineProgress.count 4 6

/-- Actual finite observations feed the existing head/map and first consumers. -/
theorem even_counting_observation_and_head (q : Nat → Prop) :
    openPrefix [4, 6, 8] ∈ observations (filterProducer even PartialSpineProgress.count) 4 ∧
      Observations.head
        (Observations.map q (observations (filterProducer even PartialSpineProgress.count) 4)) = q 4 := by
  constructor
  · exact (openPrefix_mem_iff _ _ _).mpr ⟨9, 5, even_counting_delivery⟩
  · rw [PartialSpineMap.head_map_first]
    exact first_filter_guarded_accept q even PartialSpineProgress.count 4 rfl

example :
    Observations.filter (fun n => some (decide (6 ≤ n)))
        (observations (filterProducer even PartialSpineProgress.count) 4) =
      observations
        (filterProducer (fun n => even n && decide (6 ≤ n)) PartialSpineProgress.count) 4 ∧
      Delivers (filterProducer (fun n => even n && decide (6 ≤ n)) PartialSpineProgress.count)
        4 [6] 7 3 := by
  refine ⟨filter_observations_fusion (fun n => decide (6 ≤ n)) even _ 4, ?_⟩
  have first : Evaluates
      (filterProducer (fun n => even n && decide (6 ≤ n)) PartialSpineProgress.count)
      4 (6, 7) 3 :=
    .next rfl (.next rfl (.done rfl))
  exact Delivers.cons first (.nil 7)

/-- Inner rejection avoids an undefined outer test; reversing them changes the ideal. -/
theorem partial_predicate_order (a : α) :
    Observations.filter (fun _ => none)
        (Observations.filter (fun _ => some false) (Ideal.principal (ofList [a]))) =
        Ideal.principal .nil ∧
      Observations.filter (fun _ => some false)
        (Observations.filter (fun _ => none) (Ideal.principal (ofList [a]))) = ⊥ ∧
      Observations.filter (fun _ => none)
          (Observations.filter (fun _ => some false) (Ideal.principal (ofList [a]))) ≠
        Observations.filter (fun _ => some false)
          (Observations.filter (fun _ => none) (Ideal.principal (ofList [a]))) := by
  have reject_first : Observations.filter (fun _ => none)
      (Observations.filter (fun _ => some false) (Ideal.principal (ofList [a]))) =
      Ideal.principal .nil := by
    rw [Observations.filter_fusion]
    change Observations.filter (fun _ => some false) (Ideal.principal (ofList [a])) = _
    rw [Observations.filter_ofList]
    rfl
  have undefined_first : Observations.filter (fun _ => some false)
      (Observations.filter (fun _ => none) (Ideal.principal (ofList [a]))) = ⊥ := by
    rw [Observations.filter_fusion]
    change Observations.filter (fun _ => none) (Ideal.principal (ofList [a])) = _
    rw [ofList_cons, ← Observations.cons_principal, Observations.filter_cons]
    rfl
  refine ⟨reject_first, undefined_first, ?_⟩
  rw [reject_first, undefined_first]
  intro same
  have finite := principal_injective same
  cases finite

example (a : α) (σ : Stream' α) :
    Observations.filter (fun _ => some false) (Ideal.principal (ofList [a])) =
        Ideal.principal .nil ∧
      Observations.filter (fun _ => some false) (Ideal.principal (openPrefix [a])) = ⊥ ∧
      Observations.filter (fun _ => some false) (stream σ) = ⊥ := by
  refine ⟨?_, ?_, Observations.filter_stream_all_false _ σ (fun _ => rfl)⟩
  · rw [Observations.filter_ofList]
    rfl
  · rw [Observations.filter_openPrefix]
    rfl

example (I : Observations α) : Observations.filter (fun _ => some true) I = I :=
  Observations.filter_true I

/-- Input productivity does not justify filtered-output productivity. -/
theorem all_reject_counting :
    Productive (guarded PartialSpineProgress.count) 4 ∧
      observations (filterProducer (fun _ => false) PartialSpineProgress.count) 4 = ⊥ ∧
      ¬ Productive (filterProducer (fun _ => false) PartialSpineProgress.count) 4 :=
  ⟨guarded_productive _ 4, observations_filter_never _ _ (fun _ => rfl) 4,
    filter_no_match _ _ (fun _ => rfl) 4⟩

end PartialSpineFilter

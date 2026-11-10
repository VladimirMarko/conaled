import Applications.Progress.SpineZips
import Examples.PartialSpineLimits

/-!
# Online labels consumed from actual paired producers

Independent finite expectations distinguish pair order and observed ends.
Existing first/allCuts consumers use the actual paired coalgebra, whose guarded
and paused realizations retain separate finite delivery witnesses.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineZip

open Order SquareKit PartialSpine Progress Progress.SpineObservations

universe u v w
variable {α : Type u} {β : Type v}

/-- A known pair is observable without inspecting an arbitrary continuation. -/
theorem first_zip_cons (p : β × α → Prop) (σ : Stream' β) (a : α)
    (I : Observations α) :
    PartialSpineLimits.first p (Observations.zipStream σ (Observations.cons a I)) =
      p (σ 0, a) := by
  rw [Observations.zipStream_cons, PartialSpineLimits.first_cons]

/-- Projection recovers every ideal, not only completed finite lists. -/
example (σ : Stream' β) (I : Observations α) :
    Observations.map Prod.snd (Observations.zipStream σ I) = I :=
  Observations.map_snd_zipStream σ I

example (n : Nat) (I : Observations α) :
    Observations.map Prod.snd (Observations.labelFrom n I) = I :=
  Observations.map_snd_labelFrom n I

theorem nonzero_finite_views :
    view (PartialSpine.zipStream (fun k => 7 + k) (ofList [4, 9])) =
        ([(7, 4), (8, 9)], true) ∧
      view (PartialSpine.zipStream (fun k => 7 + k) (openPrefix [4, 9])) =
        ([(7, 4), (8, 9)], false) := by
  constructor
  · exact (congrArg view (PartialSpine.zipStream_index_ofList 7 [4, 9])).trans (by rfl)
  · exact (congrArg view (PartialSpine.zipStream_index_openPrefix 7 [4, 9])).trans (by rfl)

theorem nonzero_finite_ideals :
    Observations.labelFrom 7 (Ideal.principal (ofList [4, 9])) =
        Ideal.principal (ofList [(7, 4), (8, 9)]) ∧
      Observations.labelFrom 7 (Ideal.principal (openPrefix [4, 9])) =
        Ideal.principal (openPrefix [(7, 4), (8, 9)]) := by
  constructor
  · exact Observations.labelFrom_ofList 7 [4, 9]
  · exact Observations.labelFrom_openPrefix 7 [4, 9]

example : Observations.label (Ideal.principal (ofList [4, 9])) =
    Ideal.principal (ofList [(0, 4), (1, 9)]) :=
  Observations.label_ofList [4, 9]

/-- The finite view uses independent Boolean labels and natural values. -/
example : Observations.zipStream (fun k : Nat => k == 0)
    (Ideal.principal (ofList [4, 9])) =
      Ideal.principal (ofList [(true, 4), (false, 9)]) :=
  Observations.zipStream_ofList (fun k : Nat => k == 0) [4, 9]

theorem label_nil_ne_bottom (n : Nat) :
    Observations.labelFrom n (Ideal.principal (.nil : PartialSpine α)) ≠
      Observations.labelFrom n ⊥ := by
  intro same
  have original := congrArg (Observations.map Prod.snd) same
  rw [Observations.map_snd_labelFrom, Observations.map_snd_labelFrom] at original
  have impossible : (.nil : PartialSpine α) = .bottom := principal_injective original
  cases impossible

example (σ : Stream' α) : Observations.label (stream σ) = stream (Stream'.enum σ) :=
  Observations.label_stream σ

section Producers

-- The existing Progress coalgebra interface has one common universe.
variable {S T A B : Type w}

theorem first_zip_guarded (p : A × B → Prop) (c : Coalgebra S A)
    (d : Coalgebra T B) (s : S) (t : T) :
    PartialSpineLimits.first p (Observations.zipStream (Stream'.corec' c s)
      (observations (guarded d) t)) = p ((c s).1, (d t).1) := by
  rw [zip_observations_guarded, PartialSpineLimits.first_guarded]
  rfl

theorem first_zip_paused (p : A × B → Prop) (c : Coalgebra S A)
    (d : Coalgebra T B) (s : S) (t : T) :
    PartialSpineLimits.first p (Observations.zipStream (Stream'.corec' c s)
      (observations (paused d) (false, t))) = p ((c s).1, (d t).1) := by
  rw [zip_observations_paused, PartialSpineLimits.first_paused]
  rfl

theorem allCuts_zip_guarded (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    PartialSpineLimits.allCuts (Observations.zipStream (Stream'.corec' c s)
      (observations (guarded d) t)) =
      fun n => Ideal.principal (openPrefix ((unfold c s n).zip (unfold d t n))) := by
  rw [zip_observations_guarded, PartialSpineLimits.allCuts_guarded]
  funext n
  rw [unfold_zip]

theorem allCuts_zip_paused (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    PartialSpineLimits.allCuts (Observations.zipStream (Stream'.corec' c s)
      (observations (paused d) (false, t))) =
      fun n => Ideal.principal (openPrefix ((unfold c s n).zip (unfold d t n))) := by
  rw [zip_observations_paused, PartialSpineLimits.allCuts_paused]
  funext n
  rw [unfold_zip]

theorem paired_second_guarded (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    Observations.map (Prod.snd : A × B → B) (observations (guarded (zipCoalgebra c d)) (s, t)) =
      observations (guarded d) t := by
  rw [← zip_observations_guarded c d s t]
  exact Observations.map_snd_zipStream.{w, w} (Stream'.corec' c s) (observations (guarded d) t)

theorem paired_second_paused (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    Observations.map (Prod.snd : A × B → B)
        (observations (paused (zipCoalgebra c d)) (false, (s, t))) =
      observations (paused d) (false, t) := by
  rw [← zip_observations_paused c d s t]
  exact Observations.map_snd_zipStream.{w, w} (Stream'.corec' c s)
    (observations (paused d) (false, t))

end Producers

/-- The existing counter supplies the total index stream, with no second executor. -/
theorem count_corec (n : Nat) : Stream'.corec' PartialSpineProgress.count n = fun k => n + k := by
  funext k
  induction k generalizing n with
  | zero => exact congrFun (Stream'.corec'_eq PartialSpineProgress.count n) 0
  | succ k ih =>
    calc
      Stream'.corec' PartialSpineProgress.count n (k + 1) =
          Stream'.corec' PartialSpineProgress.count (n + 1) k :=
        congrFun (Stream'.corec'_eq PartialSpineProgress.count n) (k + 1)
      _ = (n + 1) + k := ih (n + 1)
      _ = n + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem label_count_guarded (n s : Nat) :
    Observations.labelFrom n (observations (guarded PartialSpineProgress.count) s) =
      observations (guarded (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
        (n, s) := by
  change Observations.zipStream (fun k => n + k) _ = _
  rw [← count_corec, zip_observations_guarded]

theorem label_count_paused (n s : Nat) :
    Observations.labelFrom n (observations (paused PartialSpineProgress.count) (false, s)) =
      observations (paused (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
        (false, (n, s)) := by
  change Observations.zipStream (fun k => n + k) _ = _
  rw [← count_corec, zip_observations_paused]

/-- These exact counts concern the paired atomic transition, not two schedulers. -/
theorem paired_deliveries :
    Delivers (guarded (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
        (10, 4) [(10, 4), (11, 5), (12, 6)] (13, 7) 3 ∧
      Delivers (paused (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
        (false, (10, 4)) [(10, 4), (11, 5), (12, 6)] (false, (13, 7)) 6 := by
  simpa [unfold, advance, zipCoalgebra, PartialSpineProgress.count] using
    guarded_paused_progress
      (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count) (10, 4) 3

theorem labelled_first (p : Nat × Nat → Prop) :
    PartialSpineLimits.first p
        (Observations.labelFrom 10 (observations (guarded PartialSpineProgress.count) 4)) =
        p (10, 4) ∧
      PartialSpineLimits.first p
        (Observations.labelFrom 10 (observations (paused PartialSpineProgress.count) (false, 4))) =
        p (10, 4) := by
  rw [label_count_guarded, label_count_paused,
    PartialSpineLimits.first_guarded, PartialSpineLimits.first_paused]
  exact ⟨rfl, rfl⟩

theorem labelled_prefixes :
    PartialSpineLimits.allCuts
        (Observations.labelFrom 10 (observations (guarded PartialSpineProgress.count) 4)) 0 = ⊥ ∧
      PartialSpineLimits.allCuts
        (Observations.labelFrom 10 (observations (guarded PartialSpineProgress.count) 4)) 3 =
        Ideal.principal (openPrefix [(10, 4), (11, 5), (12, 6)]) ∧
      PartialSpineLimits.allCuts
        (Observations.labelFrom 10 (observations (paused PartialSpineProgress.count) (false, 4))) 3 =
        Ideal.principal (openPrefix [(10, 4), (11, 5), (12, 6)]) := by
  rw [label_count_guarded, label_count_paused,
    PartialSpineLimits.allCuts_guarded, PartialSpineLimits.allCuts_paused]
  exact ⟨rfl, rfl, rfl⟩

theorem paired_values_recovered :
    Observations.map Prod.snd
        (observations (guarded (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
          (10, 4)) = observations (guarded PartialSpineProgress.count) 4 ∧
      Observations.map Prod.snd
        (observations (paused (zipCoalgebra PartialSpineProgress.count PartialSpineProgress.count))
          (false, (10, 4))) = observations (paused PartialSpineProgress.count) (false, 4) :=
  ⟨paired_second_guarded _ _ _ _, paired_second_paused _ _ _ _⟩

end PartialSpineZip

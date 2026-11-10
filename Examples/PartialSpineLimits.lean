import SquareKit.PartialSpine.Limits
import Examples.PartialSpineProgress

/-!
# Directed limits consumed through actual producer observations

Constructor-budget truncation and a first-output predicate consume both guarded
and paused realizations. Their equal ideals retain the separate exact transition
counts. A single function-valued extension supplies every truncation together.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineLimits

open Order SquareKit PartialSpine Progress Progress.SpineObservations
open scoped SquareKit.DirectedLimits

universe u v
variable {α S : Type u}

private theorem cutInterpreter_monotone (n : Nat) :
    Monotone (fun s : PartialSpine α => Ideal.principal (cut n s)) :=
  IdealCompletion.principal_monotone.comp (cut_monotone n)

/-- Extend the finite constructor budget through the shared ideal interpreter. -/
def truncate (n : Nat) (I : Observations α) : Observations α :=
  IdealCompletion.extend (fun s => Ideal.principal (cut n s)) I

theorem truncate_principal (n : Nat) (s : PartialSpine α) :
    truncate n (Ideal.principal s) = Ideal.principal (cut n s) :=
  IdealCompletion.extend_principal (cutInterpreter_monotone n) s

theorem truncate_stream (n : Nat) (σ : Stream' α) :
    truncate n (stream σ) = Ideal.principal (openPrefix (σ.take n)) := by
  apply le_antisymm
  · apply IdealCompletion.extend_le (cutInterpreter_monotone n)
    intro s hs
    obtain ⟨m, hs⟩ := hs
    apply IdealCompletion.principal_monotone
    calc
      cut n s ≤ cut n (openPrefix (σ.take m)) := cut_monotone n hs
      _ = openPrefix (σ.take (min m n)) := by rw [cut_openPrefix, Stream'.take_take]
      _ ≤ openPrefix (σ.take n) := streamPrefix_mono σ (Nat.min_le_right m n)
  · have known := IdealCompletion.le_extend (cutInterpreter_monotone n) (stream σ)
      (stream_observes_prefix σ n)
    simpa only [truncate, cut_openPrefix, Stream'.take_take, Nat.min_self] using known

theorem guarded_limit (c : Coalgebra S α) (s : S) :
    observations (guarded c) s =
      sSup (Set.range fun n => Ideal.principal (openPrefix (unfold c s n))) := by
  rw [observations_guarded, Observations.stream_eq_sSup_prefixes]
  simp_rw [← unfold_eq_take_corec]

theorem paused_limit (c : Coalgebra S α) (s : S) :
    observations (paused c) (false, s) =
      sSup (Set.range fun n => Ideal.principal (openPrefix (unfold c s n))) := by
  rw [← guarded_paused_observations]
  exact guarded_limit c s

theorem truncate_guarded (n : Nat) (c : Coalgebra S α) (s : S) :
    truncate n (observations (guarded c) s) = Ideal.principal (openPrefix (unfold c s n)) := by
  rw [observations_guarded, truncate_stream, ← unfold_eq_take_corec]

theorem truncate_paused (n : Nat) (c : Coalgebra S α) (s : S) :
    truncate n (observations (paused c) (false, s)) = Ideal.principal (openPrefix (unfold c s n)) := by
  rw [observations_paused, truncate_stream, ← unfold_eq_take_corec]

/-- Equal truncations accompany, rather than replace, the original distinct costs. -/
theorem counting_truncations_and_costs (s n : Nat) :
    truncate n (observations (guarded PartialSpineProgress.count) s) =
        Ideal.principal (openPrefix (unfold PartialSpineProgress.count s n)) ∧
      truncate n (observations (paused PartialSpineProgress.count) (false, s)) =
        Ideal.principal (openPrefix (unfold PartialSpineProgress.count s n)) ∧
      Delivers (guarded PartialSpineProgress.count) s (unfold PartialSpineProgress.count s n)
        (advance PartialSpineProgress.count s n) n ∧
      Delivers (paused PartialSpineProgress.count) (false, s) (unfold PartialSpineProgress.count s n)
        (false, advance PartialSpineProgress.count s n) (2 * n) :=
  ⟨truncate_guarded n _ s, truncate_paused n _ s, PartialSpineProgress.count_deliveries s n⟩

example : truncate 3 (observations (guarded PartialSpineProgress.count) 4) =
    Ideal.principal (openPrefix [4, 5, 6]) ∧
    truncate 3 (observations (paused PartialSpineProgress.count) (false, 4)) =
      Ideal.principal (openPrefix [4, 5, 6]) ∧
    Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6] 7 3 ∧
    Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6] (false, 7) 6 := by
  simpa [unfold, advance, PartialSpineProgress.count] using counting_truncations_and_costs 4 3

example (s : Nat) (q : PartialSpine Nat) :
    sSup (Set.range fun n => Ideal.principal (openPrefix (unfold PartialSpineProgress.count s n))) ≠
      Ideal.principal q := by
  rw [← guarded_limit, observations_guarded]
  exact stream_ne_principal _ q

-- Independent view checks retain the budget needed to observe the final nil.
example : cut 0 (.nil : PartialSpine α) = .bottom := by
  apply view_injective
  rw [view_cut]
  rfl

example : cut 1 (.nil : PartialSpine α) = .nil := by
  apply view_injective
  rw [view_cut]
  rfl

example (a : α) : cut 1 (ofList [a]) = .cons a .bottom := by
  apply view_injective
  rw [view_cut, view_ofList]
  rfl

example (a : α) : cut 2 (ofList [a]) = ofList [a] := by
  apply view_injective
  rw [view_cut, view_ofList]
  rfl

example (a : α) : ScottContinuous (Observations.cons a) ∧ Observations.cons a ⊥ ≠ ⊥ :=
  ⟨Observations.cons_continuous a, Observations.cons_not_strict a⟩

example : sSup (∅ : Set (Observations α)) = ⊥ := Observations.sSup_empty

/-- A continuous tail-ignoring step observes the first output, even with an unknown end. -/
def first (p : α → Prop) (I : Observations α) : Prop :=
  Observations.foldr (fun a _ => p a) False I

theorem first_cons (p : α → Prop) (a : α) (I : Observations α) :
    first p (Observations.cons a I) = p a :=
  Observations.foldr_cons _ False (fun a => (ScottContinuous.const (p a)).monotone)
    a (ScottContinuous.const (p a)) I

theorem first_stream (p : α → Prop) (σ : Stream' α) : first p (stream σ) = p (σ 0) := by
  rw [Observations.stream_cons, first_cons]

theorem first_guarded (p : α → Prop) (c : Coalgebra S α) (s : S) :
    first p (observations (guarded c) s) = p (c s).1 := by
  rw [observations_guarded, first_stream, Stream'.corec'_eq]
  rfl

theorem first_paused (p : α → Prop) (c : Coalgebra S α) (s : S) :
    first p (observations (paused c) (false, s)) = p (c s).1 := by
  rw [← guarded_paused_observations]
  exact first_guarded p c s

theorem first_once (p : α → Prop) (a : α) :
    first p (observations PartialSpineProgress.once (some a)) = p a := by
  rw [PartialSpineProgress.once_observations, ← Observations.cons_principal, first_cons]

theorem first_silent (p : α → Prop) (next : S → S) (s : S) :
    first p (observations (fun x => .inr (next x) : Producer S α) s) = False := by
  rw [observations_silent]
  exact Observations.foldr_bottom _ False (fun a => (ScottContinuous.const (p a)).monotone)

example (p : Nat → Prop) :
    first p (observations (guarded PartialSpineProgress.count) 4) = p 4 ∧
    first p (observations (paused PartialSpineProgress.count) (false, 4)) = p 4 :=
  ⟨first_guarded p _ 4, first_paused p _ 4⟩

example (a : α) :
    Observations.foldr (fun (_ : α) P => P) True (Ideal.principal .nil) = True ∧
      Observations.foldr (fun (_ : α) P => P) True
        (observations PartialSpineProgress.once (some a)) = False := by
  constructor
  · exact Observations.foldr_nil _ True (fun _ => monotone_id)
  · rw [PartialSpineProgress.once_observations]
    exact Observations.foldr_principal (fun (_ : α) (P : Prop) => P) True
      (fun _ => monotone_id) (.cons a .bottom)

theorem and_scottContinuous (Q : Prop) : ScottContinuous (fun P : Prop => P ∧ Q) := by
  intro S _ _ P lub
  constructor
  · rintro _ ⟨R, hR, rfl⟩ ⟨hr, hq⟩
    exact ⟨lub.1 hR hr, hq⟩
  · intro U upper ⟨hp, hq⟩
    exact lub.2 (fun R hR hr => upper ⟨R, hR, rfl⟩ ⟨hr, hq⟩) hp

/-- The fusion client retains the transformed seed before any propositional simplification. -/
theorem first_fusion (p : α → Prop) (Q : Prop) (I : Observations α) :
    (first p I ∧ Q) = Observations.foldr (fun a _ => p a ∧ Q) (False ∧ Q) I := by
  exact Observations.foldr_fusion _ _ False
    (fun a => (ScottContinuous.const (p a)).monotone)
    (fun a => (ScottContinuous.const (p a ∧ Q)).monotone)
    (fun P => P ∧ Q) (and_scottContinuous Q) (by simp) (fun _ _ => rfl) I

theorem first_combined_guarded (p : α → Prop) (Q : Prop) (c : Coalgebra S α) (s : S) :
    Observations.foldr (fun a _ => p a ∧ Q) (False ∧ Q) (observations (guarded c) s) =
      (p (c s).1 ∧ Q) := by
  rw [← first_fusion, first_guarded]

theorem first_combined_paused (p : α → Prop) (Q : Prop) (c : Coalgebra S α) (s : S) :
    Observations.foldr (fun a _ => p a ∧ Q) (False ∧ Q) (observations (paused c) (false, s)) =
      (p (c s).1 ∧ Q) := by
  rw [← first_fusion, first_paused]

private def truthStep (_ : Unit) (_ : Prop) : Prop := True
private def truthObserver (_ : Prop) : Prop := True

/-- Continuity and commutation do not replace strictness at the bottom ideal. -/
theorem nonstrict_counterexample :
    ScottContinuous truthObserver ∧
    (∀ a P, truthObserver (truthStep a P) = truthStep a (truthObserver P)) ∧
    truthObserver False ≠ False ∧
    truthObserver (Observations.foldr truthStep False (⊥ : Observations Unit)) ≠
      Observations.foldr truthStep (truthObserver False) (⊥ : Observations Unit) := by
  refine ⟨ScottContinuous.const True, fun _ _ => rfl, ?_, ?_⟩
  · intro same
    exact Eq.mp same True.intro
  · rw [Observations.foldr_bottom truthStep (truthObserver False)
      (fun _ => (ScottContinuous.const True).monotone)]
    change True ≠ False
    intro same
    exact Eq.mp same True.intro

theorem nonstrict_total_finite_fusion (xs : List Unit) :
    truthObserver (Observations.foldr truthStep False (Ideal.principal (ofList xs))) =
      Observations.foldr truthStep (truthObserver False) (Ideal.principal (ofList xs)) := by
  rw [Observations.foldr_principal truthStep False (fun _ => (ScottContinuous.const True).monotone),
    Observations.foldr_principal truthStep (truthObserver False)
      (fun _ => (ScottContinuous.const True).monotone)]
  exact PartialSpine.foldr_fusion_ofList False False truthStep truthStep truthObserver False
    nonstrict_counterexample.2.1 xs

/-- One full function-space result contains every finite constructor-budget observation. -/
def allCuts (I : Observations α) : Nat → Observations α :=
  IdealCompletion.extend (fun s n => Ideal.principal (cut n s)) I

private theorem allCutsInterpreter_monotone :
    Monotone (fun s : PartialSpine α => fun n => Ideal.principal (cut n s)) := by
  intro s t h n
  exact cutInterpreter_monotone n h

/-- This function-valued least-upper-bound law consumes the full Pi CPO instance. -/
theorem allCuts_isLUB (I : Observations α) :
    IsLUB ((fun s : PartialSpine α => fun n => Ideal.principal (cut n s)) '' (I : Set _))
      (allCuts I) :=
  IdealCompletion.extend_isLUB allCutsInterpreter_monotone I

theorem allCuts_continuous : ScottContinuous (allCuts (α := α)) :=
  IdealCompletion.extend_scottContinuous allCutsInterpreter_monotone

theorem allCuts_apply (I : Observations α) (n : Nat) : allCuts I n = truncate n I :=
  IdealCompletion.extend_apply (fun s n => Ideal.principal (cut n s)) I n

theorem allCuts_stream (σ : Stream' α) :
    allCuts (stream σ) = fun n => Ideal.principal (openPrefix (σ.take n)) := by
  funext n
  rw [allCuts_apply, truncate_stream]

theorem allCuts_guarded (c : Coalgebra S α) (s : S) :
    allCuts (observations (guarded c) s) = fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  funext n
  rw [allCuts_apply, truncate_guarded]

theorem allCuts_paused (c : Coalgebra S α) (s : S) :
    allCuts (observations (paused c) (false, s)) = fun n => Ideal.principal (openPrefix (unfold c s n)) := by
  funext n
  rw [allCuts_apply, truncate_paused]

example : allCuts (observations (guarded PartialSpineProgress.count) 4) 0 = ⊥ ∧
    allCuts (observations (guarded PartialSpineProgress.count) 4) 3 =
      Ideal.principal (openPrefix [4, 5, 6]) := by
  rw [allCuts_guarded]
  constructor <;> rfl

example : allCuts (observations (paused PartialSpineProgress.count) (false, 4)) 0 = ⊥ ∧
    allCuts (observations (paused PartialSpineProgress.count) (false, 4)) 3 =
      Ideal.principal (openPrefix [4, 5, 6]) := by
  rw [allCuts_paused]
  constructor <;> rfl

-- The scoped CPO and existing complete-lattice routes share the same supremum data.
example {ι : Type u} {X : ι → Type v} [∀ i, CompletePartialOrder (X i)] :
    (DirectedLimits.piCompletePartialOrder (X := X)).toSupSet =
      (Pi.supSet : SupSet (∀ i, X i)) := rfl

example {ι : Type u} {X : ι → Type v} [∀ i, CompleteLattice (X i)] :
    (DirectedLimits.piCompletePartialOrder (X := X)).toSupSet =
      (CompleteLattice.toCompletePartialOrder (α := ∀ i, X i)).toSupSet := rfl

end PartialSpineLimits

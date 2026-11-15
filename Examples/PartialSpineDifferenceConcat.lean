import SquareKit.PartialSpine.DifferenceConcat
import Examples.PartialSpineLimits

/-!
# Function accumulation compared through producer observations

An outer coalgebra repeatedly emits the observation ideal of the existing
counting producer. Guarded and paused realizations share independent stream
semantics. Right-fold concat exposes the inner first value and finite cuts;
the function accumulator demands a completed outer end and yields bottom.
Outer and inner delivery counts remain separate operational witnesses.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PartialSpineDifferenceConcat

open Order SquareKit PartialSpine Progress Progress.SpineObservations PartialSpineLimits
open scoped SquareKit.DirectedLimits

universe u
variable {α : Type u}

/-- Keep the starting count as state and repeatedly emit that producer's whole ideal. -/
def repeatCounting : Coalgebra Nat (Observations Nat) :=
  fun s => (observations (guarded PartialSpineProgress.count) s, s)

/-- The actual guarded producer is connected through its independent corec stream. -/
theorem guarded_disagrees (s : Nat) :
    Observations.concatD (observations (guarded repeatCounting) s) = ⊥ ∧
      Observations.concat (observations (guarded repeatCounting) s) =
        observations (guarded PartialSpineProgress.count) s ∧
      Observations.concatD (observations (guarded repeatCounting) s) ≠
        Observations.concat (observations (guarded repeatCounting) s) := by
  have left : Observations.concatD (observations (guarded repeatCounting) s) = ⊥ := by
    rw [observations_guarded, Observations.concatD_stream]
  have right : Observations.concat (observations (guarded repeatCounting) s) =
      observations (guarded PartialSpineProgress.count) s := by
    rw [observations_guarded, Observations.stream_cons]
    change Observations.concat (Observations.cons
      (observations (guarded PartialSpineProgress.count) s) _) =
        observations (guarded PartialSpineProgress.count) s
    simpa only [observations_guarded] using
      Observations.concat_infinite_first (Stream'.corec' PartialSpineProgress.count s)
        (stream (fun n => Stream'.corec' repeatCounting s (n + 1)))
  refine ⟨left, right, ?_⟩
  rw [left, right, observations_guarded]
  exact (stream_ne_principal _ .bottom).symm

/-- Pauses preserve the observed ideal while retaining their own delivery costs. -/
theorem paused_disagrees (s : Nat) :
    Observations.concatD (observations (paused repeatCounting) (false, s)) = ⊥ ∧
      Observations.concat (observations (paused repeatCounting) (false, s)) =
        observations (guarded PartialSpineProgress.count) s ∧
      Observations.concatD (observations (paused repeatCounting) (false, s)) ≠
        Observations.concat (observations (paused repeatCounting) (false, s)) := by
  rw [← guarded_paused_observations repeatCounting s]
  exact guarded_disagrees s

theorem guarded_first (p : Nat → Prop) (s : Nat) :
    first p (Observations.concat (observations (guarded repeatCounting) s)) = p s ∧
      first p (Observations.concatD (observations (guarded repeatCounting) s)) = False := by
  rw [(guarded_disagrees s).2.1, (guarded_disagrees s).1]
  exact ⟨first_guarded p PartialSpineProgress.count s,
    Observations.foldr_bottom _ False (fun a => (ScottContinuous.const (p a)).monotone)⟩

theorem paused_first (p : Nat → Prop) (s : Nat) :
    first p (Observations.concat (observations (paused repeatCounting) (false, s))) = p s ∧
      first p (Observations.concatD (observations (paused repeatCounting) (false, s))) = False := by
  rw [← guarded_paused_observations repeatCounting s]
  exact guarded_first p s

theorem guarded_allCuts (s : Nat) :
    allCuts (Observations.concat (observations (guarded repeatCounting) s)) =
        (fun n => Ideal.principal (openPrefix (unfold PartialSpineProgress.count s n))) ∧
      allCuts (Observations.concatD (observations (guarded repeatCounting) s)) =
        (fun _ => ⊥) := by
  rw [(guarded_disagrees s).2.1, (guarded_disagrees s).1]
  constructor
  · exact allCuts_guarded PartialSpineProgress.count s
  · funext n
    rw [allCuts_apply]
    change truncate n (Ideal.principal (.bottom : PartialSpine Nat)) = ⊥
    rw [truncate_principal]
    cases n <;> rfl

theorem paused_allCuts (s : Nat) :
    allCuts (Observations.concat (observations (paused repeatCounting) (false, s))) =
        (fun n => Ideal.principal (openPrefix (unfold PartialSpineProgress.count s n))) ∧
      allCuts (Observations.concatD (observations (paused repeatCounting) (false, s))) =
        (fun _ => ⊥) := by
  rw [← guarded_paused_observations repeatCounting s]
  exact guarded_allCuts s

/-- Both realizations expose the expected inner prefix only through right-fold concat. -/
theorem counting_cuts :
    allCuts (Observations.concat (observations (guarded repeatCounting) 4)) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      allCuts (Observations.concat (observations (paused repeatCounting) (false, 4))) 3 =
        Ideal.principal (openPrefix [4, 5, 6]) ∧
      allCuts (Observations.concatD (observations (guarded repeatCounting) 4)) 3 = ⊥ ∧
      allCuts (Observations.concatD (observations (paused repeatCounting) (false, 4))) 3 = ⊥ := by
  rw [(guarded_allCuts 4).1, (paused_allCuts 4).1,
    (guarded_allCuts 4).2, (paused_allCuts 4).2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Delivering two inner ideals takes two guarded transitions or four paused transitions. -/
theorem outer_deliveries (s : Nat) :
    let inner := observations (guarded PartialSpineProgress.count) s
    Delivers (guarded repeatCounting) s [inner, inner] s 2 ∧
      Delivers (paused repeatCounting) (false, s) [inner, inner] (false, s) 4 := by
  simpa [unfold, advance, repeatCounting] using guarded_paused_progress repeatCounting s 2

/-- These are the separate counting producer's costs, without a nested scheduling claim. -/
theorem inner_deliveries :
    Delivers (guarded PartialSpineProgress.count) 4 [4, 5, 6] 7 3 ∧
      Delivers (paused PartialSpineProgress.count) (false, 4) [4, 5, 6] (false, 7) 6 := by
  simpa [unfold, advance, PartialSpineProgress.count] using
    PartialSpineProgress.count_deliveries 4 3

/-- Distinct labels fix both composition order and the independent final tail. -/
theorem composition_order :
    ([Ideal.principal (ofList [1]), Ideal.principal (ofList [2, 3])] :
      List (Observations Nat)).foldl
        (fun k xs ys => k (Observations.append xs ys))
        (Observations.append (Ideal.principal (ofList [0])))
        (Ideal.principal (ofList [9])) = Ideal.principal (ofList [0, 1, 2, 3, 9]) := by
  rw [Observations.difference_foldl_apply]
  simp only [List.foldr_cons, List.foldr_nil, Observations.append_ofList]
  rfl

/-- A completed outer end suffices even with an infinite first inner value and arbitrary later value. -/
theorem finite_outer_infinite_inner (σ : Stream' α) (later : Observations α) :
    Observations.concatD (Ideal.principal (ofList [stream σ, later])) = stream σ := by
  rw [Observations.concatD_ofList]
  change Observations.concat (Ideal.principal (.cons (stream σ) (ofList [later]))) = _
  rw [← Observations.cons_principal, Observations.concat_infinite_first]

/-- The full function accumulator is bottom on an infinite outer input, for any tail. -/
theorem infinite_fold_at_tail (σ : Stream' (Observations α))
    (h : Observations α → Observations α) (tail : Observations α) :
    Observations.foldl (fun k xs ys => k (Observations.append xs ys)) h (stream σ) tail = ⊥ := by
  rw [Observations.difference_foldl_stream]
  rfl

theorem empty_and_unknown :
    Observations.concatD (Ideal.principal (.nil : PartialSpine (Observations α))) =
        Ideal.principal .nil ∧
      Observations.concatD (⊥ : Observations (Observations α)) = ⊥ ∧
      (Ideal.principal (.nil : PartialSpine α) : Observations α) ≠ ⊥ := by
  refine ⟨Observations.concatD_nil, Observations.concatD_bottom, ?_⟩
  intro same
  have impossible := principal_injective same
  cases impossible

/-- A completed finite outer list can still have bottom result because of its inner labels. -/
theorem bottom_first_inner (later : Observations α) :
    Observations.concatD (Ideal.principal (ofList [⊥, later])) = ⊥ := by
  rw [Observations.concatD_ofList]
  change Observations.concat (Ideal.principal (.cons ⊥ (ofList [later]))) = _
  rw [← Observations.cons_principal, Observations.concat_cons, Observations.append_bottom]

end PartialSpineDifferenceConcat

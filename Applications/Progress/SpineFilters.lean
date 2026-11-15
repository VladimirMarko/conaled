import Applications.Progress.SpineObservations
import SquareKit.PartialSpine.Filter

/-!
# Total filtering producers and partial-spine semantics

A delivery accounts for exactly its consumed input prefix. Conversely, an
underlying finite prefix needs only an at-most-length delivery: trailing
rejections need not be consumed, and an empty output can use zero transitions.
The two finite directions identify the existing observation ideal by a lub.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace Progress

open Order SquareKit PartialSpine

universe u
variable {S A : Type u}

/-- One emitted filtered value accounts for its whole finite route through rejected inputs. -/
theorem filter_evaluation_prefix (p : A → Bool) (c : Coalgebra S A)
    {s : S} {result : A × S} {k : Nat} (h : Evaluates (filterProducer p c) s result k) :
    (unfold c s k).filter p = [result.1] ∧ advance c s k = result.2 := by
  induction h with
  | @done s result step =>
    cases hp : p (c s).1 with
    | false => simp [filterProducer, hp] at step
    | true =>
      have same : c s = result := by simpa [filterProducer, hp] using step
      constructor
      · simpa [unfold, hp] using congrArg (fun pair : A × S => [pair.1]) same
      · simpa [advance] using congrArg Prod.snd same
  | @next s t _ _ step _ ih =>
    cases hp : p (c s).1 with
    | false =>
      have state : (c s).2 = t := by simpa [filterProducer, hp] using step
      simpa [unfold, advance, hp, state] using ih
    | true => simp [filterProducer, hp] at step

/-- An exact-cost filtered delivery is the filtered underlying prefix of that cost. -/
theorem filter_delivery_prefix (p : A → Bool) (c : Coalgebra S A)
    {s t : S} {xs : List A} {k : Nat} (h : Delivers (filterProducer p c) s xs t k) :
    (unfold c s k).filter p = xs ∧ advance c s k = t := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons first _ ih =>
    obtain ⟨prefix_eq, state⟩ := filter_evaluation_prefix p c first
    constructor
    · simp only [unfold_add, List.filter_append, state, prefix_eq, ih.1, List.cons_append, List.nil_append]
    · simpa only [advance_add, state] using ih.2

/-- Trailing rejected inputs need not be consumed; the final state belongs to the actual k. -/
theorem filter_unfold_delivery (p : A → Bool) (c : Coalgebra S A) (s : S) (n : Nat) :
    ∃ k ≤ n, Delivers (filterProducer p c) s ((unfold c s n).filter p) (advance c s k) k := by
  induction n generalizing s with
  | zero => exact ⟨0, le_rfl, .nil s⟩
  | succ n ih =>
    obtain ⟨k, bound, delivery⟩ := ih (c s).2
    cases hp : p (c s).1 with
    | false =>
      cases outputs : (unfold c (c s).2 n).filter p with
      | nil =>
        refine ⟨0, Nat.zero_le _, ?_⟩
        simpa [unfold, advance, hp, outputs] using
          (Delivers.nil s : Delivers (filterProducer p c) s [] s 0)
      | cons a xs =>
        rw [outputs] at delivery
        refine ⟨k + 1, Nat.succ_le_succ bound, ?_⟩
        have silent : filterProducer p c s = .inr (c s).2 := by simp [filterProducer, hp]
        simpa [unfold, advance, hp, outputs] using delivery.prepend_silent silent
    | true =>
      refine ⟨k + 1, Nat.succ_le_succ bound, ?_⟩
      have first : Evaluates (filterProducer p c) s ((c s).1, (c s).2) 1 :=
        .done (by simp [filterProducer, hp])
      simpa [unfold, advance, hp, Nat.add_comm] using Delivers.cons first delivery

namespace SpineObservations

/-- The operational ideal is the lub of all ordinary filtered open input prefixes. -/
theorem filtered_prefixes_isLUB (p : A → Bool) (c : Coalgebra S A) (s : S) :
    IsLUB (Set.range fun n => Ideal.principal (openPrefix ((unfold c s n).filter p)))
      (observations (filterProducer p c) s) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    apply Ideal.principal_le_iff.mpr
    obtain ⟨k, _, delivery⟩ := filter_unfold_delivery p c s n
    exact (openPrefix_mem_iff _ _ _).mpr ⟨advance c s k, k, delivery⟩
  · intro I upper q observed
    obtain ⟨xs, t, k, delivery, prefix_le⟩ := observed
    apply upper ⟨k, rfl⟩
    change q ≤ openPrefix ((unfold c s k).filter p)
    rw [(filter_delivery_prefix p c delivery).1]
    exact prefix_le

/-- The existing total filtering producer realizes the semantic total-predicate filter. -/
theorem observations_filterProducer (p : A → Bool) (c : Coalgebra S A) (s : S) :
    observations (filterProducer p c) s =
      Observations.filter (fun a => some (p a)) (observations (guarded c) s) := by
  rw [observations_guarded]
  have semantic := Observations.filter_stream_prefixes_isLUB p (Stream'.corec' c s)
  simp_rw [← unfold_eq_take_corec] at semantic
  exact (filtered_prefixes_isLUB p c s).unique semantic

/-- Semantic outer filtering of an actual filtered producer keeps the inner-first conjunction. -/
theorem filter_observations_fusion (outer inner : A → Bool) (c : Coalgebra S A) (s : S) :
    Observations.filter (fun a => some (outer a)) (observations (filterProducer inner c) s) =
      observations (filterProducer (fun a => inner a && outer a) c) s := by
  rw [observations_filterProducer, Observations.filter_fusion_total, observations_filterProducer]

end SpineObservations
end Progress

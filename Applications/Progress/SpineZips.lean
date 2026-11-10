import Applications.Progress.SpineObservations
import SquareKit.PartialSpine.Zip

/-!
# Semantic zip realized by the existing paired coalgebra

The first total stream is supplied by a coalgebra's standard corecursion.
Existing finite unfolding and observation adequacy identify both actual paired
realizations. These equalities retain observations; delivery judgments retain
their separate atomic transition counts. The Progress API has one universe.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace Progress.SpineObservations

open SquareKit PartialSpine

universe u
variable {S T A B : Type u}

private theorem take_zip (σ : Stream' A) (τ : Stream' B) (n : Nat) :
    (σ.take n).zip (τ.take n) = (Stream'.zip Prod.mk σ τ).take n := by
  induction n generalizing σ τ with
  | zero => rfl
  | succ n ih =>
    change (σ 0, τ 0) :: (σ.tail.take n).zip (τ.tail.take n) =
      (σ 0, τ 0) :: (Stream'.zip Prod.mk σ.tail τ.tail).take n
    exact congrArg (List.cons (σ 0, τ 0)) (ih σ.tail τ.tail)

/-- The existing finite paired unfolding determines the standard zipped stream. -/
theorem corec_zip (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    Stream'.corec' (zipCoalgebra c d) (s, t) =
      Stream'.zip Prod.mk (Stream'.corec' c s) (Stream'.corec' d t) := by
  apply Stream'.take_theorem
  intro n
  rw [← unfold_eq_take_corec, unfold_zip, unfold_eq_take_corec, unfold_eq_take_corec]
  exact take_zip _ _ n

theorem zip_observations_guarded (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    Observations.zipStream (Stream'.corec' c s) (observations (guarded d) t) =
      observations (guarded (zipCoalgebra c d)) (s, t) := by
  rw [observations_guarded, observations_guarded, Observations.zipStream_stream, corec_zip]

theorem zip_observations_paused (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) :
    Observations.zipStream (Stream'.corec' c s) (observations (paused d) (false, t)) =
      observations (paused (zipCoalgebra c d)) (false, (s, t)) := by
  rw [observations_paused, observations_paused, Observations.zipStream_stream, corec_zip]

end Progress.SpineObservations

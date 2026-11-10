import Applications.Progress.SpineObservations
import SquareKit.PartialSpine.Map

/-!
# Semantic map realized by mapped producers

Finite coalgebra map and the standard stream prefix bridge identify the mapped
stream. Observation adequacy then connects both guarded and paused realizations
to semantic map. These equalities forget time; the existing delivery judgments
remain the owners of operational transition counts.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace Progress.SpineObservations

open SquareKit PartialSpine

universe u
variable {S A B : Type u}

/-- The existing finite unfolding law determines the standard mapped corec stream. -/
theorem corec_map (f : A → B) (c : Coalgebra S A) (s : S) :
    Stream'.corec' (mapCoalgebra f c) s = Stream'.map f (Stream'.corec' c s) := by
  apply Stream'.take_theorem
  intro n
  rw [← unfold_eq_take_corec, unfold_map, unfold_eq_take_corec, Stream'.map_take]

theorem map_observations_guarded (f : A → B) (c : Coalgebra S A) (s : S) :
    Observations.map f (observations (guarded c) s) =
      observations (guarded (mapCoalgebra f c)) s := by
  rw [observations_guarded, observations_guarded, Observations.map_stream, corec_map]

theorem map_observations_paused (f : A → B) (c : Coalgebra S A) (s : S) :
    Observations.map f (observations (paused c) (false, s)) =
      observations (paused (mapCoalgebra f c)) (false, s) := by
  rw [observations_paused, observations_paused, Observations.map_stream, corec_map]

end Progress.SpineObservations

import Applications.Progress.SpineObservations
import SquareKit.PartialSpine.LeftFold

/-!
# Completed-end demand at the producer boundary

The current producer interface emits labels or silent transitions, with no
completed-end event. Its observation ideal therefore cannot provide a result
to the strict semantic left fold, even when arbitrary output prefixes exist.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace Progress.SpineObservations

open SquareKit PartialSpine

universe u v
variable {S A : Type u} {B : Type v} [CompletePartialOrder B]

/-- Every producer observation lacks the completed end required by source foldl. -/
theorem foldl_observations (step : Producer S A) (f : B → A → B) (e : B) (s : S) :
    Observations.foldl f e (observations step s) = ⊥ :=
  Observations.foldl_eq_bottom_of_no_total f e (observations step s)
    (fun q observed => not_total_of_mem step s q observed)

end Progress.SpineObservations

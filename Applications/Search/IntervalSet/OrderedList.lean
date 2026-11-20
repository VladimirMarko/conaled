import Applications.Search.IntervalSet.Contract
import Applications.Search.OrderedList.Basic

/-!
# A finite executable interval-set reference

The existential overlap observation holds for every list. Strictness is needed
only for the existing complete-key set updates. This realization requires no
bottom endpoint and supplies no logarithmic operation-cost claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalSet
universe u v
variable {α : Type u} {κ : Type v} [LE α] [DecidableLE α]

def orderedListSearch (iv : κ → IntervalKey α) (xs : List κ)
    (query : IntervalKey α) : Bool :=
  xs.any (fun key => decide ((iv key).overlap query))

theorem orderedListSearch_correct (iv : κ → IntervalKey α) (xs : List κ)
    (query : IntervalKey α) :
    orderedListSearch iv xs query = true ↔
      hasOverlap (iv '' {key | key ∈ xs}) query := by
  rw [hasOverlap_image_iff]
  simp [orderedListSearch, List.any_eq_true]

theorem orderedListLaws [LinearOrder κ] (iv : κ → IntervalKey α) :
    Laws OrderedList.ops (orderedListSearch iv) iv
      (fun xs key => key ∈ xs) OrderedList.Strict where
  toDeleteLaws := OrderedList.laws
  overlap xs _ query := orderedListSearch_correct iv xs query

end Search.IntervalSet

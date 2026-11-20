import Applications.Search.AbstractSet.Deletion
import Applications.Search.IntervalSet

/-! An interval-set capability extends the shared complete-key set contract
by one geometric observation. Keys, endpoints and representations have
independent universes; projecting contents need not preserve key identity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalSet
universe u v w
variable {α : Type u} {κ : Type v} {S : Type w} [LE α]

structure Laws (ops : AbstractSet.DeleteOps κ S)
    (overlapSearch : S → IntervalKey α → Bool) (iv : κ → IntervalKey α)
    (observe : S → Set κ) (Valid : S → Prop) : Prop
    extends AbstractSet.DeleteLaws ops observe Valid where
  overlap : ∀ s, Valid s → ∀ query,
    overlapSearch s query = true ↔ hasOverlap (iv '' observe s) query

/-- Compose the new observation with the existing mixed-update semantics. -/
theorem Laws.search_execute {ops : AbstractSet.DeleteOps κ S}
    {overlapSearch : S → IntervalKey α → Bool} {iv : κ → IntervalKey α}
    {observe : S → Set κ} {Valid : S → Prop}
    (laws : Laws ops overlapSearch iv observe Valid)
    (updates : List (AbstractSet.Update κ)) {s : S} (valid : Valid s)
    (query : IntervalKey α) :
    overlapSearch (AbstractSet.execute ops updates s) query = true ↔
      hasOverlap (iv '' (updates.foldl AbstractSet.meaningStep (observe s))) query := by
  rw [laws.overlap _ (laws.toDeleteLaws.execute_valid updates valid) query,
    laws.toDeleteLaws.execute_observe updates valid]
  rfl

end Search.IntervalSet

import SquareKit.Internal.Cubical.CocycleFamily

/-! Global cochain reconstruction commutes with actual context substitution. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

theorem cocycleSection_reindex {Γ Δ : Context.{0}} (z : Cocycle2 Γ.Elementsᵒᵖ) (σ : Δ ⟶ Γ) :
    (cocycleSection z).reindex σ = cocycleSection (z.pullback σ.mapElements.op) := by
  apply Term.ext
  intro x
  change z.pullback (elementRestriction (σ.mapElements.obj x)) =
    (z.pullback σ.mapElements.op).pullback (elementRestriction x)
  rw [Cocycle2.pullback_comp,elementRestriction_substitution]

end SquareKit.Cubical.CategoryCocycles

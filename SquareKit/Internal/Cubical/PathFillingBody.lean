import SquareKit.Internal.Cubical.PathFillingBox

/-! The filled body retains the endpoints needed to abstract a dependent path. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

section
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
  {a₀ : Term (reindex B (endpointSub Γ false))}
  {a₁ : Term (reindex B (endpointSub Γ true))}
  (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
  (b : OpenBox (reindex (path B a₀ a₁) p) φ)
  (t : Term (reindex B (pathFillingContext p)))
  (ht : (pathFillingBox p φ b).Fills t)

include ht
theorem pathFillingBody_zero :
    (t.reindex (swapIntervals Δ)).reindex (endpointSub (total (interval Δ)) false) = a₀.reindex p := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨δ,i⟩⟩
  let y := Δ.elementsMk I δ
  let z := (total (interval (total (interval Δ)))).elementsMk I
    ⟨⟨δ,(endpoint Δ false).val y⟩,i⟩
  have hp := pathBoundaryFace_endpoint φ false y
  have h := ht.2 z hp
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  have hz : (intervalFace (total (interval Δ)) false).full ((swapIntervals Δ).mapElements.obj z) :=
    (Cofibration.full_endpoint (generic (interval (total (interval Δ)))) false _).mpr rfl
  exact eq_of_heq ((heq_of_eq h).trans (s.pathBoundary_zero ((swapIntervals Δ).mapElements.obj z) hp hz))

theorem pathFillingBody_one :
    (t.reindex (swapIntervals Δ)).reindex (endpointSub (total (interval Δ)) true) = a₁.reindex p := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨δ,i⟩⟩
  let y := Δ.elementsMk I δ
  let z := (total (interval (total (interval Δ)))).elementsMk I
    ⟨⟨δ,(endpoint Δ true).val y⟩,i⟩
  have hp := pathBoundaryFace_endpoint φ true y
  have h := ht.2 z hp
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  have hz : (intervalFace (total (interval Δ)) true).full ((swapIntervals Δ).mapElements.obj z) :=
    (Cofibration.full_endpoint (generic (interval (total (interval Δ)))) true _).mpr rfl
  exact eq_of_heq ((heq_of_eq h).trans (s.pathBoundary_one ((swapIntervals Δ).mapElements.obj z) hp hz))

def pathFillingBody_path : Term (path (reindex B (liftSub (interval Γ) p)) (a₀.reindex p) (a₁.reindex p)) :=
  pathLam (t.reindex (swapIntervals Δ)) (pathFillingBody_zero p φ b t ht) (pathFillingBody_one p φ b t ht)

end
end SquareKit.Cubical.Presheaf

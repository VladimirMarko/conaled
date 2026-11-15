import SquareKit.Internal.PathTransport.TwoGroupoidPath

/-! Checked discriminators for the first #322 construction checkpoint.
These concern the total path family and do not claim a dependent interpretation.+-/
namespace Examples.TwoGroupoidPath
open SquareKit.Internal.PathTransport.TwoGroupoidPath

/-- The oriented boundary 3 = -2 + m forces m = 5. -/
theorem comparison_three_neg_two : (comparison 3 (-2)).base = 5 := by
  have h := (comparison 3 (-2)).base_eq
  simp only [Arrow] at h
  omega

/-- The actual coherent transformation retains base component one. -/
theorem contraction_one :
    ((coherentContraction.naturality
      (show Quiver.Hom point point from (1 : ℤ))).hom :
      Cell (1 + 0) (0 + 0)).base = 1 := coherentContraction_base 1

/-- Erasing that comparison loses data required by the total-space boundary. -/
theorem base_erasure_rejected : ¬ ∃ p : Cell 1 0, p.base = 0 := by
  rintro ⟨p, hp⟩
  have h := p.base_eq
  simp only [Arrow] at h
  omega

/-- Allowing an arbitrary contraction component still cannot repair strictness. -/
theorem strict_component_rejected (c : ℤ) : ¬ ∀ a : ℤ, c = a + c :=
  fun h => no_strict_contraction ⟨c, h⟩

end Examples.TwoGroupoidPath

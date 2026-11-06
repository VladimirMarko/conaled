import SquareKit.Internal.Cubical.CompositionFilling
import Examples.CubicalDiscreteFilling

/-! Reconstruct whole filling from endpoint composition in a dependent finite
family. Even with an empty tube, the added zero face retains the selected cap. -/
namespace Examples.CubicalCompositionFilling
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev fiber := discreteFamily index (fun n => Fin (n+1))
abbrev original := discreteFilling index (fun n => Fin (n+1))
abbrev composition := original.toComposition
noncomputable abbrev reconstructed := composition.toFilling
abbrev reconstructedLawful :=
  Composition.toFilling_lawful (Filling.toComposition_lawful (discreteFilling_lawful index (fun n => Fin (n+1))))
abbrev emptyBox := OpenBox.empty (reindex fiber (projection (interval naturals))) finiteLast
noncomputable abbrev filled := reconstructed.fill (projection (interval naturals))
  (Cofibration.bot naturals) emptyBox

theorem empty_tube_retains_cap : filled = finiteLast.reindex (projection (interval naturals)) := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨γ,r⟩⟩
  let y := naturals.elementsMk I γ
  have h := discrete_partial_interval (q := index) (S := fun n => Fin (n+1))
    (φ := Cofibration.top naturals) (PartialSection.ofTerm _ filled)
    y rfl r ((endpoint naturals false).val y)
  exact h.trans (congrArg (fun t => t.val y)
    (reconstructedLawful.fills (projection (interval naturals)) _ emptyBox).1)

theorem two_substitutions :
    ((reconstructed.reindex successor).reindex twice).fill
      (projection (interval naturals))
      (((Cofibration.bot naturals).reindex successor).reindex twice)
      ((emptyBox.reindex successor).reindex twice) =
      (filled.reindex (liftSub (interval naturals) successor)).reindex
        (liftSub (interval naturals) twice) := by
  exact ((reconstructedLawful.reindex successor).uniform
    (projection (interval naturals)) _ (emptyBox.reindex successor) twice).trans
      (congrArg (fun t => t.reindex (liftSub (interval naturals) twice))
        (reconstructedLawful.uniform (projection (interval naturals)) _ emptyBox successor))

theorem retained_value :
    (filled.reindex (liftSub (interval naturals) (twice ≫ successor))).val
      ((total (interval naturals)).elementsMk (Opposite.op ⟨1⟩)
        ⟨(2 : ℕ),⟨Cube.identity ⟨1⟩⟩⟩) = (5 : Fin 6) := by
  rw [empty_tube_retains_cap]
  rfl

theorem erasure_rejected :
    ((filled.reindex (liftSub (interval naturals) (twice ≫ successor))).val
      ((total (interval naturals)).elementsMk (Opposite.op ⟨1⟩)
        ⟨(2 : ℕ),⟨Cube.identity ⟨1⟩⟩⟩)).val ≠ 0 := by
  rw [retained_value]
  decide

end Examples.CubicalCompositionFilling

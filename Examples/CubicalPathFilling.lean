import SquareKit.Internal.Cubical.PathFilling
import Examples.CubicalDiscreteFilling

/-! Constructed Path filling retains dependent finite data, including with an
empty original tube; its endpoint faces still constrain the filled body. -/
namespace Examples.CubicalPathFilling
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev fiber := discreteFamily index (fun n => Fin (n+1))
abbrev body := reindex fiber (projection (interval naturals))
abbrev bodyFilling := discreteFilling (index.reindex (projection (interval naturals))) (fun n => Fin (n+1))
abbrev bodyLawful := discreteFilling_lawful (index.reindex (projection (interval naturals))) (fun n => Fin (n+1))

abbrev chosenPath : Term (path body finiteLast finiteLast) :=
  pathLam (finiteLast.reindex (projection (interval naturals))) rfl rfl

noncomputable abbrev paths := pathFilling bodyFilling bodyLawful finiteLast finiteLast
abbrev pathsLawful := pathFilling_lawful bodyFilling bodyLawful finiteLast finiteLast
abbrev emptyBox := OpenBox.empty
  (reindex (path body finiteLast finiteLast) (projection (interval naturals))) chosenPath
noncomputable abbrev filled := paths.hcomp (Cofibration.bot naturals) emptyBox

theorem empty_tube_retains_path : filled = chosenPath := by
  apply pathApp_injective
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨γ,r⟩⟩
  let y := naturals.elementsMk I γ
  have h := discrete_partial_interval (q := index) (S := fun n => Fin (n+1))
    (φ := Cofibration.top naturals)
    (PartialSection.ofTerm _ (pathApp filled)) y rfl r ((endpoint naturals false).val y)
  exact h.trans (congrArg (fun t => t.val y) (pathApp_zero filled))

theorem two_substitutions :
    (((paths.reindex successor).reindex twice).hcomp
      (((Cofibration.bot naturals).reindex successor).reindex twice)
      ((emptyBox.reindex successor).reindex twice)) =
      (filled.reindex successor).reindex twice := by
  exact (Filling.hcomp_reindex (pathsLawful.reindex successor) _ (emptyBox.reindex successor) twice).trans
    (congrArg (fun t => t.reindex twice) (Filling.hcomp_reindex pathsLawful _ emptyBox successor))

theorem retained_value :
    ((pathApp filled).reindex (liftSub (interval naturals) (twice ≫ successor))).val
      ((total (interval naturals)).elementsMk (Opposite.op ⟨1⟩)
        ⟨(2 : ℕ),⟨Cube.identity ⟨1⟩⟩⟩) = (5 : Fin 6) := by
  rw [empty_tube_retains_path]
  rfl

theorem erasure_rejected :
    (((pathApp filled).reindex (liftSub (interval naturals) (twice ≫ successor))).val
      ((total (interval naturals)).elementsMk (Opposite.op ⟨1⟩)
        ⟨(2 : ℕ),⟨Cube.identity ⟨1⟩⟩⟩)).val ≠ 0 := by
  rw [retained_value]
  decide

end Examples.CubicalPathFilling

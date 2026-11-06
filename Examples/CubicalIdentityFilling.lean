import SquareKit.Internal.Cubical.IdentityFilling
import Examples.CubicalIdentity

/-! Identity composition preserves its selected marked tube. The test uses
actual constructed filling, with a dependent finite fiber and a rejected
replacement of its selected identity by reflexivity. -/
namespace Examples.CubicalIdentityFilling
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
  CubicalPresheaf CubicalDiscreteFilling CubicalIdentity

noncomputable abbrev chosenComposition := identityComposition (discreteFilling index (fun n => Fin (n+1)))
  (discreteFilling_lawful index (fun n => Fin (n+1))) finiteLast finiteLast

noncomputable abbrev chosenFilling := identityFilling (discreteFilling index (fun n => Fin (n+1)))
  (discreteFilling_lawful index (fun n => Fin (n+1))) finiteLast finiteLast

def box : OpenBox (reindex (identity fiber finiteLast finiteLast) (projection (interval naturals)))
    (Cofibration.top naturals) where
  tube := PartialSection.ofTerm _ (unmarked.reindex (projection (interval naturals)))
  base := unmarked
  boundary _ _ := rfl

theorem composition_retains_marked_identity :
    chosenComposition.comp (projection (interval naturals)) (Cofibration.top naturals) box = unmarked := by
  apply Term.ext
  intro x
  exact (identityComposition_lawful _ _ _ _).boundary _ _ box x rfl

theorem selected_filling_lawful : chosenFilling.Lawful := identityFilling_lawful _ _ _ _

theorem reflexivity_replacement_rejected :
    chosenComposition.comp (projection (interval naturals)) (Cofibration.top naturals) box ≠
      identityRefl finiteLast := by
  rw [composition_retains_marked_identity]
  exact markers_retained

end Examples.CubicalIdentityFilling

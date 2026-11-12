import SquareKit.Internal.Cubical.LocalFillingBridge
import Examples.CubicalDependentFilling

/-! Representable-local admission recovers the existing nonconstant discrete
family and its selected whole filler under two substitutions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalLocalFilling
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalPresheaf CubicalDiscreteFilling CubicalDependentFilling

abbrev localProvider := filling.toLocal
abbrev localLawful := Filling.toLocal_lawful (discreteFilling_lawful index (fun n => Fin (n+1)))
abbrev recovered := localProvider.toFilling localLawful

theorem selected_filler_recovered : recovered = filling :=
  Filling.toLocal_toFilling filling (discreteFilling_lawful index (fun n => Fin (n+1)))

theorem recovered_lawful : recovered.Lawful := localProvider.toFilling_lawful localLawful

theorem two_substitutions :
    (recovered.comp (liftSub (interval naturals) successor ≫ projection (interval naturals))
      ((Cofibration.top naturals).reindex successor) (generalBox.reindex successor)).reindex twice =
      ((recovered.comp (projection (interval naturals)) (Cofibration.top naturals) generalBox).reindex
        successor).reindex twice := by
  rw [Filling.comp_reindex recovered_lawful]
  rfl

theorem retained_value :
    ((recovered.comp (projection (interval naturals)) (Cofibration.top naturals) generalBox).reindex
      (twice ≫ successor)).val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) := by
  rw [selected_filler_recovered]
  exact computed_at_two

end Examples.CubicalLocalFilling

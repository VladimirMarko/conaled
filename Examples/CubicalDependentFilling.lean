import SquareKit.Internal.Cubical.Filling
import Examples.CubicalDiscreteFilling

/-! The general uniform filling interface recovers the selected dependent data. -/
namespace Examples.CubicalDependentFilling
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev family := discreteFamily index (fun n => Fin (n+1))
abbrev filling := discreteFilling index (fun n => Fin (n+1))

abbrev generalBox : OpenBox (reindex family (projection (interval naturals)))
    (Cofibration.top naturals) where
  tube := box.tube
  base := box.base
  boundary := box.boundary

theorem recovers_filler : filling.fill (projection (interval naturals))
    (Cofibration.top naturals) generalBox = box.fill := rfl

theorem computed_at_two :
    ((filling.comp (projection (interval naturals)) (Cofibration.top naturals) generalBox).reindex
      (twice ≫ successor)).val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) := by
  change box.hcomp.val ((twice ≫ successor).mapElements.obj _) = _
  exact varying_result_at_two

theorem entire_tube (x : (total (interval naturals)).Elements)
    (h : ((Cofibration.top naturals).reindex (projection (interval naturals))).full x) :
    (filling.fill (projection (interval naturals)) (Cofibration.top naturals) generalBox).val x =
      generalBox.tube.val x h :=
  ((discreteFilling_lawful index (fun n => Fin (n+1))).fills _ _ generalBox).2 x h

theorem two_substitutions :
    (filling.comp (liftSub (interval naturals) successor ≫ projection (interval naturals))
      ((Cofibration.top naturals).reindex successor) (generalBox.reindex successor)).reindex twice =
    ((filling.comp (projection (interval naturals)) (Cofibration.top naturals) generalBox).reindex
      successor).reindex twice := by
  rw [Filling.comp_reindex (discreteFilling_lawful index (fun n => Fin (n+1)))]
  rfl

end Examples.CubicalDependentFilling

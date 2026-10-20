import SquareKit.SmoothRealPointCovers
import SquareKit.SmoothOrdinaryCover

/-! Real sections of embedded ordinary opens and their naturality. -/
noncomputable section
open CategoryTheory Opposite
namespace SquareKit.EuclideanOpen
open SmoothAlgebra SmoothPresentationSite SmoothOpenSite

theorem realEvaluation_scalar :
    Hom.comp realEvaluation (DualExtension.realHom : Hom ℝ (Carrier (free 0))) =
      Hom.ident := by
  apply Hom.ext
  intro r
  exact realEvaluation.map_scalar r

def realSectionEquiv (U : Domain) :
    realSections.obj (embedding.obj U) ≃ Points U where
  toFun h := Localization.realPoints U.defining (Hom.comp realEvaluation
    (show Hom (Localization.Principal U.defining) (Carrier (free 0)) from h.unop))
  invFun x := (show code U ⟶ free 0 from Hom.comp DualExtension.realHom
    ((Localization.realPoints U.defining).symm x)).op
  left_inv h := by
    apply Quiver.Hom.unop_inj
    let k : Hom (Localization.Principal U.defining) (Carrier (free 0)) := h.unop
    change Hom.comp DualExtension.realHom
      ((Localization.realPoints U.defining).symm
        (Localization.realPoints U.defining (Hom.comp realEvaluation k))) = k
    rw [Equiv.symm_apply_apply, Hom.comp_assoc, realEvaluation_inverse, Hom.ident_comp]
  right_inv x := by
    change Localization.realPoints U.defining
      (Hom.comp realEvaluation (Hom.comp DualExtension.realHom
        ((Localization.realPoints U.defining).symm x))) = x
    rw [Hom.comp_assoc, realEvaluation_scalar, Hom.ident_comp]
    exact (Localization.realPoints U.defining).apply_symm_apply x

/-- Naturality uses point evaluation only for the full ordinary function
algebras; no detection assertion for arbitrary presentation quotients is used. -/
theorem realSectionEquiv_naturality {U V : Domain} (f : U ⟶ V)
    (a : realSections.obj (embedding.obj U)) :
    realSectionEquiv V (realSections.map (embedding.map f) a) =
      (show Map U V from f) (realSectionEquiv U a) := by
  apply Subtype.ext
  funext i
  let h : Hom (Localization.Principal U.defining) ℝ :=
    Hom.comp realEvaluation (show Hom (Localization.Principal U.defining) (Carrier (free 0)) from a.unop)
  have he (b : Localization.Principal U.defining) :
      h b = (Localization.toOpen U.defining b).val (Localization.realPoints U.defining h) := by
    exact ((Localization.toOpen_realPoint U.defining
      (Localization.realPoints U.defining h) b).trans
        (congrArg (fun k : Hom (Localization.Principal U.defining) ℝ => k b)
          ((Localization.realPoints U.defining).symm_apply_apply h))).symm
  change h (Localization.pullback f (Localization.principalBase V.defining (generator i))) = _
  exact (he _).trans ((Localization.pullback_apply f _ _).trans
    (Localization.toOpen_base V.defining (generator i) _))

end SquareKit.EuclideanOpen

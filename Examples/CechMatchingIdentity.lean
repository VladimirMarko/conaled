import SquareKit.Internal.PathTransport.CechMatchingIdentity
import SquareKit.Internal.PathTransport.CechMatchingConstant
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

noncomputable section
namespace Examples.CechMatchingIdentity
open CategoryTheory SquareKit.Internal.PathTransport
open CechMatching

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev star := SingleObj.star (Multiplicative ℤ)
abbrev loop : star ⟶ star := Multiplicative.ofAdd 1
abbrev C := Grpd.of Loops

def recoverPaths := Identity.restrictionIso (constantFunctor C) (𝟭 Loops) (𝟭 Loops)

/-- Identity matching retains a selected nonidentity loop, despite equal endpoints. -/
theorem selected_loop : (recoverPaths.hom.app star loop).val = loop := rfl

theorem selected_loop_ne_refl : recoverPaths.hom.app star loop ≠
    recoverPaths.hom.app star (𝟙 star) := by
  intro h
  have hh := congrArg Subtype.val h
  change (1 : ℤ) = 0 at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

/-- Recovery is defined for every supplied matching identity, not only a chosen image. -/
theorem arbitrary_local_recovery (p : Identity.Fiber
    ((constantFunctor C).obj star) ((constantFunctor C).obj star)) :
    recoverPaths.hom.app star (recoverPaths.inv.app star p) = p := by
  exact ConcreteCategory.congr_hom (recoverPaths.inv_hom_id_app star) p

/-- The general endpoint action retains conjugation by both selected arrows. -/
example {D : Diagram.{0,0}} {B : Type} [Category B]
    (X Y : B ⥤ Datum D) {b c : B} (f : b ⟶ c)
    (p : Identity.Fiber (X.obj b) (Y.obj b)) :
    ((Identity.family X Y).map f p).val =
      inv (X.map f).localArrow ≫ p.val ≫ (Y.map f).localArrow :=
  Identity.map_localArrow X Y f p

end Examples.CechMatchingIdentity

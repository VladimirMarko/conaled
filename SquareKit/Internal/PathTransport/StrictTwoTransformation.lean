import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-! Strict natural transformations between strict higher functors.
The component is a 1-arrow; its action on fiber 2-cells is retained through
the naturality equation. This is structural family data, not an eliminator.
-/
namespace SquareKit.Internal.PathTransport.StrictTwoTransformation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]

/-- Naturality is strict at arrows and coherent at genuine 2-cells. -/
structure Trans (F G : StrictPseudofunctor A B) where
  app (a : A) : F.obj a ⟶ G.obj a
  naturality {a b : A} (f : a ⟶ b) : F.map f ≫ app b = app a ≫ G.map f
  naturality₂ {a b : A} {f g : a ⟶ b} (α : f ⟶ g) :
    F.map₂ α ▷ app b ≫ eqToHom (naturality g) =
      eqToHom (naturality f) ≫ app a ◁ G.map₂ α

/-- The unit and composition coherence follow from strictness, rather than
being additional requirements on the transformation. -/
def Trans.toStrong {F G : StrictPseudofunctor A B} (η : Trans F G) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor where
  app := η.app
  naturality f := eqToIso (η.naturality f)
  naturality_naturality := η.naturality₂
  naturality_id a := by
    simp [F.mapId_eq_eqToIso, G.mapId_eq_eqToIso, whiskerLeft_eqToHom,
      eqToHom_whiskerRight, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  naturality_comp f g := by
    simp [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso, whiskerLeft_eqToHom,
      eqToHom_whiskerRight, Strict.associator_eqToIso]

end SquareKit.Internal.PathTransport.StrictTwoTransformation

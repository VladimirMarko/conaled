import SquareKit.Internal.PathTransport.CechMatchingComprehensionConstant
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor

/-! Extracting a constant matching fiber recovers coefficient projection of the
supplied total functor, including every arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E : StrictDiagram.{u,u}} {A : FamilyData D}
variable (q : A = data D E) (ha : A.Coherence) (hb : (data D E).Coherence)

def projectionOfEq : StrictMap (A.total ha) E := by
  subst A
  exact projection D E hb

def fixedBaseCoefficientComparison {Z : Type v} [Category.{u} Z]
    (F : Z ⥤ Datum (A.total ha).toDiagram) (d : Datum D.toDiagram)
    (he : F ⋙ (A.projection ha).functor = (Functor.const Z).obj d) :
    fixedBaseFunctor A ha F d he ⋙
        ((familyIsoOfEq q ha hb ≪≫ familyIso D E hb).hom.app d) ≅
      F ⋙ (projectionOfEq q ha hb).functor := by
  subst A
  exact isoWhiskerRight (fixedBaseComparison _ _ _ _ _) (projection D E hb).functor

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant

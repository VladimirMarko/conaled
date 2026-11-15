import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! The inverse comprehension equivalence retains the matching base projection. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory CategoryTheory.Functor GroupoidModel
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)

def inverseProjectionComparison :
    (equivalence A h).inverse ⋙ weaken (family A h) ≅ (A.projection h).functor :=
  isoWhiskerLeft (equivalence A h).inverse (projectionComparison A h).symm ≪≫
    isoWhiskerRight (equivalence A h).counitIso (A.projection h).functor

end SquareKit.Internal.PathTransport.CechMatching.Comprehension

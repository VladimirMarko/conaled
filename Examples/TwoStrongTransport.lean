import SquareKit.Internal.PathTransport.TwoStrongTransport
import SquareKit.Internal.PathTransport.TwoGroupoidPath

/-! Coherent transport accepts the integer contraction, including its nonidentity comparisons. -/
namespace Examples.TwoStrongTransport
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def constant : StrictPseudofunctor TwoGroupoidPath.Total TwoGroupoidPath.Total where
  toPseudofunctor := TwoGroupoidPath.constant
  map_id _ := rfl
  map_comp _ _ := rfl
  mapId_eq_eqToIso _ := by apply Iso.ext; exact Subsingleton.elim _ _
  mapComp_eq_eqToIso _ _ := by apply Iso.ext; exact Subsingleton.elim _ _

abbrev contraction : Pseudofunctor.StrongTrans
    (StrictPseudofunctor.id TwoGroupoidPath.Total).toPseudofunctor constant.toPseudofunctor :=
  TwoGroupoidPath.coherentContraction

/-- Postcomposition preserves the contraction's required, nonzero comparison. -/
theorem comparison_retained (n : ℤ) :
    ((strongPostcomp contraction (StrictPseudofunctor.id TwoGroupoidPath.Total)).naturality
      (show TwoGroupoidPath.point ⟶ TwoGroupoidPath.point from n)).hom.base = n := by
  have h := ((strongPostcomp contraction (StrictPseudofunctor.id TwoGroupoidPath.Total)).naturality
    (show TwoGroupoidPath.point ⟶ TwoGroupoidPath.point from n)).hom.boundary
  change n + 0 = 0 + 0 + _ at h
  omega

/-- The same non-strict homotopy acts on every admitted family and section. -/
def transported (F : TwoFamily.Family TwoGroupoidPath.Total)
    (s : TwoFamily.Section (TwoFamily.reindex (StrictPseudofunctor.id _) F)) :
    TwoFamily.Section (TwoFamily.reindex constant F) :=
  TwoFamily.Section.transport F contraction s

end Examples.TwoStrongTransport

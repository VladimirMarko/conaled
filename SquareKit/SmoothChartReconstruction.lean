import SquareKit.SmoothChartRealMaps
import SquareKit.SmoothChartLocalLifting

/-! Reconstruction of local ordinary coordinates from all sheaf arrows. -/
noncomputable section
open CategoryTheory
namespace SquareKit.EuclideanOpen.Charts
variable {M N : Type} (A : Charts M) (B : Charts N)
    (ha : ∀ x, ∃ i y, A.coordinate i y = x)
    (hb : ∀ x, ∃ i y, B.coordinate i y = x)
    (h : A.realization ⟶ B.realization)

/-- The local lift theorem supplies the coordinate data; they are not extra
hypotheses on the sheaf arrow. -/
def reconstructLocalMap : LocalMap A B (A.realMap B ha hb h) where
  Cover i := Points (A.domain i)
  defining i x := (B.localLift _ (A.chart i ≫ h) x).defining
  covers i x := ⟨x, (B.localLift _ (A.chart i ≫ h) x).atPoint⟩
  index i x := (B.localLift _ (A.chart i ≫ h) x).index
  coordinate i x := (B.localLift _ (A.chart i ≫ h) x).coordinate
  agreement i x z :=
    A.realMap_factor B ha hb h i (B.localLift _ (A.chart i ≫ h) x).index _
      (subInclusion _ _) (B.localLift _ (A.chart i ≫ h) x).coordinate
      (B.localLift _ (A.chart i ≫ h) x).factorization z

/-- Descent of reconstructed coordinates recovers the original arrow at all
stages, including infinitesimal stages. -/
theorem reconstruct_realize : (A.reconstructLocalMap B ha hb h).realize = h := by
  let l := A.reconstructLocalMap B ha hb h
  apply A.hom_ext
  intro i
  rw [LocalMap.chart_realize]
  apply cover_jointly_epic (A.domain i) (l.defining i) (l.covers i) B.realization
  intro x
  exact (l.section_restrict i x).trans (B.localLift _ (A.chart i ≫ h) x).factorization.symm

end SquareKit.EuclideanOpen.Charts

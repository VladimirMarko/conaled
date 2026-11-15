import SquareKit.SmoothQuotientCoverMatching
import SquareKit.SmoothQuotientGeneratedRelativeDiagram
import SquareKit.Internal.PathTransport.CechMatchingMapComposition
import SquareKit.Internal.PathTransport.CechMatchingComprehensionDiagram
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Actual original-cover restrictions supply the independent relative matching diagram. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

def relativeFamilyData (f : Y ⟶ X) :
    CechMatching.Comprehension.FamilyData (strictDiagram a hΓ f) where
  localFamily := interpretedFamily a hΓ hB Y
  doubleFamily := interpretedFamily a hΓ hB (SheafCoverCech.double f)
  tripleFamily := interpretedFamily a hΓ hB (SheafCoverCech.triple f)
  first := familyRestriction a hΓ hB (SheafCoverCech.first f)
  second := familyRestriction a hΓ hB (SheafCoverCech.second f)
  diagonal := familyRestriction a hΓ hB (SheafCoverCech.diagonal f)
  firstSecond := familyRestriction a hΓ hB (SheafCoverCech.firstSecond f)
  firstThird := familyRestriction a hΓ hB (SheafCoverCech.firstThird f)
  secondThird := familyRestriction a hΓ hB (SheafCoverCech.secondThird f)

/-- Strict coherence comes from actual context restriction, including extensions. -/
theorem relativeFamilyCoherence (f : Y ⟶ X) :
    (relativeFamilyData a hΓ hB f).Coherence where
  diagonalFirst := by
    change totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.first f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.diagonal f)) = _
    rw [← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) f).diagonalFirst
  diagonalSecond := by
    change totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.second f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.diagonal f)) = _
    rw [← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) f).diagonalSecond
  tripleFirst := by
    change totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.first f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.firstSecond f)) =
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.first f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.firstThird f))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) f).tripleFirst
  tripleMiddle := by
    change totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.second f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.firstSecond f)) =
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.first f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.secondThird f))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) f).tripleMiddle
  tripleLast := by
    change totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.second f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.firstThird f)) =
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.second f)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SheafCoverCech.secondThird f))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) f).tripleLast

def relativeToGenerated (f : Y ⟶ X) :
    CechMatching.StrictMap ((relativeFamilyData a hΓ hB f).total
      (relativeFamilyCoherence a hΓ hB f)) (strictDiagram a (.ext hΓ hB) f) where
  localMap := 𝟭 _
  doubleMap := 𝟭 _
  tripleMap := 𝟭 _
  first := restriction_extend a hΓ hB (SheafCoverCech.first f)
  second := restriction_extend a hΓ hB (SheafCoverCech.second f)
  diagonal := restriction_extend a hΓ hB (SheafCoverCech.diagonal f)
  firstSecond := restriction_extend a hΓ hB (SheafCoverCech.firstSecond f)
  firstThird := restriction_extend a hΓ hB (SheafCoverCech.firstThird f)
  secondThird := restriction_extend a hΓ hB (SheafCoverCech.secondThird f)

def generatedToRelative (f : Y ⟶ X) :
    CechMatching.StrictMap (strictDiagram a (.ext hΓ hB) f)
      ((relativeFamilyData a hΓ hB f).total (relativeFamilyCoherence a hΓ hB f)) where
  localMap := 𝟭 _
  doubleMap := 𝟭 _
  tripleMap := 𝟭 _
  first := (restriction_extend a hΓ hB (SheafCoverCech.first f)).symm
  second := (restriction_extend a hΓ hB (SheafCoverCech.second f)).symm
  diagonal := (restriction_extend a hΓ hB (SheafCoverCech.diagonal f)).symm
  firstSecond := (restriction_extend a hΓ hB (SheafCoverCech.firstSecond f)).symm
  firstThird := (restriction_extend a hΓ hB (SheafCoverCech.firstThird f)).symm
  secondThird := (restriction_extend a hΓ hB (SheafCoverCech.secondThird f)).symm

/-- The relative total diagram is the actual generated extended-context diagram. -/
def relativeMatchingEquivalence (f : Y ⟶ X) :
    CechMatching.Datum ((relativeFamilyData a hΓ hB f).total
      (relativeFamilyCoherence a hΓ hB f)).toDiagram ≌ Datum a (.ext hΓ hB) f :=
  (relativeToGenerated a hΓ hB f).equivalence (generatedToRelative a hΓ hB f)
    (CechMatching.StrictMap.ext _ _ rfl rfl rfl)
    (CechMatching.StrictMap.ext _ _ rfl rfl rfl)

end SquareKit.SmoothQuotientCoverMatching

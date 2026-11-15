import SquareKit.SmoothQuotientGeneratedMatching
import SquareKit.Internal.PathTransport.CechMatchingMapComposition
import SquareKit.Internal.PathTransport.CechMatchingComprehensionDiagram
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Actual generated family restrictions supply the relative matching diagram. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

def interpretedFamily (_hB : Typed.TyDeriv.{2} Γ γ B b) (Y : Sheaf topology Type) : context a hΓ Y ⥤ Grpd.{1,1} :=
  b (SmoothQuotientSource.model a Y)

def familyRestriction (f : Y ⟶ X) :
    interpretedFamily a hΓ hB X ⟶ restriction a hΓ f ⋙ interpretedFamily a hΓ hB Y :=
  generatedFamilyMap (SmoothQuotientComparison.signature (a := a) f) hΓ hB

def relativeFamilyData (A : SplitSheaf.Ty X) :
    CechMatching.Comprehension.FamilyData (strictDiagram a hΓ A) where
  localFamily := interpretedFamily a hΓ hB (SplitSheaf.Ext A)
  doubleFamily := interpretedFamily a hΓ hB (SplitSheaf.Cech.double A)
  tripleFamily := interpretedFamily a hΓ hB (SplitSheaf.Cech.triple A)
  first := familyRestriction a hΓ hB (SplitSheaf.Cech.first A)
  second := familyRestriction a hΓ hB (SplitSheaf.Cech.second A)
  diagonal := familyRestriction a hΓ hB (SplitSheaf.Cech.diagonal A)
  firstSecond := familyRestriction a hΓ hB (SplitSheaf.Cech.firstSecond A)
  firstThird := familyRestriction a hΓ hB (SplitSheaf.Cech.firstThird A)
  secondThird := familyRestriction a hΓ hB (SplitSheaf.Cech.secondThird A)

theorem restriction_extend (f : Y ⟶ X) :
    restriction a (.ext hΓ hB) f =
      totalMap (restriction a hΓ f) (familyRestriction a hΓ hB f) :=
  generatedContextMap_extend (SmoothQuotientComparison.signature (a := a) f) hΓ hB

/-- Strict coherence comes from actual context restriction, including extensions. -/
theorem relativeFamilyCoherence (A : SplitSheaf.Ty X) :
    (relativeFamilyData a hΓ hB A).Coherence where
  diagonalFirst := by
    change totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.first A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.diagonal A)) = _
    rw [← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) A).diagonalFirst
  diagonalSecond := by
    change totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.second A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.diagonal A)) = _
    rw [← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) A).diagonalSecond
  tripleFirst := by
    change totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.first A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.firstSecond A)) =
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.first A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.firstThird A))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) A).tripleFirst
  tripleMiddle := by
    change totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.second A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.firstSecond A)) =
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.first A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.secondThird A))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) A).tripleMiddle
  tripleLast := by
    change totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.second A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.firstThird A)) =
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.second A)) ⋙
      totalMap _ (familyRestriction a hΓ hB (SplitSheaf.Cech.secondThird A))
    rw [← restriction_extend, ← restriction_extend, ← restriction_extend]
    exact (strictDiagram a (.ext hΓ hB) A).tripleLast

def relativeToGenerated (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap ((relativeFamilyData a hΓ hB A).total
      (relativeFamilyCoherence a hΓ hB A)) (strictDiagram a (.ext hΓ hB) A) where
  localMap := 𝟭 _
  doubleMap := 𝟭 _
  tripleMap := 𝟭 _
  first := restriction_extend a hΓ hB (SplitSheaf.Cech.first A)
  second := restriction_extend a hΓ hB (SplitSheaf.Cech.second A)
  diagonal := restriction_extend a hΓ hB (SplitSheaf.Cech.diagonal A)
  firstSecond := restriction_extend a hΓ hB (SplitSheaf.Cech.firstSecond A)
  firstThird := restriction_extend a hΓ hB (SplitSheaf.Cech.firstThird A)
  secondThird := restriction_extend a hΓ hB (SplitSheaf.Cech.secondThird A)

def generatedToRelative (A : SplitSheaf.Ty X) :
    CechMatching.StrictMap (strictDiagram a (.ext hΓ hB) A)
      ((relativeFamilyData a hΓ hB A).total (relativeFamilyCoherence a hΓ hB A)) where
  localMap := 𝟭 _
  doubleMap := 𝟭 _
  tripleMap := 𝟭 _
  first := (restriction_extend a hΓ hB (SplitSheaf.Cech.first A)).symm
  second := (restriction_extend a hΓ hB (SplitSheaf.Cech.second A)).symm
  diagonal := (restriction_extend a hΓ hB (SplitSheaf.Cech.diagonal A)).symm
  firstSecond := (restriction_extend a hΓ hB (SplitSheaf.Cech.firstSecond A)).symm
  firstThird := (restriction_extend a hΓ hB (SplitSheaf.Cech.firstThird A)).symm
  secondThird := (restriction_extend a hΓ hB (SplitSheaf.Cech.secondThird A)).symm

/-- The relative total diagram is the actual generated extended-context diagram. -/
def relativeMatchingEquivalence (A : SplitSheaf.Ty X) :
    CechMatching.Datum ((relativeFamilyData a hΓ hB A).total
      (relativeFamilyCoherence a hΓ hB A)).toDiagram ≌ Datum a (.ext hΓ hB) A :=
  (relativeToGenerated a hΓ hB A).equivalence (generatedToRelative a hΓ hB A)
    (CechMatching.StrictMap.ext _ _ rfl rfl rfl)
    (CechMatching.StrictMap.ext _ _ rfl rfl rfl)

end SquareKit.SmoothQuotientGeneratedMatching

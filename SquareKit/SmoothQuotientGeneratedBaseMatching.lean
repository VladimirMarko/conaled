import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.Internal.PathTransport.CechMatchingComprehensionConstant
import SquareKit.Internal.PathTransport.CechMatchingAsSmall
import SquareKit.SheafActionQuotientCechMatching

/-! The actual generated base binder has constant relative matching coefficients,
with the primitive quotient datum and its local arrows retained. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (A : SplitSheaf.Ty X)

abbrev liftedRestriction {Y Z : Sheaf topology Type} (f : Z ⟶ Y) :
    AsSmall.{0} (Object a Y) ⥤ AsSmall.{0} (Object a Z) :=
  AsSmall.down ⋙ SheafActionQuotient.restriction f ⋙ AsSmall.up

theorem liftedRestriction_comp {Y Z W : Sheaf topology Type} (f : Z ⟶ Y) (g : W ⟶ Z) :
    liftedRestriction a f ⋙ liftedRestriction a g = liftedRestriction a (g ≫ f) := by
  change AsSmall.down ⋙ (SheafActionQuotient.restriction f ⋙
    SheafActionQuotient.restriction g) ⋙ AsSmall.up = _
  rw [SheafActionQuotient.restriction_comp]

theorem liftedRestriction_id (Y : Sheaf topology Type) :
    liftedRestriction a (𝟙 Y) = 𝟭 (AsSmall.{0} (Object a Y)) := by
  unfold liftedRestriction
  rw [SheafActionQuotient.restriction_id]
  rfl

def baseDiagram : CechMatching.StrictDiagram.{1,1} where
  localCategory := Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Ext A)))
  doubleCategory := Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Cech.double A)))
  tripleCategory := Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Cech.triple A)))
  first := liftedRestriction a (SplitSheaf.Cech.first A)
  second := liftedRestriction a (SplitSheaf.Cech.second A)
  diagonal := liftedRestriction a (SplitSheaf.Cech.diagonal A)
  firstSecond := liftedRestriction a (SplitSheaf.Cech.firstSecond A)
  firstThird := liftedRestriction a (SplitSheaf.Cech.firstThird A)
  secondThird := liftedRestriction a (SplitSheaf.Cech.secondThird A)
  diagonalFirst := by
    rw [liftedRestriction_comp]
    exact liftedRestriction_id a _
  diagonalSecond := by
    rw [liftedRestriction_comp]
    exact liftedRestriction_id a _
  tripleFirst := by
    rw [liftedRestriction_comp, liftedRestriction_comp]
    rfl
  tripleMiddle := by
    rw [liftedRestriction_comp, liftedRestriction_comp]
    rfl
  tripleLast := by
    rw [liftedRestriction_comp, liftedRestriction_comp]
    rfl

theorem relativeFamilyData_base : relativeFamilyData a hΓ (.base hΓ) A =
    CechMatching.Comprehension.Constant.data (strictDiagram a hΓ A) (baseDiagram a A) := by
  unfold relativeFamilyData familyRestriction
  simp only [generatedFamilyMap_base]
  rfl

theorem baseCoherence : (CechMatching.Comprehension.Constant.data
    (strictDiagram a hΓ A) (baseDiagram a A)).Coherence := by
  rw [← relativeFamilyData_base a hΓ A]
  exact relativeFamilyCoherence a hΓ (.base hΓ) A

/-- Base matching coefficients are independent of the supplied context datum,
including their action on context arrows. -/
def baseFamilyIso : relativeMatchingFamily a hΓ (.base hΓ) A ≅
    (Functor.const (Datum a hΓ A)).obj (Grpd.of (CechMatching.Datum (baseDiagram a A).toDiagram)) := by
  exact CechMatching.Comprehension.Constant.familyIsoOfEq (relativeFamilyData_base a hΓ A)
    (relativeFamilyCoherence a hΓ (.base hΓ) A) (baseCoherence a hΓ A) ≪≫
      CechMatching.Comprehension.Constant.familyIso _ _ _

theorem baseDiagram_eq : (baseDiagram a A).toDiagram =
    CechMatching.UniverseLift.diagram.{0,1,0} (SheafActionQuotient.Cech.matchingDiagram a A) := by
  unfold baseDiagram CechMatching.StrictDiagram.toDiagram
    CechMatching.UniverseLift.diagram SheafActionQuotient.Cech.matchingDiagram
  congr 1

/-- The primitive comparison before the strict-diagram presentation change. -/
def liftedCoefficientIso : Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) ≅
    Grpd.of (CechMatching.Datum (CechMatching.UniverseLift.diagram.{0,1,0}
      (SheafActionQuotient.Cech.matchingDiagram a A))) where
  hom := AsSmall.down ⋙ (SheafActionQuotient.Cech.matchingEquivalence a A).functor ⋙
    CechMatching.UniverseLift.up _
  inv := CechMatching.UniverseLift.down _ ⋙
    (SheafActionQuotient.Cech.matchingEquivalence a A).inverse ⋙ AsSmall.up
  hom_inv_id := rfl
  inv_hom_id := rfl

def baseCoefficientIso : Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) ≅
    Grpd.of (CechMatching.Datum (baseDiagram a A).toDiagram) :=
  liftedCoefficientIso a A ≪≫
    CechMatching.Comprehension.Constant.diagramIsoOfEq (baseDiagram_eq a A).symm

def baseCoefficientEquivalence : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ≌
    CechMatching.Datum (baseDiagram a A).toDiagram :=
  CechMatching.Comprehension.Constant.equivalenceOfGrpdIso (baseCoefficientIso a A)

/-- The base binder's relative family is naturally the primitive matching
category, with its fixed universe lift. -/
def basePrimitiveFamilyIso : relativeMatchingFamily a hΓ (.base hΓ) A ≅
    (Functor.const (Datum a hΓ A)).obj
      (Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A))) :=
  baseFamilyIso a hΓ A ≪≫ (Functor.const _).mapIso (baseCoefficientIso a A).symm

/-- Extending a generated context by a base binder adds an arbitrary primitive
matching datum to its independent relative matching total. -/
def baseComprehensionEquivalence :
    Extend ((Functor.const (Datum a hΓ A)).obj
      (Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)))) ≌
      Datum a (.ext hΓ (.base hΓ)) A :=
  (CechMatching.Comprehension.Constant.totalFamilyEquivalence
    (basePrimitiveFamilyIso a hΓ A)).symm.trans
      (dependentComprehensionEquivalence a hΓ (.base hΓ) A)

/-- Base extension preserves the supplied context datum and every base arrow. -/
def baseComprehensionProjection :
    (baseComprehensionEquivalence a hΓ A).functor ⋙ projection a hΓ (.base hΓ) A ≅
      Grothendieck.forget (((Functor.const (Datum a hΓ A)).obj
        (Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)))) ⋙ Grpd.forgetToCat) :=
  isoWhiskerLeft _ (dependentComprehensionProjection a hΓ (.base hΓ) A)

variable (d : Datum a hΓ A)
variable (x : CechMatching.Comprehension.Fiber (relativeFamilyData a hΓ (.base hΓ) A)
  (relativeFamilyCoherence a hΓ (.base hΓ) A) d)

theorem baseFamilyIso_local : (((baseFamilyIso a hΓ A).hom.app d).obj x).localObject =
    x.localFiber := by
  exact eq_of_heq (CechMatching.Comprehension.Constant.familyIsoOfEq_localFiber
    (relativeFamilyData_base a hΓ A) _ _ d x)

theorem baseFamilyIso_overlap : HEq
    (((baseFamilyIso a hΓ A).hom.app d).obj x).overlap.hom x.overlap.hom.fiber := by
  change HEq (CechMatching.Comprehension.Constant.toDatum _ _ _ _).overlap.hom _
  rw [CechMatching.Comprehension.Constant.toDatum_overlap]
  exact CechMatching.Comprehension.Constant.familyIsoOfEq_overlap
    (relativeFamilyData_base a hΓ A) _ _ d x

theorem baseFamilyIso_localArrow
    {x y : CechMatching.Comprehension.Fiber (relativeFamilyData a hΓ (.base hΓ) A)
      (relativeFamilyCoherence a hΓ (.base hΓ) A) d} (f : x ⟶ y) :
    HEq (((baseFamilyIso a hΓ A).hom.app d).map f).localArrow f.matchingArrow.localArrow.fiber :=
  CechMatching.Comprehension.Constant.familyIsoOfEq_arrow (relativeFamilyData_base a hΓ A) _ _ d f

end SquareKit.SmoothQuotientGeneratedMatching

import SquareKit.SmoothQuotientCechLocalSignature
import SquareKit.SmoothQuotientGeneratedDescentEquivalence
import SquareKit.Internal.PathTransport.AlignedSignatureComparison

/-! The independent Čech source and the global quotient interpretation. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechGlobal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

def baseEquivalence :=
  (SheafActionQuotient.Cech.equivalence (a := a) (A := A)).trans
    (Descent.quotientDescentEquivalence a A)

def fiberComparison : SmoothQuotientDeformations.Cech.family (a := a) (A := A) ≅
    (baseEquivalence a A).functor ⋙ family a X :=
  SmoothQuotientDeformations.Cech.comparison ≪≫
    isoWhiskerLeft SheafActionQuotient.Cech.toDescent
      (CocycleDatum.fiberComparison (a := a) (A := A)).symm

def signature := GroupoidModel.Comparison.alignedUniverseSignature
  (baseEquivalence a A).functor (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
  (family a X) (fiberComparison a A).hom

instance signature_base_equivalence : (signature a A).base.map.IsEquivalence := by
  change (AsSmall.down ⋙ (baseEquivalence a A).functor ⋙ AsSmall.up).IsEquivalence
  exact ((AsSmall.equiv (C := SheafActionQuotient.Cech.Datum (a := a) A)).symm.trans
    ((baseEquivalence a A).trans (AsSmall.equiv (C := Object a X)))).isEquivalence_functor

theorem signature_fiber_bijective : ∀ c, Function.Bijective ((signature a A).fiberMap.app c) := by
  intro c
  let e := (Equiv.ulift : ULift _ ≃ _).trans
    ((CategoryTheory.Iso.toEquiv ((fiberComparison a A).app (ULift.down c))).trans Equiv.ulift.symm)
  exact e.bijective

def contextEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)) ≌
      (show Grpd.{1,1} from γ (SmoothQuotientSource.model a X)) :=
  GroupoidModel.Comparison.generatedContextEquivalence (signature a A)
    (signature_fiber_bijective a A) hΓ

omit [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] in
theorem toDescent_local :
    SheafActionQuotient.Cech.toDescent (a := a) (A := A) ⋙ Descent.localFunctor =
      SheafActionQuotient.Cech.localFunctor := by
  apply CategoryTheory.Functor.ext
  · intro d e f
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  intro d
  rfl


/-- The selected quotient descent comparison recovers the supplied local object. -/
def localComparison : (baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A) ≅
    SheafActionQuotient.Cech.localFunctor :=
  NatIso.ofComponents (fun d => d.toDescent.comparison.toIso) (by
    intro d e f
    have h := Descent.Map.comparison_naturality a A f.toDescent
    change (f.toDescent.arrow.reindex (SplitSheaf.p A)).comp e.toDescent.comparison =
      d.toDescent.comparison.comp f.localArrow
    rw [← SheafActionQuotient.Cech.mapOfDescent_toDescent_localArrow f]
    exact h)

def restrictedFiber : SmoothQuotientDeformations.Cech.family (a := a) (A := A) ⟶
    ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) ⋙
      family a (SplitSheaf.Ext A) :=
  (fiberComparison a A).hom ≫ whiskerLeft (baseEquivalence a A).functor
    (restrictionFamily (SplitSheaf.p A))

/-- Fiber recovery uses the selected local comparison, not equality of objects. -/
theorem localComparison_square : restrictedFiber a A ≫
    whiskerRight (localComparison a A).hom (family a (SplitSheaf.Ext A)) =
      SmoothQuotientCechLocal.localFiber a A := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  exact (CocycleDatum.ofFiber d.toDescent (SmoothQuotientDeformations.Cech.fiberEquiv d x)).recover

/-- Generated recovery retains the selected primitive descent comparison. -/
def contextLocalComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    GroupoidModel.Comparison.generatedContextMap
      (GroupoidModel.Comparison.alignedUniverseSignature
        ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A))
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Ext A)) (restrictedFiber a A)) hΓ ≅
    GroupoidModel.Comparison.generatedContextMap (SmoothQuotientCechLocal.signature a A) hΓ :=
  GroupoidModel.Comparison.alignedContextComparison (localComparison a A) _ _
    (restrictedFiber a A) (SmoothQuotientCechLocal.localFiber a A)
    (localComparison_square a A) hΓ

end SquareKit.SmoothQuotientCechGlobal

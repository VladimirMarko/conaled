import SquareKit.SmoothQuotientCechFibers
import SquareKit.SmoothQuotientGeneratedPrimitiveReindex

/-! Primitive coefficient values retain the local deformation and its overlap equation. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

/-- Forget only universe wrappers, retaining the supplied local object and overlap. -/
def coefficientDatum (d : CechMatching.Datum (baseDiagram a A).toDiagram) :
    SheafActionQuotient.Cech.Datum (a := a) A where
  localObject := AsSmall.down.obj d.localObject
  overlap := AsSmall.down.mapIso d.overlap
  diagonal := by
    have hd := congrArg AsSmall.down.map d.diagonal
    simp only [CechMatching.StrictDiagram.toDiagram, eqToIso.hom, eqToIso.inv,
      eqToHom_app, Functor.map_comp, eqToHom_map] at hd
    simp only [eqToHom_refl, Category.id_comp] at hd
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact congrArg (fun k => k.torsorArrow.iso.hom) hd
  cocycle := by
    have hd := congrArg AsSmall.down.map d.cocycle
    simp only [CechMatching.StrictDiagram.toDiagram, eqToIso.hom,
      eqToHom_app, Functor.map_comp, eqToHom_map] at hd
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hd
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact congrArg (fun k => k.torsorArrow.iso.hom) hd

def coefficientDatumFunctor : CechMatching.Datum (baseDiagram a A).toDiagram ⥤
    SheafActionQuotient.Cech.Datum (a := a) A where
  obj := coefficientDatum a A
  map f := {
    localArrow := AsSmall.down.map f.localArrow
    commutes := by
      have hf := congrArg AsSmall.down.map f.commutes
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      exact congrArg (fun k => k.torsorArrow.iso.hom) hf }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The coefficient matching equation is exactly the existing primitive Čech
fiber equation, with the fixed universe lift made explicit. -/
def coefficientValueEquiv (d : CechMatching.Datum (baseDiagram a A).toDiagram) :
    (primitiveCoefficientValues a A).obj d ≃
      ULift.{1} (SmoothQuotientDeformations.Cech.Fiber (coefficientDatum a A d)) where
  toFun z := ⟨⟨z.val.down, by
    exact congrArg ULift.down z.property⟩⟩
  invFun z := ⟨ULift.up z.down.val, by
    apply ULift.ext
    exact z.down.property⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply ULift.ext; apply Subtype.ext; rfl

@[simp] theorem coefficientValueEquiv_value
    (d : CechMatching.Datum (baseDiagram a A).toDiagram)
    (z : (primitiveCoefficientValues a A).obj d) :
    (coefficientValueEquiv a A d z).down.val = z.val.down := rfl

/-- Coefficient matching agrees naturally with the primitive Čech family,
including transport along every supplied local arrow. -/
def coefficientValueFamilyIso : primitiveCoefficientValues a A ≅
    coefficientDatumFunctor a A ⋙ SmoothQuotientDeformations.Cech.family ⋙ uliftFunctor.{1} :=
  NatIso.ofComponents (fun d => (coefficientValueEquiv a A d).toIso) (by
    intro d e f
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply Subtype.ext
    rfl)

variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

/-- Arbitrary generated primitive matching is the primitive Čech fiber over
its selected term datum; no descended object is supplied. -/
def primitiveCechMatchingEquivalence (d : Datum a hΓ A) :
    (relativeMatchingFamily a hΓ (.fiber hx) A).obj d ≌
      Discrete (ULift.{1} (SmoothQuotientDeformations.Cech.Fiber
        (coefficientDatum a A ((baseTermDiagram a hΓ hx A).mapDatum d)))) :=
  (primitiveCoefficientMatchingEquivalence a hΓ hx A d).trans
    (Discrete.equivalence (coefficientValueEquiv a A ((baseTermDiagram a hΓ hx A).mapDatum d)))

end SquareKit.SmoothQuotientGeneratedMatching

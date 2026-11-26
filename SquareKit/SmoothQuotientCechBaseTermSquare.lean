import SquareKit.SmoothQuotientCechBaseTermEvaluation
import SquareKit.Internal.PathTransport.AlignedBaseTermComparison
import SquareKit.Internal.PathTransport.CechMatchingConeMap

/-! The selected overlap commutes with every generated base term. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
private theorem lifted_id_down {C : Type u} [Groupoid.{v} C] (c : AsSmall.{w} C) :
    ULift.down (𝟙 c) = 𝟙 (ULift.down c) := rfl

private theorem whiskering_square_relabel
    {C D E F : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] [Category.{v} F]
    (s : C ⥤ D) (t : E ⥤ F)
    {I J : D ⥤ F} {I' J' L' R' : C ⥤ E}
    (e : I ≅ J) (e' : I' ≅ J') (hI : L' = I') (hJ : R' = J')
    (hi : s ⋙ I = I' ⋙ t) (hj : s ⋙ J = J' ⋙ t)
    (hl : s ⋙ I = L' ⋙ t) (hr : s ⋙ J = R' ⋙ t)
    (h : isoWhiskerLeft s e ≪≫ eqToIso hj = eqToIso hi ≪≫ isoWhiskerRight e' t) :
    isoWhiskerLeft s e ≪≫ eqToIso hr = eqToIso hl ≪≫
      isoWhiskerRight (eqToIso hI ≪≫ e' ≪≫ (eqToIso hJ).symm) t := by
  cases hI
  cases hJ
  simpa using h

variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

private theorem quotient_id (p : Object a Y) : (𝟙 p : p ⟶ p) = Arrow.ident p := rfl
private theorem quotient_comp {p q r : Object a Y} (f : p ⟶ q) (g : q ⟶ r) :
    f ≫ g = Arrow.comp f g := rfl

def primitiveLocalMap := (signature a A).base.map

def primitiveOverlap : primitiveLocalMap a A ⋙
      (SmoothQuotientGeneratedMatching.baseDiagram a A).first ≅
    primitiveLocalMap a A ⋙ (SmoothQuotientGeneratedMatching.baseDiagram a A).second :=
  alignedBaseIso (overlap a A)
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.double A)) (firstFiber a A) (secondFiber a A)

theorem primitive_coneLaws : CechMatching.ConeLaws
    (D := (SmoothQuotientGeneratedMatching.baseDiagram a A).toDiagram)
    (primitiveLocalMap a A) (primitiveOverlap a A) where
  diagonal := by
    apply Iso.ext
    apply NatTrans.ext
    funext d
    apply ULift.ext
    simp only [SmoothQuotientGeneratedMatching.baseDiagram,
      CechMatching.StrictDiagram.toDiagram, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app, isoWhiskerLeft_inv, eqToIso.hom, eqToIso.inv, NatTrans.id_app,
      eqToHom_refl, ]
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    simpa [primitiveLocalMap, primitiveOverlap, alignedBaseIso, overlap, signature, alignedUniverseSignature, restriction, SheafActionQuotient.Cech.localFunctor, AsSmall.up, AsSmall.down, CategoryTheory.down_comp, lifted_id_down, SheafActionQuotient.instCategoryObject, SheafActionQuotient.instGroupoidObject, quotient_id, quotient_comp] using congrArg (fun k => k.torsorArrow.iso.hom) (AsSmall.down.obj d).diagonal
  cocycle := by
    apply Iso.ext
    apply NatTrans.ext
    funext d
    apply ULift.ext
    simp only [SmoothQuotientGeneratedMatching.baseDiagram,
      CechMatching.StrictDiagram.toDiagram, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app, eqToIso.hom, NatTrans.id_app,
      eqToHom_refl, ]
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    simpa [primitiveLocalMap, primitiveOverlap, alignedBaseIso, overlap, signature, alignedUniverseSignature, restriction, SheafActionQuotient.Cech.localFunctor, AsSmall.up, AsSmall.down, CategoryTheory.down_comp, lifted_id_down, SheafActionQuotient.instCategoryObject, SheafActionQuotient.instGroupoidObject, quotient_id, quotient_comp] using congrArg (fun k => k.torsorArrow.iso.hom) (AsSmall.down.obj d).cocycle

include hx

theorem localMap_comp_restriction_base_term (f : Y ⟶ SplitSheaf.extension A) :
    baseFunctor (ξ (model a A)).down ⋙ (parameterSignature a A f).base.map =
      (localMap a A hΓ ⋙ SmoothQuotientGeneratedMatching.restriction a hΓ f) ⋙
        baseFunctor (ξ (SmoothQuotientSource.model a Y)).down := by
  rw [localMap_restriction]
  exact generatedBaseTerm_commutes (parameterSignature a A f) hΓ hx

theorem generatedOverlap_base_term :
    isoWhiskerLeft (baseFunctor (ξ (model a A)).down)
        (alignedBaseIso (overlap a A)
          (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
          (family a (SplitSheaf.Cech.double A)) (firstFiber a A) (secondFiber a A)) ≪≫
      eqToIso (localMap_comp_restriction_base_term a A hΓ hx (SplitSheaf.Cech.second A)) =
    eqToIso (localMap_comp_restriction_base_term a A hΓ hx (SplitSheaf.Cech.first A)) ≪≫
      isoWhiskerRight (generatedOverlap a A hΓ)
        (baseFunctor (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down) := by
  exact whiskering_square_relabel
    (baseFunctor (ξ (model a A)).down)
    (baseFunctor (ξ (SmoothQuotientSource.model a (SplitSheaf.Cech.double A))).down)
    _ _
    (localMap_restriction a A hΓ (SplitSheaf.Cech.first A))
    (localMap_restriction a A hΓ (SplitSheaf.Cech.second A))
    _ _ _ _
    (alignedContextComparison_base_term (overlap a A)
      (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
      (family a (SplitSheaf.Cech.double A)) (firstFiber a A) (secondFiber a A)
      (overlap_square a A) hΓ hx)

def primitiveCoefficientFunctor :
    AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ⥤
      CechMatching.Datum (SmoothQuotientGeneratedMatching.baseDiagram a A).toDiagram :=
  CechMatching.coneFunctor (primitiveLocalMap a A) (primitiveOverlap a A)
    (primitive_coneLaws a A)

theorem matchingEvaluation_baseTermDiagram :
    matchingEvaluation a A hΓ ⋙
        (SmoothQuotientGeneratedMatching.baseTermDiagram a hΓ hx A).functor =
      baseFunctor (ξ (model a A)).down ⋙ primitiveCoefficientFunctor a A := by
  apply CechMatching.ConeMap.coneFunctor_map
    (SmoothQuotientGeneratedMatching.baseTermDiagram a hΓ hx A)
    (localMap a A hΓ) (primitiveLocalMap a A) (baseFunctor (ξ (model a A)).down)
    (generatedOverlap a A hΓ) (primitiveOverlap a A)
    (generated_coneLaws a A hΓ) (primitive_coneLaws a A)
    (generatedBaseTerm_commutes (signature a A) hΓ hx).symm
  exact CechMatching.ConeMap.transportedOverlap_of_square
    (SmoothQuotientGeneratedMatching.baseTermDiagram a hΓ hx A)
    (localMap a A hΓ) (primitiveLocalMap a A) (baseFunctor (ξ (model a A)).down)
    (generatedOverlap a A hΓ) (primitiveOverlap a A)
    (generatedBaseTerm_commutes (signature a A) hΓ hx).symm
    (localMap_comp_restriction_base_term a A hΓ hx (SplitSheaf.Cech.first A))
    (localMap_comp_restriction_base_term a A hΓ hx (SplitSheaf.Cech.second A))
    (generatedOverlap_base_term a A hΓ hx)

omit hx in
theorem primitiveCoefficientFunctor_recovery :
    primitiveCoefficientFunctor a A ⋙
      SmoothQuotientGeneratedMatching.coefficientDatumFunctor a A = AsSmall.down := by
  rfl

def primitiveCoefficientEquivalence :
    AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ≌
      CechMatching.Datum (SmoothQuotientGeneratedMatching.baseDiagram a A).toDiagram where
  functor := primitiveCoefficientFunctor a A
  inverse := SmoothQuotientGeneratedMatching.coefficientDatumFunctor a A ⋙ AsSmall.up
  unitIso := Iso.refl _
  counitIso := Iso.refl _

theorem evaluatedBaseTerm_eq_source :
    evaluatedBaseTerm a A hΓ hx = sourceBaseTerm a A hx := by
  dsimp only [evaluatedBaseTerm, sourceBaseTerm]
  rw [← Functor.assoc, matchingEvaluation_baseTermDiagram, Functor.assoc,
    primitiveCoefficientFunctor_recovery]

end SquareKit.SmoothQuotientCechLocal

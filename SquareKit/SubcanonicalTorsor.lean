import SquareKit.SubcanonicalSheafStack
import SquareKit.SheafSliceQuotient

/-! Coherent comparison of original-site restriction with independent slice torsors. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SubcanonicalTorsor
open CategoryTheory Opposite
open SubcanonicalSheafStack
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} [J.Subcanonical]
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)} {U V W : C}

/-- The identity comparison in represented contexts is the actual functor identity law. -/
def torsorIdentityIso (P : SheafTorsor.Torsor G (J.yoneda.obj U)) :
    SheafTorsor.reindex P (J.yoneda.map (𝟙 U)) ≅ P :=
  eqToIso (by rw [J.yoneda.map_id]; rfl)

/-- The slice comparison commutes with the identity restriction isomorphisms. -/
theorem torsor_identity_coherence (P : SheafTorsor.Torsor G (J.yoneda.obj U)) :
    (SheafSliceTorsor.forward J U).map (torsorIdentityIso P).hom =
      (SheafSliceTorsor.restrictionComparison J (𝟙 U)).hom.app P ≫
        (SheafSliceTorsor.restrictionId J).hom.app ((SheafSliceTorsor.forward J U).obj P) := by
  apply SheafSliceTorsor.Arrow.ext
  ext X p
  change (eqToHom (congrArg (SheafTorsor.reindex P) (J.yoneda.map_id U))).iso.hom.app
    ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom) p = P.family.family.map _ p
  rw [TorsorExtension.eqToHom_reindex_app P (J.yoneda.map_id U)]
  rfl

/-- Repeated represented pullback and independent slice restriction have the
same comparison, including the canonical associativity transport. -/
theorem torsor_composition_coherence (f : V ⟶ U) (g : W ⟶ V)
    (P : SheafTorsor.Torsor G (J.yoneda.obj U)) :
    (SheafSliceTorsor.forward J W).map (TorsorExtension.compositionIso P f g).hom ≫
      (SheafSliceTorsor.restrictionComparison J g).hom.app (SheafTorsor.reindex P (J.yoneda.map f)) ≫
      (SheafSliceTorsor.restriction J g).map ((SheafSliceTorsor.restrictionComparison J f).hom.app P) =
    (SheafSliceTorsor.restrictionComparison J (g ≫ f)).hom.app P ≫
      (SheafSliceTorsor.restrictionComp J f g).hom.app ((SheafSliceTorsor.forward J U).obj P) := by
  apply SheafSliceTorsor.Arrow.ext
  ext X p
  change (TorsorExtension.compositionIso P f g).hom.iso.hom.app
    ((yoneda.obj W).elementsMk (op X.unop.left) X.unop.hom) p = P.family.family.map _ p
  rw [TorsorExtension.compositionIso_hom_app]
  rfl

variable {a : SheafActionQuotient.Action G M}

omit [J.Subcanonical] in
lemma eqToHom_torsorArrow {X : Sheaf J (Type u)} {P Q : SheafActionQuotient.Object a X}
    (h : P = Q) : (eqToHom h).torsorArrow = eqToHom (congrArg SheafActionQuotient.Object.torsor h) := by
  subst Q
  rfl

def quotientIdentityIso (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    SheafActionQuotient.reindex P (J.yoneda.map (𝟙 U)) ≅ P :=
  eqToIso (by rw [J.yoneda.map_id]; rfl)

def quotientCompositionIso (P : SheafActionQuotient.Object a (J.yoneda.obj U))
    (f : V ⟶ U) (g : W ⟶ V) :
    SheafActionQuotient.reindex P (J.yoneda.map (g ≫ f)) ≅
      SheafActionQuotient.reindex (SheafActionQuotient.reindex P (J.yoneda.map f)) (J.yoneda.map g) :=
  eqToIso (by rw [J.yoneda.map_comp]; rfl)

lemma quotientIdentityIso_torsorArrow (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    (quotientIdentityIso P).hom.torsorArrow = (torsorIdentityIso P.torsor).hom := by
  simp only [quotientIdentityIso, eqToIso.hom, eqToHom_torsorArrow]
  rfl

lemma quotientCompositionIso_torsorArrow (P : SheafActionQuotient.Object a (J.yoneda.obj U))
    (f : V ⟶ U) (g : W ⟶ V) :
    (quotientCompositionIso P f g).hom.torsorArrow =
      (TorsorExtension.compositionIso P.torsor f g).hom := by
  simp only [quotientCompositionIso, eqToIso.hom, eqToHom_torsorArrow]
  rfl

/-- Quotient identity coherence retains the actual equivariant target maps. -/
theorem quotient_identity_coherence (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    (SheafSliceQuotient.forward a U).map (quotientIdentityIso P).hom =
      (SheafSliceQuotient.restrictionComparison a (𝟙 U)).hom.app P ≫
        (SheafSliceQuotient.restrictionId a).hom.app ((SheafSliceQuotient.forward a U).obj P) := by
  apply SheafSliceQuotient.Arrow.ext
  change (SheafSliceTorsor.forward J U).map (quotientIdentityIso P).hom.torsorArrow = _
  rw [quotientIdentityIso_torsorArrow]
  exact torsor_identity_coherence P.torsor

/-- Quotient repeated restriction is compatible with the slice comparison on all arrows. -/
theorem quotient_composition_coherence (f : V ⟶ U) (g : W ⟶ V)
    (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    (SheafSliceQuotient.forward a W).map (quotientCompositionIso P f g).hom ≫
      (SheafSliceQuotient.restrictionComparison a g).hom.app (SheafActionQuotient.reindex P (J.yoneda.map f)) ≫
      (SheafSliceQuotient.restriction a g).map ((SheafSliceQuotient.restrictionComparison a f).hom.app P) =
    (SheafSliceQuotient.restrictionComparison a (g ≫ f)).hom.app P ≫
      (SheafSliceQuotient.restrictionComp a f g).hom.app ((SheafSliceQuotient.forward a U).obj P) := by
  apply SheafSliceQuotient.Arrow.ext
  change (SheafSliceTorsor.forward J W).map (quotientCompositionIso P f g).hom.torsorArrow ≫ _ = _
  rw [quotientCompositionIso_torsorArrow]
  exact torsor_composition_coherence f g P.torsor

end SquareKit.SubcanonicalTorsor

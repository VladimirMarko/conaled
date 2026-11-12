import SquareKit.Internal.Cubical.Univalence
import SquareKit.Internal.Cubical.GlueEquivalence

/-! Elimination from the supplied Glue code, retaining its native map. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Glue
open CategoryTheory
universe u
variable {Γ : Context.{u}} (φ : Cofibration Γ)
  (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
  (t : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
  (e : decode t ⟶ reindex (decode a) (restrictInclusion φ))
  (E : HomotopyEquivalence e)

/-- The supplied-code Glue family retains the native compatible presentation. -/
noncomputable def codeNativeIso :
    decode (code φ a t e E) ≅ family φ (decode a) (decode t) e :=
  eqToIso (LocalFamily.decodeCode_family_eq
    (LocalFamily.normalizedGlue φ (decodedLocalFamily a) (decodedLocalFamily t) e E)) ≪≫
    (Datum.nativeIso (Datum.mk φ (decode a) (decode t) e)).symm

noncomputable def codeUnglue : decode (code φ a t e E) ⟶ decode a :=
  eqToHom (LocalFamily.decodeCode_family_eq
    (LocalFamily.normalizedGlue φ (decodedLocalFamily a) (decodedLocalFamily t) e E)) ≫
    (Datum.smallFamilyIso (Datum.mk φ (decode a) (decode t) e)).hom ≫
    compatibleUnglue φ (decode a) (decode t) e

private theorem cancelIso {Ξ : Context.{u}} {W X Y Z : Family Ξ}
    (h : W ⟶ Y) (i : X ≅ Y) (k : Y ⟶ Z) :
    h ≫ k = (h ≫ i.inv) ≫ i.hom ≫ k := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem codeUnglue_native : codeUnglue φ a t e E =
    (codeNativeIso φ a t e E).hom ≫ unglue φ (decode a) (decode t) e :=
  cancelIso
    (eqToHom (LocalFamily.decodeCode_family_eq
      (LocalFamily.normalizedGlue φ (decodedLocalFamily a) (decodedLocalFamily t) e E)) ≫
      (Datum.smallFamilyIso (Datum.mk φ (decode a) (decode t) e)).hom)
    (familyIso φ (decode a) (decode t) e) (compatibleUnglue φ (decode a) (decode t) e)

/-- Full-face code elimination recovers the original supplied map. -/
theorem codeUnglue_full :
    Functor.whiskerLeft (restrictInclusion φ).mapElements (codeUnglue φ a t e E) =
      eqToHom (congrArg decode (code_full φ a t e E)) ≫ e := by
  ext x z
  let D := Datum.mk φ (decode a) (decode t) e
  let h := LocalFamily.decodeCode_family_eq
    (LocalFamily.normalizedGlue φ (decodedLocalFamily a) (decodedLocalFamily t) e E)
  let w := (eqToHom (congrArg decode (code_full φ a t e E))).app x z
  have hz : HEq ((eqToHom h).app ((restrictInclusion φ).mapElements.obj x) z) w :=
    (family_eqToIso_hom_heq h _ z).trans
      (family_eqToIso_hom_heq (congrArg decode (code_full φ a t e E)) x z).symm
  exact congrArg (fun c => c.ambient) (D.smallFiberEquiv_full x.val.property _ w hz)

/-- Native elimination on the full face is the original supplied map. -/
theorem unglue_full {Ξ : Context.{u}} (ψ : Cofibration Ξ) (A : Family Ξ)
    (T : Family (restrictContext ψ)) (f : T ⟶ reindex A (restrictInclusion ψ)) :
    Functor.whiskerLeft (restrictInclusion ψ).mapElements (unglue ψ A T f) =
      eqToHom (family_full ψ A T f) ≫ f := by
  ext x z
  let w := (eqToHom (family_full ψ A T f)).app x z
  have hz : HEq z w := (family_eqToIso_hom_heq (family_full ψ A T f) x z).symm
  have h := fiberEquiv_full ψ A T f x.val.property z w hz
  exact congrArg (fun c => c.ambient) h

end SquareKit.Cubical.Presheaf.Glue

namespace SquareKit.Cubical.Presheaf.IntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family (total (interval Γ))} {B : Family Γ}

/-- Applying a map into a constant family to a chosen filling gives the actual
comparison path between its endpoint observations. No regularity of constant
transport is assumed. -/
def mapLineComparison (F : Filling A) (hF : F.Lawful)
    (f : A ⟶ reindex B (projection (interval Γ)))
    (a : Term (reindex A (endpointSub Γ false))) :
    Term (homogeneousPath B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements f) a)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements f)
        (Term.map (map F) a))) :=
  pathLam (Term.map f (forward F (𝟙 Γ) a))
    (congrArg (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements f))
      (forward_zero F hF (𝟙 Γ) a))
    (congrArg (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements f))
      (map_section F hF a).symm)


def mapLineComparisonTo {C : Family Γ} (F : Filling A) (hF : F.Lawful)
    (h₀ : reindex A (endpointSub Γ false) = C)
    (h₁ : reindex A (endpointSub Γ true) = B)
    (g : A ⟶ reindex B (projection (interval Γ))) (f : C ⟶ B)
    (g₀ : Functor.whiskerLeft (endpointSub Γ false).mapElements g = eqToHom h₀ ≫ f)
    (g₁ : Functor.whiskerLeft (endpointSub Γ true).mapElements g = eqToHom h₁)
    (x : Term C) :
    Term (homogeneousPath B (Term.map f x) (Term.map (mapTo F C B h₀ h₁) x)) := by
  let z := Term.map (eqToHom h₀.symm) x
  let q := mapLineComparison F hF g z
  refine pathLam (pathApp q) ((pathApp_zero q).trans ?_) ((pathApp_one q).trans ?_)
  · change Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements g) z = Term.map f x
    rw [g₀]
    exact congrArg (Term.map f) (Term.map_iso_roundtrip (eqToIso h₀).symm x)
  · change Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements g)
      (Term.map (map F) z) = _
    rw [g₁]
    rfl

end SquareKit.Cubical.Presheaf.IntervalTransport

namespace SquareKit.Cubical.Presheaf.Univalence
open CategoryTheory
universe u
variable {Γ : Context.{u}} (a b : raisedContext Γ ⟶ smallFamilyCodes.{u})
  (f : decode a ⟶ decode b) (H : HomotopyEquivalence f)

noncomputable def unglueLine : decode (uaCode a b f H) ⟶
    reindex (decode b) (projection (interval Γ)) :=
  Glue.codeUnglue face (ambient b) (CodeSystem.boundary a b)
    (boundaryMap a b f) (boundaryEquivalence a b f H)

private theorem whisker_eqToHom {Ξ Ω : Context.{u}} {A B : Family Ξ}
    (h : A = B) (σ : Ω ⟶ Ξ) :
    Functor.whiskerLeft σ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun X => reindex X σ) h) := by
  cases h
  rfl

private theorem cast_comp {Ξ : Context.{u}} {A B C D : Family Ξ}
    (h : A = B) (k : B = C) (f : C ⟶ D) :
    eqToHom h ≫ eqToHom k ≫ f = eqToHom (h.trans k) ≫ f := by
  cases h
  cases k
  rfl

theorem unglueLine_zero :
    Functor.whiskerLeft (endpointSub Γ false).mapElements (unglueLine a b f H) =
      eqToHom (congrArg decode (uaCode_zero a b f H)) ≫ f := by
  have h := congrArg (Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements)
    (Glue.codeUnglue_full face (ambient b) (CodeSystem.boundary a b)
      (boundaryMap a b f) (boundaryEquivalence a b f H))
  refine h.trans ?_
  change Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements (eqToHom _) ≫
    Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements (boundaryMap a b f) = _
  rw [whisker_eqToHom, boundaryMap_zero]
  exact cast_comp _ _ _

theorem unglueLine_one :
    Functor.whiskerLeft (endpointSub Γ true).mapElements (unglueLine a b f H) =
      eqToHom (congrArg decode (uaCode_one a b f H)) := by
  have h := congrArg (Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements)
    (Glue.codeUnglue_full face (ambient b) (CodeSystem.boundary a b)
      (boundaryMap a b f) (boundaryEquivalence a b f H))
  refine h.trans ?_
  change Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements (eqToHom _) ≫
    Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements (boundaryMap a b f) = _
  rw [whisker_eqToHom, boundaryMap_one]
  exact eqToHom_trans _ _

/-- Transport along the actual decoded ua code line, with its selected filler. -/
noncomputable def transport : decode a ⟶ decode b :=
  IntervalTransport.mapTo (decodedLocalFamily (uaCode a b f H)).toNative.filling
    (decode a) (decode b) (congrArg decode (uaCode_zero a b f H))
    (congrArg decode (uaCode_one a b f H))

/-- The supplied map and the chosen ua transport are connected by an actual
native path in the target family. -/
noncomputable def comparison (x : Term (decode a)) :
    Term (homogeneousPath (decode b) (Term.map f x) (Term.map (transport a b f H) x)) :=
  IntervalTransport.mapLineComparisonTo
    (decodedLocalFamily (uaCode a b f H)).toNative.filling
    (decodedLocalFamily (uaCode a b f H)).toNative.lawful
    (congrArg decode (uaCode_zero a b f H)) (congrArg decode (uaCode_one a b f H))
    (unglueLine a b f H) f (unglueLine_zero a b f H) (unglueLine_one a b f H) x

end SquareKit.Cubical.Presheaf.Univalence

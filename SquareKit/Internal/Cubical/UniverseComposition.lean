import SquareKit.Internal.Cubical.UniverseFilling
import SquareKit.Internal.Cubical.SmallFamilySubstitution

/-! Cap/tube data for universe filling. The backward equivalence is constructed
from the selected filling of the supplied tube code. -/
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.Cubical.Presheaf.IntervalTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
def mapTo (F : Filling A) (B C : Family Γ)
    (h₀ : reindex A (endpointSub Γ false) = B)
    (h₁ : reindex A (endpointSub Γ true) = C) : B ⟶ C :=
  eqToHom h₀.symm ≫ map F ≫ eqToHom h₁

noncomputable def equivalenceTo (F : Filling A) (hF : F.Lawful) (B C : Family Γ)
    (h₀ : reindex A (endpointSub Γ false) = B)
    (h₁ : reindex A (endpointSub Γ true) = C) : HomotopyEquivalence (mapTo F B C h₀ h₁) := by
  subst B
  subst C
  exact equivalence F hF

theorem mapTo_reindex (F : Filling A) (hF : F.Lawful) (B C : Family Γ)
    (h₀ : reindex A (endpointSub Γ false) = B)
    (h₁ : reindex A (endpointSub Γ true) = C) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (mapTo F B C h₀ h₁) =
      mapTo (F.reindex (liftSub (interval Γ) σ)) (reindex B σ) (reindex C σ)
        (congrArg (fun X => reindex X σ) h₀) (congrArg (fun X => reindex X σ) h₁) := by
  subst B
  subst C
  exact (map_reindex F hF σ).symm

theorem equivalenceTo_reindex (F : Filling A) (hF : F.Lawful) (B C : Family Γ)
    (h₀ : reindex A (endpointSub Γ false) = B)
    (h₁ : reindex A (endpointSub Γ true) = C) (σ : Δ ⟶ Γ) :
    HEq ((equivalenceTo F hF B C h₀ h₁).reindex σ)
      (equivalenceTo (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
        (reindex B σ) (reindex C σ)
        (congrArg (fun X => reindex X σ) h₀) (congrArg (fun X => reindex X σ) h₁)) := by
  subst B
  subst C
  exact equivalence_reindex F hF σ
variable {Γ : Context.{u}} {L L' : LawfulFamily (total (interval Γ))}
  {B B' C C' : Family Γ}
  (hL : L = L') (hB : B = B') (hC : C = C')
  (h₀ : reindex L.family (endpointSub Γ false) = B)
  (h₁ : reindex L.family (endpointSub Γ true) = C)
  (h₀' : reindex L'.family (endpointSub Γ false) = B')
  (h₁' : reindex L'.family (endpointSub Γ true) = C')
include hL hB hC in
theorem mapTo_native_congr :
    HEq (mapTo L.filling B C h₀ h₁) (mapTo L'.filling B' C' h₀' h₁') := by
  cases hL
  cases hB
  cases hC
  rfl

include hL hB hC in
theorem equivalenceTo_native_congr :
    HEq (equivalenceTo L.filling L.lawful B C h₀ h₁)
      (equivalenceTo L'.filling L'.lawful B' C' h₀' h₁') := by
  cases hL
  cases hB
  cases hC
  rfl

end SquareKit.Cubical.Presheaf.IntervalTransport

namespace SquareKit.Cubical.Presheaf.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ : Context.{u}} (φ : Cofibration Γ)

abbrev TubeContext := restrictContext (φ.reindex (projection (interval Γ)))

def tubeProjection : TubeContext φ ⟶ restrictContext φ where
  app _ := TypeCat.ofHom (fun x => ⟨x.val.1,x.property⟩)
  naturality _ _ _ := rfl

/-- Scale the tube coordinate while preserving its base face. -/
def tubeScale : total (interval (TubeContext φ)) ⟶ TubeContext φ where
  app _ := TypeCat.ofHom (fun x =>
    ⟨⟨x.1.val.1,ULift.up (Cube.meet x.1.val.2.down x.2.down)⟩,x.1.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (scaleInterval Γ).naturality_apply f ⟨x.1.val,x.2⟩

theorem tubeScale_zero :
    endpointSub (TubeContext φ) false ≫ tubeScale φ = tubeProjection φ ≫ tubeCap φ := by
  ext I x
  apply Subtype.ext
  exact congrArg (fun r => (⟨x.val.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    (Cube.meet_zero x.val.2.down)

theorem tubeScale_one : endpointSub (TubeContext φ) true ≫ tubeScale φ = 𝟙 _ := by
  ext I x
  apply Subtype.ext
  exact congrArg (fun r => (⟨x.val.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    (Cube.meet_one x.val.2.down)

def backwardScale : total (interval (TubeContext φ)) ⟶ TubeContext φ :=
  reverseInterval (TubeContext φ) ≫ tubeScale φ

theorem backwardScale_zero : endpointSub (TubeContext φ) false ≫ backwardScale φ = 𝟙 _ := by
  unfold backwardScale
  rw [← Category.assoc, reverseInterval_endpoint]
  exact tubeScale_one φ

theorem backwardScale_one :
    endpointSub (TubeContext φ) true ≫ backwardScale φ = tubeProjection φ ≫ tubeCap φ := by
  unfold backwardScale
  rw [← Category.assoc, reverseInterval_endpoint]
  exact tubeScale_zero φ

variable {φ} (b : Box Γ φ)

/-- The backward code line contracts each supplied tube fiber to the cap. -/
def backwardCode : raisedContext (total (interval (TubeContext φ))) ⟶ smallFamilyCodes.{u} :=
  raisedSub (backwardScale φ) ≫ b.tube

theorem backwardCode_zero :
    raisedSub (endpointSub (TubeContext φ) false) ≫ b.backwardCode = b.tube :=
  congrArg (fun σ => raisedSub σ ≫ b.tube) (backwardScale_zero φ)

theorem backwardCode_one :
    raisedSub (endpointSub (TubeContext φ) true) ≫ b.backwardCode =
      raisedSub (restrictInclusion (φ.reindex (projection (interval Γ))) ≫ projection (interval Γ)) ≫ b.base :=
  (congrArg (fun σ => raisedSub σ ≫ b.tube) (backwardScale_one φ)).trans
    (congrArg (fun a => raisedSub (tubeProjection φ) ≫ a) b.boundary)

/-- This is the actual chosen native equivalence of the backward code line.
Endpoint identification and overlap coherence remain separate obligations. -/
noncomputable def backwardEquivalence : HomotopyEquivalence
    (IntervalTransport.map (decodedLocalFamily b.backwardCode).toNative.filling) :=
  IntervalTransport.equivalence (decodedLocalFamily b.backwardCode).toNative.filling
    (decodedLocalFamily b.backwardCode).toNative.lawful

/-- Contract the complete cap/tube face, so overlap coherence is built into
one supplied code line rather than a later comparison of chosen equivalences. -/
def faceScale : total (interval (restrictContext (face (φ := φ)))) ⟶
    restrictContext (face (φ := φ)) where
  app I := TypeCat.ofHom (fun x =>
    ⟨⟨x.1.val.1,ULift.up (Cube.meet x.1.val.2.down x.2.down)⟩,by
      apply (Cofibration.full_join _ _ _).mpr
      rcases (Cofibration.full_join _ _ _).mp x.1.property with h | h
      · apply Or.inl
        apply (Cofibration.full_endpoint (generic (interval Γ)) false _).mpr
        have hr := (Cofibration.full_endpoint (generic (interval Γ)) false _).mp h
        change x.1.val.2 = ULift.up (Cube.endpoint I.unop false) at hr
        change ULift.up (Cube.meet x.1.val.2.down x.2.down) =
          ULift.up (Cube.endpoint I.unop false)
        rw [hr]
        exact congrArg ULift.up (Cube.zero_meet x.2.down)
      · exact Or.inr h⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (scaleInterval Γ).naturality_apply f ⟨x.1.val,x.2⟩

def faceProjection : restrictContext (face (φ := φ)) ⟶ Γ :=
  restrictInclusion (face (φ := φ)) ≫ projection (interval Γ)

theorem faceScale_zero :
    endpointSub _ false ≫ faceScale (φ := φ) = faceProjection (φ := φ) ≫ cap := by
  ext I x
  apply Subtype.ext
  exact congrArg (fun r => (⟨x.val.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    (Cube.meet_zero x.val.2.down)

theorem faceScale_one : endpointSub _ true ≫ faceScale (φ := φ) = 𝟙 _ := by
  ext I x
  apply Subtype.ext
  exact congrArg (fun r => (⟨x.val.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    (Cube.meet_one x.val.2.down)

def faceBackwardScale : total (interval (restrictContext (face (φ := φ)))) ⟶
    restrictContext (face (φ := φ)) :=
  reverseInterval _ ≫ faceScale

theorem faceBackwardScale_zero : endpointSub _ false ≫ faceBackwardScale (φ := φ) = 𝟙 _ := by
  unfold faceBackwardScale
  rw [← Category.assoc, reverseInterval_endpoint]
  exact faceScale_one

theorem faceBackwardScale_one :
    endpointSub _ true ≫ faceBackwardScale (φ := φ) = faceProjection (φ := φ) ≫ cap := by
  unfold faceBackwardScale
  rw [← Category.assoc, reverseInterval_endpoint]
  exact faceScale_zero

def faceBackwardCode :
    raisedContext (total (interval (restrictContext (face (φ := φ))))) ⟶ smallFamilyCodes.{u} :=
  raisedSub faceBackwardScale ≫ b.partialCode

theorem faceBackwardCode_zero : raisedSub (endpointSub _ false) ≫ b.faceBackwardCode = b.partialCode := by
  change raisedSub (endpointSub _ false ≫ faceBackwardScale (φ := φ)) ≫ b.partialCode = b.partialCode
  rw [faceBackwardScale_zero]
  rfl

theorem faceBackwardCode_one : raisedSub (endpointSub _ true) ≫ b.faceBackwardCode =
    raisedSub faceProjection ≫ b.base :=
by
  change raisedSub (endpointSub _ true ≫ faceBackwardScale (φ := φ)) ≫ b.partialCode = _
  rw [faceBackwardScale_one]
  exact congrArg (fun a => raisedSub (faceProjection (φ := φ)) ≫ a) b.partial_cap

/-- The complete-face contraction commutes with changes of base context. -/
theorem faceScale_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    faceScale (φ := φ.reindex σ) ≫
      restrictSubstitution face (liftSub (interval Γ) σ) =
    liftSub (interval (restrictContext (face (φ := φ))))
      (restrictSubstitution face (liftSub (interval Γ) σ)) ≫ faceScale := rfl

theorem faceBackwardScale_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    faceBackwardScale (φ := φ.reindex σ) ≫
      restrictSubstitution face (liftSub (interval Γ) σ) =
    liftSub (interval (restrictContext (face (φ := φ))))
      (restrictSubstitution face (liftSub (interval Γ) σ)) ≫ faceBackwardScale := rfl

theorem faceBackwardCode_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    raisedSub (liftSub (interval (restrictContext (face (φ := φ))))
      (restrictSubstitution face (liftSub (interval Γ) σ))) ≫ b.faceBackwardCode =
      (b.reindex σ).faceBackwardCode :=
  congrArg (fun a => raisedSub (faceBackwardScale (φ := φ.reindex σ)) ≫ a)
    (b.partial_reindex σ)

theorem faceBackwardFamily_zero :
    Presheaf.reindex (decode b.faceBackwardCode) (endpointSub _ false) = decode b.partialCode :=
  congrArg decode b.faceBackwardCode_zero

theorem faceBackwardFamily_one :
    Presheaf.reindex (decode b.faceBackwardCode) (endpointSub _ true) =
      Presheaf.reindex (decode b.base) faceProjection :=
  congrArg decode b.faceBackwardCode_one

/-- Endpoint identifications only transport the actual interval map. -/
noncomputable def faceMap : decode b.partialCode ⟶
    Presheaf.reindex (decode (raisedSub (projection (interval Γ)) ≫ b.base)) (restrictInclusion face) :=
  IntervalTransport.mapTo (decodedLocalFamily b.faceBackwardCode).toNative.filling
    _ _ b.faceBackwardFamily_zero b.faceBackwardFamily_one

noncomputable def faceEquivalence : HomotopyEquivalence b.faceMap :=
  IntervalTransport.equivalenceTo (decodedLocalFamily b.faceBackwardCode).toNative.filling
    (decodedLocalFamily b.faceBackwardCode).toNative.lawful
    _ _ b.faceBackwardFamily_zero b.faceBackwardFamily_one

/-- Small-context universe filling is built by Glue from the contracted whole
face. Both cap and tube are recovered as the original supplied codes. -/
noncomputable def fillCode : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  Glue.code face (raisedSub (projection (interval Γ)) ≫ b.base)
    b.partialCode b.faceMap b.faceEquivalence

theorem fillCode_face : raisedSub (restrictInclusion face) ≫ b.fillCode = b.partialCode :=
  Glue.code_full _ _ _ _ _

theorem fillCode_cap : raisedSub (endpointSub Γ false) ≫ b.fillCode = b.base :=
  (congrArg (fun a => raisedSub (cap (φ := φ)) ≫ a) b.fillCode_face).trans b.partial_cap

theorem fillCode_tube :
    raisedSub (restrictInclusion (φ.reindex (projection (interval Γ)))) ≫ b.fillCode = b.tube :=
  (congrArg (fun a => raisedSub
    (includeRight (intervalFace Γ false) (φ.reindex (projection (interval Γ)))) ≫ a)
    b.fillCode_face).trans b.partial_tube

/-- Recover the whole decoded family and its selected filling, not just its carrier. -/
theorem filledLocal_face :
    (decodedLocalFamily b.fillCode).reindex (restrictInclusion face) =
      decodedLocalFamily b.partialCode :=
  (decodedLocalFamily_reindex _ _).symm.trans (congrArg decodedLocalFamily b.fillCode_face)

theorem filledLocal_cap :
    (decodedLocalFamily b.fillCode).reindex (endpointSub Γ false) = decodedLocalFamily b.base :=
  (decodedLocalFamily_reindex _ _).symm.trans (congrArg decodedLocalFamily b.fillCode_cap)

theorem faceBackwardLocal_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (decodedLocalFamily b.faceBackwardCode).reindex
      (liftSub (interval (restrictContext (face (φ := φ))))
        (restrictSubstitution face (liftSub (interval Γ) σ))) =
      decodedLocalFamily (b.reindex σ).faceBackwardCode :=
  (decodedLocalFamily_reindex _ _).symm.trans
    (congrArg decodedLocalFamily (b.faceBackwardCode_reindex σ))

variable {Δ : Context.{u}} (σ : Δ ⟶ Γ)

theorem faceMap_reindex :
    HEq (Functor.whiskerLeft
      (restrictSubstitution face (liftSub (interval Γ) σ)).mapElements b.faceMap)
      (b.reindex σ).faceMap :=
  (heq_of_eq (IntervalTransport.mapTo_reindex
    (decodedLocalFamily b.faceBackwardCode).toNative.filling
    (decodedLocalFamily b.faceBackwardCode).toNative.lawful _ _
    b.faceBackwardFamily_zero b.faceBackwardFamily_one
    (restrictSubstitution face (liftSub (interval Γ) σ)))).trans
      (IntervalTransport.mapTo_native_congr
        ((LocalFamily.toNative_reindex _ _).symm.trans
          (congrArg LocalFamily.toNative (b.faceBackwardLocal_reindex σ)))
        (congrArg decode (b.partial_reindex σ)) rfl _ _ _ _)

theorem faceEquivalence_reindex :
    HEq (b.faceEquivalence.reindex (restrictSubstitution face (liftSub (interval Γ) σ)))
      (b.reindex σ).faceEquivalence := by
  let τ := restrictSubstitution (face (φ := φ)) (liftSub (interval Γ) σ)
  let L := (decodedLocalFamily b.faceBackwardCode).toNative
  let L' := (decodedLocalFamily (b.reindex σ).faceBackwardCode).toNative
  have hL : L.reindex (liftSub (interval (restrictContext (face (φ := φ)))) τ) = L' :=
    (LocalFamily.toNative_reindex _ _).symm.trans
      (congrArg LocalFamily.toNative (b.faceBackwardLocal_reindex σ))
  have hB : Presheaf.reindex (decode b.partialCode) τ = decode (b.reindex σ).partialCode :=
    congrArg decode (b.partial_reindex σ)
  have h := IntervalTransport.equivalenceTo_reindex L.filling L.lawful
    (decode b.partialCode) (Presheaf.reindex (decode b.base) faceProjection)
    b.faceBackwardFamily_zero b.faceBackwardFamily_one τ
  have k := IntervalTransport.equivalenceTo_native_congr hL hB rfl
    (congrArg (fun X => Presheaf.reindex X τ) b.faceBackwardFamily_zero)
    (congrArg (fun X => Presheaf.reindex X τ) b.faceBackwardFamily_one)
    (b.reindex σ).faceBackwardFamily_zero (b.reindex σ).faceBackwardFamily_one
  exact h.trans k
private theorem glueCode_congr {Ξ : Context.{u}} {ψ : Cofibration Ξ}
    (a : raisedContext Ξ ⟶ smallFamilyCodes.{u})
    {t t' : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}}
    (ht : t = t')
    (e : decode t ⟶ Presheaf.reindex (decode a) (restrictInclusion ψ))
    (E : HomotopyEquivalence e)
    (e' : decode t' ⟶ Presheaf.reindex (decode a) (restrictInclusion ψ))
    (E' : HomotopyEquivalence e') (he : HEq e e') (hE : HEq E E') :
    Glue.code ψ a t e E = Glue.code ψ a t' e' E' := by
  cases ht
  cases he
  cases hE
  rfl

theorem fillCode_reindex :
    raisedSub (liftSub (interval Γ) σ) ≫ b.fillCode = (b.reindex σ).fillCode :=
  (Glue.code_substitution face (raisedSub (projection (interval Γ)) ≫ b.base)
    b.partialCode b.faceMap b.faceEquivalence (liftSub (interval Γ) σ)).trans
      (glueCode_congr _ (b.partial_reindex σ) _ _ _ _
        (b.faceMap_reindex σ) (b.faceEquivalence_reindex σ))


end SquareKit.Cubical.Presheaf.CodeSystem.Box

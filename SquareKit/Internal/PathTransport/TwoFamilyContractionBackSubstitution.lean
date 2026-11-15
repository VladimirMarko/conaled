import SquareKit.Internal.PathTransport.TwoFamilySubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ] [IsLocallyGroupoid Δ]
variable (R : StrictPseudofunctor Γ Γ) (R' : StrictPseudofunctor Δ Δ)
variable (σ : StrictPseudofunctor Δ Γ) (hR : R'.comp σ = σ.comp R)
variable (η : Pseudofunctor.StrongTrans R.toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (η' : Pseudofunctor.StrongTrans R'.toPseudofunctor (StrictPseudofunctor.id Δ).toPseudofunctor)
variable [∀x, IsIso (η.app x)] [∀x, IsIso (η'.app x)]
variable (hη : HEq (strongPostcomp η' σ) (strongPrecomp η σ))
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
include hR in
theorem contractionReindexFamily : reindex R' (reindex σ E) = reindex σ (reindex R E) :=
  (reindex_comp E σ R').trans ((congrArg (fun K => reindex K E) hR).trans (reindex_comp E R σ).symm)

include hR hη in
theorem forwardFamilyContraction_reindex :
    HEq (forwardFamilyContraction R' η' (reindex σ E))
      (strongPrecomp (forwardFamilyContraction R η E) σ) := by
  have h1 := forwardFamilyContraction_heq R' η' (reindex σ E)
  have h2 := (strongPostcomp_comp η' σ E).symm
  have h3 := strongPostcomp_heq hR
    ((StrictTwoTransformation.functor_id_comp σ).trans (StrictTwoTransformation.functor_comp_id σ).symm)
    (strongPostcomp η' σ) (strongPrecomp η σ) hη E
  have h4 := strongPostcomp_precomp η σ E
  have h5 := strongPrecomp_heq rfl (StrictTwoTransformation.functor_id_comp E)
    (strongPostcomp η E) (forwardFamilyContraction R η E) (forwardFamilyContraction_heq R η E).symm σ
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

include hR hη in
theorem inverseFamilyContraction_reindex :
    HEq (inverseFamilyContraction R' η' (reindex σ E))
      (strongPrecomp (inverseFamilyContraction R η E) σ) := by
  let α := forwardFamilyContraction R η E
  let β := forwardFamilyContraction R' η' (reindex σ E)
  have h1 := strongInverse_heq
    (iη := fun x => forwardFamilyContraction_isIso R' η' (reindex σ E) x)
    (iθ := fun x => forwardFamilyContraction_isIso R η E (σ.obj x))
    (contractionReindexFamily R R' σ hR E) rfl β (strongPrecomp α σ)
    (forwardFamilyContraction_reindex R R' σ hR η η' hη E)
  have h2 := heq_of_eq (strongInverse_precomp α σ)
  exact h1.trans h2

section CastMap
omit [IsLocallyGroupoid Γ] in
theorem strongMap_codomain_cast {F G G' : Family.{u,v,w,uE,vE,wE} Γ}
    (e : G = G') (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (β : Pseudofunctor.StrongTrans F.toPseudofunctor G'.toPseudofunctor) (h : HEq α β) :
    (StrongMap.toHigher α).comp (familyCast e) = StrongMap.toHigher β := by
  cases e
  cases eq_of_heq h
  exact StrictTwoTransformation.functor_comp_id _
end CastMap

include hR hη in
theorem contractionBack_reindex :
    (contractionBack R' η' (reindex σ E)).comp
      (familySubstitution (reindex R E) σ (contractionReindexFamily R R' σ hR E)) =
        (reindexHigher E σ).comp (contractionBack R η E) := by
  unfold familySubstitution
  rw [← strictFunctor_comp_assoc]
  change ((StrongMap.toHigher (inverseFamilyContraction R' η' (reindex σ E))).comp
    (familyCast (contractionReindexFamily R R' σ hR E))).comp _ = _
  have k := strongMap_codomain_cast (contractionReindexFamily R R' σ hR E)
    (inverseFamilyContraction R' η' (reindex σ E))
    (strongPrecomp (inverseFamilyContraction R η E) σ)
    (inverseFamilyContraction_reindex R R' σ hR η η' hη E)
  exact (congrArg (fun K => K.comp (reindexHigher (reindex R E) σ)) k).trans
    (StrongMap.reindex_square (inverseFamilyContraction R η E) σ)
end SquareKit.Internal.PathTransport.TwoFamily

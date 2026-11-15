import SquareKit.Internal.PathTransport.TwoStrongInverse
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (R : StrictPseudofunctor Γ Γ)
variable (η : Pseudofunctor.StrongTrans R.toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor) [∀ x, IsIso (η.app x)]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)

private def castStrongTarget {F G G' : Family.{u,v,w,uE,vE,wE} Γ}
    (e : G = G') (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G'.toPseudofunctor := by
  cases e
  exact θ

private theorem castStrongTarget_app {F G G' : Family.{u,v,w,uE,vE,wE} Γ}
    (e : G = G') (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (x : Γ) : HEq ((castStrongTarget e θ).app x) (θ.app x) := by
  cases e
  rfl

private theorem castStrongTarget_heq {F G G' : Family.{u,v,w,uE,vE,wE} Γ}
    (e : G = G') (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    HEq (castStrongTarget e θ) θ := by
  cases e
  rfl

/-- Forward action of a contraction with its strict identity target normalized. -/
noncomputable def forwardFamilyContraction :
    Pseudofunctor.StrongTrans (reindex R E).toPseudofunctor E.toPseudofunctor :=
  castStrongTarget (StrictTwoTransformation.functor_id_comp E) (strongPostcomp η E)

theorem forwardFamilyContraction_heq :
    HEq (forwardFamilyContraction R η E) (strongPostcomp η E) :=
  castStrongTarget_heq (StrictTwoTransformation.functor_id_comp E) (strongPostcomp η E)

theorem forwardFamilyContraction_app (x : Γ) :
    (forwardFamilyContraction R η E).app x = E.map (η.app x) :=
  eq_of_heq (castStrongTarget_app (StrictTwoTransformation.functor_id_comp E)
    (strongPostcomp η E) x)

instance forwardFamilyContraction_isIso (x : Γ) :
    IsIso ((forwardFamilyContraction R η E).app x) := by
  rw [forwardFamilyContraction_app]
  change IsIso (E.toFunctor.map (η.app x))
  infer_instance

/-- Backward transport is the constructed coherent inverse of forward action. -/
noncomputable def inverseFamilyContraction :
    Pseudofunctor.StrongTrans E.toPseudofunctor (reindex R E).toPseudofunctor :=
  strongInverse (forwardFamilyContraction R η E)

theorem inverseFamilyContraction_app (x : Γ) :
    (inverseFamilyContraction R η E).app x = E.map (inv (η.app x)) := by
  change inv ((forwardFamilyContraction R η E).app x) = _
  apply IsIso.inv_eq_of_hom_inv_id
  rw [forwardFamilyContraction_app, ← E.map_comp, IsIso.hom_inv_id, E.map_id]
  rfl

/-- Pull every tail element back along the inverse contraction component. -/
noncomputable def contractionBack : StrictPseudofunctor (Total E) (Total (reindex R E)) :=
  StrongMap.toHigher (inverseFamilyContraction R η E)

/-- The lifted endofunctor transports the dependent element rather than dropping it. -/
noncomputable def contractionLift : StrictPseudofunctor (Total E) (Total E) :=
  (contractionBack R η E).comp (reindexHigher E R)

theorem contractionLift_obj (x : Total E) :
    (contractionLift R η E).obj x = ⟨R.obj x.base, (E.map (inv (η.app x.base))).obj x.fiber⟩ := by
  change (⟨R.obj x.base, ((inverseFamilyContraction R η E).app x.base).obj x.fiber⟩ : Total E) = _
  rw [inverseFamilyContraction_app]

/-- Forward transport recovers the element transported backwards, for every family. -/
theorem contractionLiftBoundary (x : Total E) :
    (E.map (η.app x.base)).obj ((E.map (inv (η.app x.base))).obj x.fiber) = x.fiber := by
  have h : E.map (inv (η.app x.base)) ≫ E.map (η.app x.base) = 𝟙 (E.obj x.base) := by
    calc
      _ = E.map (inv (η.app x.base) ≫ η.app x.base) := (E.map_comp _ _).symm
      _ = _ := by rw [IsIso.inv_hom_id, E.map_id]; rfl
  exact congrArg (fun H => H.obj x.fiber) h

/-- The lifted component retains the base contraction and its dependent transport boundary. -/
noncomputable def contractionLiftComponent (x : Total E) :
    (contractionLift R η E).obj x ⟶ x :=
  eqToHom (contractionLift_obj R η E x) ≫
    (⟨η.app x.base, eqToHom (contractionLiftBoundary R η E x)⟩ :
      (⟨R.obj x.base, (E.map (inv (η.app x.base))).obj x.fiber⟩ : Total E) ⟶ x)

end SquareKit.Internal.PathTransport.TwoFamily

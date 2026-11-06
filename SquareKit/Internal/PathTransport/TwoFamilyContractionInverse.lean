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

private def castStrongSource {F F' G : Family.{u,v,w,uE,vE,wE} Γ}
    (e : F = F') (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans F'.toPseudofunctor G.toPseudofunctor := by
  cases e
  exact θ

private theorem castStrongSource_app {F F' G : Family.{u,v,w,uE,vE,wE} Γ}
    (e : F = F') (θ : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (x : Γ) : HEq ((castStrongSource e θ).app x) (θ.app x) := by
  cases e
  rfl

/-- Backward action of a coherent contraction on an arbitrary dependent family.
The strict identity boundary is changed by equality transport of all laws. -/
noncomputable def inverseFamilyContraction :
    Pseudofunctor.StrongTrans E.toPseudofunctor (reindex R E).toPseudofunctor :=
  castStrongSource (StrictTwoTransformation.functor_id_comp E)
    (strongPostcomp (strongInverse η) E)

theorem inverseFamilyContraction_app (x : Γ) :
    (inverseFamilyContraction R η E).app x = E.map (inv (η.app x)) :=
  eq_of_heq (castStrongSource_app (StrictTwoTransformation.functor_id_comp E)
    (strongPostcomp (strongInverse η) E) x)

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

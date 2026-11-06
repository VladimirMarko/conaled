import SquareKit.Internal.PathTransport.TwoFamilyReindexFaithful
import SquareKit.Internal.PathTransport.TwoStrongReflect
import SquareKit.Internal.PathTransport.TwoStrongCast
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ) (σ : StrictPseudofunctor Δ Γ)
variable {A : Type*} [Bicategory A] [Strict A]
variable {F G : StrictPseudofunctor A (Total (reindex σ E))}
theorem reindexStrongBoundary (K : StrictPseudofunctor A (Total (reindex σ E))) :
    (K.comp (projectionHigher (reindex σ E))).comp σ =
      (K.comp (reindexHigher E σ)).comp (projectionHigher E) := by
  rw [strictFunctor_comp_assoc, strictFunctor_comp_assoc, reindexHigher_projection]
variable (β : Pseudofunctor.StrongTrans (F.comp (projectionHigher (reindex σ E))).toPseudofunctor
    (G.comp (projectionHigher (reindex σ E))).toPseudofunctor)
variable (θ : Pseudofunctor.StrongTrans (F.comp (reindexHigher E σ)).toPseudofunctor
    (G.comp (reindexHigher E σ)).toPseudofunctor)
variable (h : HEq (strongPostcomp β σ) (strongPostcomp θ (projectionHigher E)))
include h in
theorem reindexStrongApp_base (x : A) : σ.map (β.app x) = (θ.app x).base :=
  eq_of_heq (strongTrans_app_heq (reindexStrongBoundary E σ F) (reindexStrongBoundary E σ G)
    _ _ h x)
def reindexStrongApp (x : A) : F.obj x ⟶ G.obj x :=
  reindexLiftHom E σ (θ.app x) (β.app x) (reindexStrongApp_base E σ β θ h x)
theorem reindexStrongApp_map (x : A) :
    (reindexHigher E σ).map (reindexStrongApp E σ β θ h x) = θ.app x := reindexLiftHom_map _ _ _ _ _
theorem reindexStrongCell_source {x y : A} (p : x ⟶ y) :
    (reindexHigher E σ).map (F.map p ≫ reindexStrongApp E σ β θ h y) =
      (F.comp (reindexHigher E σ)).map p ≫ θ.app y := by
  rw [(reindexHigher E σ).map_comp, reindexStrongApp_map]
  rfl
theorem reindexStrongCell_target {x y : A} (p : x ⟶ y) :
    (reindexHigher E σ).map (reindexStrongApp E σ β θ h x ≫ G.map p) =
      θ.app x ≫ (G.comp (reindexHigher E σ)).map p := by
  rw [(reindexHigher E σ).map_comp, reindexStrongApp_map]
  rfl
def reindexStrongCellImage {x y : A} (p : x ⟶ y) :=
  eqToHom (reindexStrongCell_source E σ β θ h p) ≫ (θ.naturality p).hom ≫
    eqToHom (reindexStrongCell_target E σ β θ h p).symm
private theorem cast_cell_base_heq {x y : Total E} {p q p' q' : x ⟶ y}
    (ep : p = p') (eq : q = q') (α : p' ⟶ q') :
    HEq ((eqToHom ep ≫ α ≫ eqToHom eq.symm).base) α.base := by
  cases ep; cases eq
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl
include h in
theorem reindexStrongCell_base {x y : A} (p : x ⟶ y) :
    σ.map₂ (β.naturality p).hom = (reindexStrongCellImage E σ β θ h p).base := by
  have h1 := (strongPostcomp_naturality_heq β σ p).symm
  have h2 := strongTrans_naturality_heq (reindexStrongBoundary E σ F) (reindexStrongBoundary E σ G)
    _ _ h p
  have h3 := strongPostcomp_naturality_heq θ (projectionHigher E) p
  have h4 := (cast_cell_base_heq E (reindexStrongCell_source E σ β θ h p)
    (reindexStrongCell_target E σ β θ h p) (θ.naturality p).hom).symm
  exact eq_of_heq (h1.trans (h2.trans (h3.trans h4)))
def reindexStrongCell {x y : A} (p : x ⟶ y) :
    F.map p ≫ reindexStrongApp E σ β θ h y ⟶ reindexStrongApp E σ β θ h x ≫ G.map p :=
  reindexLiftCell E σ (reindexStrongCellImage E σ β θ h p) (β.naturality p).hom
    (reindexStrongCell_base E σ β θ h p)
variable [IsLocallyGroupoid Δ] [∀x, IsLocallyGroupoid (E.obj x)]
noncomputable def reindexStrongNaturality {x y : A} (p : x ⟶ y) := asIso (reindexStrongCell E σ β θ h p)

theorem reindexStrongNaturality_mapped {x y : A} (p : x ⟶ y) :
    HEq (mappedStrongNaturality (reindexHigher E σ) (reindexStrongApp E σ β θ h)
      (reindexStrongNaturality E σ β θ h) p).hom (θ.naturality p).hom := by
  simp only [mappedStrongNaturality, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  change HEq ((reindexHigher E σ).map₂ (reindexStrongCell E σ β θ h p)) _
  rw [reindexStrongCell, reindexLiftCell_map]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

noncomputable def reindexStrongLift
    (hc : ∀{x y : Δ} {p q : x ⟶ y}, Function.Injective (σ.map₂ (f := p) (g := q))) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor :=
  strongReflect (reindexHigher E σ) (reindexStrongApp E σ β θ h)
    (reindexStrongNaturality E σ β θ h)
    (fun {_ _ _ _} => reindexHigher_cell_injective E σ (@hc)) θ
    (funext (reindexStrongApp_map E σ β θ h))
    (reindexStrongNaturality_mapped E σ β θ h)

theorem reindexStrongLift_map
    (hc : ∀{x y : Δ} {p q : x ⟶ y}, Function.Injective (σ.map₂ (f := p) (g := q))) :
    strongPostcomp (reindexStrongLift E σ β θ h (@hc)) (reindexHigher E σ) = θ :=
  strongReflect_postcomp _ _ _ _ _ _ _
end SquareKit.Internal.PathTransport.TwoFamily

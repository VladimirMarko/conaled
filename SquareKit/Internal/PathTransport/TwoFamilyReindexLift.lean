import SquareKit.Internal.PathTransport.TwoFamilySubstitution
import SquareKit.Internal.PathTransport.TwoFamilyComprehension
import SquareKit.Internal.PathTransport.TwoFamilyHEq
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
variable {x y : Total (reindex σ E)}
def reindexLiftHom (p : (reindexHigher E σ).obj x ⟶ (reindexHigher E σ).obj y)
    (b : x.base ⟶ y.base) (h : σ.map b = p.base) : x ⟶ y :=
  ⟨b, eqToHom (congrArg (fun f => (E.map f).obj x.fiber) h) ≫ p.fiber⟩
theorem reindexLiftHom_map (p : (reindexHigher E σ).obj x ⟶ (reindexHigher E σ).obj y)
    (b : x.base ⟶ y.base) (h : σ.map b = p.base) :
    (reindexHigher E σ).map (reindexLiftHom E σ p b h) = p := by
  apply Pseudofunctor.CoGrothendieck.ext h
  exact eqToHom_comp_heq _ _

def reindexLiftCell {p q : x ⟶ y} (α : (reindexHigher E σ).map p ⟶ (reindexHigher E σ).map q)
    (b : p.base ⟶ q.base) (h : σ.map₂ b = α.base) : p ⟶ q :=
  ⟨b, α.fiber ≫ eqToHom (congrArg (fun a => (E.map₂ a).app x.fiber ≫ q.fiber) h.symm)⟩
theorem reindexLiftCell_map {p q : x ⟶ y} (α : (reindexHigher E σ).map p ⟶ (reindexHigher E σ).map q)
    (b : p.base ⟶ q.base) (h : σ.map₂ b = α.base) :
    (reindexHigher E σ).map₂ (reindexLiftCell E σ α b h) = α := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ h
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans (comp_eqToHom_heq _ _).symm

theorem familyCast_projection {F G : Family.{u,v,w,uE,vE,wE} Γ} (e : F = G) :
    (familyCast e).comp (projectionHigher G) = projectionHigher F := by
  cases e
  exact StrictTwoTransformation.functor_id_comp _
theorem familySubstitution_projection {F : Family.{uD,vD,wD,uE,vE,wE} Δ}
    (e : F = reindex σ E) :
    (familySubstitution E σ e).comp (projectionHigher E) = (projectionHigher F).comp σ := by
  unfold familySubstitution
  rw [strictFunctor_comp_assoc, reindexHigher_projection, ← strictFunctor_comp_assoc, familyCast_projection]
variable {A : Type*} [Bicategory A] [Strict A]
def reindexLiftFunctor (b : StrictPseudofunctor A Δ) (H : StrictPseudofunctor A (Total E))
    (h : H.comp (projectionHigher E) = b.comp σ) :
    StrictPseudofunctor A (Total (reindex σ E)) :=
  (factorHigher E H).comp (familySubstitution (reindex σ E) b
    ((congrArg (fun K => reindex K E) h).trans (reindex_comp E σ b).symm))
theorem reindexLiftFunctor_map (b : StrictPseudofunctor A Δ) (H : StrictPseudofunctor A (Total E))
    (h : H.comp (projectionHigher E) = b.comp σ) :
    (reindexLiftFunctor E σ b H h).comp (reindexHigher E σ) = H := by
  unfold reindexLiftFunctor
  rw [strictFunctor_comp_assoc, ← familySubstitution_reindex E σ, familySubstitution_comp]
  rw [familySubstitution_congr E h.symm _ rfl, familySubstitution_reindex]
  exact factorHigher_reindex E H
theorem reindexLiftFunctor_projection (b : StrictPseudofunctor A Δ) (H : StrictPseudofunctor A (Total E))
    (h : H.comp (projectionHigher E) = b.comp σ) :
    (reindexLiftFunctor E σ b H h).comp (projectionHigher (reindex σ E)) = b := by
  unfold reindexLiftFunctor
  rw [strictFunctor_comp_assoc, familySubstitution_projection, ← strictFunctor_comp_assoc]
  change ((sectionOfLift E H).lift.comp (projectionHigher _)).comp b = b
  rw [(sectionOfLift E H).over]
  exact StrictTwoTransformation.functor_id_comp _
end SquareKit.Internal.PathTransport.TwoFamily

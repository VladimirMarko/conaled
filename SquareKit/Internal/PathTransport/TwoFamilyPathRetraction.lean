import SquareKit.Internal.PathTransport.TwoFamilyPathReflexivityHigher
/-! Exact first-endpoint retraction, retaining arbitrary genuine cells. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- The first endpoint projection retains the first component of an arbitrary cell. -/
theorem pathFirst_cell_fiber_heq {x y : PathContext F} {p q : x ⟶ y} (α : p ⟶ q) :
 HEq ((pathFirst F).map₂ α).fiber α.base.fiber.1 := by
 simp [pathFirst, pathEndpoints, projectionHigher, StrongMap.toHigher, StrongMap.map₂,
   StrictTwoTransformation.Trans.toStrong, firstEndpoint]
 rw [StrongMap.classifier_eqToHom_app]
 exact eqToHom_left_heq _ _
private theorem prelax_ext {A B : Type*} [Bicategory A] [Bicategory B]
    (H K : PrelaxFunctor A B) (ho : ∀ x, H.obj x = K.obj x)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (H.map p) (K.map p))
    (hc : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (H.map₂ α) (K.map₂ α)) : H = K := by
  rcases H with ⟨⟨⟨Ho,Hm⟩,Hc⟩,_,_⟩
  rcases K with ⟨⟨⟨Ko,Km⟩,Kc⟩,_,_⟩
  have hO : Ho = Ko := funext ho
  subst Ko
  have hM : @Hm = @Km := by
    funext x y p
    exact eq_of_heq (hm p)
  subst Km
  have hC : @Hc = @Kc := by
    funext x y p q α
    exact eq_of_heq (hc α)
  subst Kc
  rfl
omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem total_cell_heq {x y : Total F} {p q p' q' : x ⟶ y}
 (hp : p = p') (hq : q = q') (α : p ⟶ q) (β : p' ⟶ q')
 (hb : HEq α.base β.base) (hf : HEq α.fiber β.fiber) : HEq α β := by
 cases hp
 cases hq
 apply heq_of_eq
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb) ?_
 exact eq_of_heq (HEq.trans hf (comp_eqToHom_heq _ _).symm)
/-- Reflexivity followed by its first endpoint is the identity in every dimension. -/
theorem pathReflexivity_first :
 (pathReflexivity F).comp (pathFirst F) = StrictPseudofunctor.id (Total F) := by
 have hm {x y : Total F} (p : x ⟶ y) :
     (pathFirst F).map ((pathReflexivity F).map p) = p := by
   apply Pseudofunctor.CoGrothendieck.ext
   · rfl
   · apply HEq.trans (heq_of_eq (pathFirst_map_fiber F ((pathReflexivity F).map p)))
     exact heq_of_eq (diagonal_fiber_fst F p)
 apply StrictTwoTransformation.functor_ext
 apply prelax_ext ((pathReflexivity F).comp (pathFirst F)).toPrelaxFunctor
   (StrictPseudofunctor.id (Total F)).toPrelaxFunctor (fun _ => rfl)
   (fun p => heq_of_eq (hm p))
 intro x y p q α
 apply total_cell_heq F (hm p) (hm q) _ α
 · rfl
 · exact HEq.trans (pathFirst_cell_fiber_heq F ((pathReflexivity F).map₂ α))
     (diagonal_cell_fst_heq F α)
end SquareKit.Internal.PathTransport.TwoFamily

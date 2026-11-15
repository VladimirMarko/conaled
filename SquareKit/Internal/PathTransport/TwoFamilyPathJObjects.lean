import SquareKit.Internal.PathTransport.TwoFamilyPathJ
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable [IsLocallyGroupoid Γ]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
/-- Every higher motive sends the normalized reflexive component to identity action. -/
theorem contractionTransport_obj_refl (x : Total F)
    (a : E.obj ((contractionRetract F).obj ((pathReflexivity F).obj x))) :
    HEq ((E.map ((pathContraction F).app ((pathReflexivity F).obj x))).obj a) a := by
  have h := congrArg E.map (pathContraction_app_refl F x)
  have k := h.trans (E.map_id ((pathReflexivity F).obj x))
  exact congr_arg_heq (fun H => H.obj a) k

/-- Transport fixes the fiber object of any section at a reflexive path. -/
theorem transport_obj_refl (s : Section (reindex (contractionRetract F) E)) (x : Total F) :
    HEq (((Section.transport E (pathContraction F) s).lift.obj
      ((pathReflexivity F).obj x)).fiber) ((s.lift.obj ((pathReflexivity F).obj x)).fiber) := by
  have hb : (s.lift.obj ((pathReflexivity F).obj x)).base = (pathReflexivity F).obj x :=
    congrArg (fun H => H.obj ((pathReflexivity F).obj x)) s.over
  have h (b : PathContext F) (e : b = (pathReflexivity F).obj x)
      (a : E.obj ((contractionRetract F).obj b)) :
      HEq ((E.map ((pathContraction F).app b)).obj a) a := by
    subst b
    exact contractionTransport_obj_refl F E x a
  exact h _ hb _

/-- The constructed eliminator recovers each supplied fiber object at reflexivity. -/
theorem pathJ_obj_beta (d : Section (reindex (pathReflexivity F) E)) (x : Total F) :
    HEq (((pathJ F E d).lift.obj ((pathReflexivity F).obj x)).fiber)
      ((d.lift.obj x).fiber) := by
  dsimp only [pathJ]
  refine HEq.trans (Section.cast_obj_fiber _ _ _) ?_
  refine HEq.trans (transport_obj_refl F E _ x) ?_
  refine HEq.trans (Section.cast_obj_fiber _ _ _) ?_
  exact d.reindex_obj_fiber (reindex (pathReflexivity F) E) (pathFirst F)
    ((pathReflexivity F).obj x)
end SquareKit.Internal.PathTransport.TwoFamily

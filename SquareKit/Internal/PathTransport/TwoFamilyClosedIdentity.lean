import SquareKit.Internal.PathTransport.TwoFamilyEndpointSections
import SquareKit.Internal.PathTransport.TwoFamilyPathReflexivityHigher
/-! Closed identity families and reflexivity obtained from the open path context.
The hom-groupoid retains its genuine higher witness arrows. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
noncomputable def closedId (s t : Section F) : Family.{uΓ,vΓ,wΓ,v,w,w} Γ :=
  reindex (endpointPair F s t).lift (openIdHigher F)

instance closedId_groupoid (s t : Section F) (γ : Γ) : IsGroupoid ((closedId F s t).obj γ) :=
  inferInstanceAs (IsGroupoid ((openIdHigher F).obj ((endpointPair F s t).lift.obj γ)))
instance closedId_locallyGroupoid (s t : Section F) (γ : Γ) : IsLocallyGroupoid ((closedId F s t).obj γ) :=
  inferInstanceAs (IsLocallyGroupoid ((openIdHigher F).obj ((endpointPair F s t).lift.obj γ)))

theorem closedReflexivity_base (s : Section F) :
    factorBase (openIdHigher F) (s.lift.comp (pathReflexivity F)) = (endpointPair F s s).lift := by
  rw [endpointPair_diagonal]
  change (s.lift.comp (pathReflexivity F)).comp (pathEndpoints F) = _
  calc
    (s.lift.comp (pathReflexivity F)).comp (pathEndpoints F) =
        s.lift.comp ((pathReflexivity F).comp (pathEndpoints F)) :=
      StrictTwoTransformation.functor_ext rfl
    _ = s.lift.comp (diagonalTotal F) := by rw [pathReflexivity_endpoints]

noncomputable def closedReflexivity (s : Section F) : Section (closedId F s s) :=
  Section.cast (congrArg (fun H => reindex H (openIdHigher F)) (closedReflexivity_base F s))
    (sectionOfLift (openIdHigher F) (s.lift.comp (pathReflexivity F)))

theorem closedReflexivity_obj (s : Section F) (γ : Γ) :
    HEq (((closedReflexivity F s).lift.obj γ).fiber)
      (show LocallyDiscrete ((s.lift.obj γ).fiber ⟶ (s.lift.obj γ).fiber) from ⟨𝟙 _⟩) := by
  exact Section.cast_obj_fiber _ _ γ
end SquareKit.Internal.PathTransport.TwoFamily

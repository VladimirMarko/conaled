import SquareKit.Internal.PathTransport.TwoFamilyPathContractionStrong
import SquareKit.Internal.PathTransport.TwoStrongTransport
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
universe uE vE wE
/-- Extend any higher motive section from reflexivity along the constructed contraction.
This constructs the full higher section; its beta and substitution laws are separate obligations. -/
noncomputable def pathJ [IsLocallyGroupoid Γ]
    (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
    (d : Section (reindex (pathReflexivity F) E)) : Section E := by
  let pulled : Section (reindex (contractionRetract F) E) :=
    Section.cast (reindex_comp E (pathReflexivity F) (pathFirst F))
      (d.reindex (reindex (pathReflexivity F) E) (pathFirst F))
  exact Section.cast (reindex_id E) (Section.transport E (pathContraction F) pulled)

end SquareKit.Internal.PathTransport.TwoFamily

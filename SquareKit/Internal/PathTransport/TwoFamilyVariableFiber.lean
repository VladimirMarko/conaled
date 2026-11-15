import SquareKit.Internal.PathTransport.TwoFamilyModelData
import SquareKit.Internal.PathTransport.TwoFamilyClosedComparison
import SquareKit.Internal.PathTransport.TwoFamilyClosedReflexivitySubstitution
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable {Γ : Context.{u}} (A : Family Γ) (γ : Γ)
theorem variableFamily_fiber :
 reindex (fiberInclusion A.data γ) (reindex (projectionHigher A.data) A.data) =
 constantFamily (A.data.obj γ) (A.data.obj γ) := by
 apply strictFunctorData_ext
 apply prelaxData_ext
 · intro x; rfl
 · intro x y p
   change HEq (A.data.map (𝟙 γ)) (StrictPseudofunctor.id (A.data.obj γ))
   exact heq_of_eq (A.data.map_id γ)
 · intro x y p q α
   change HEq (A.data.map₂ (𝟙 (𝟙 γ))) (𝟙 (StrictPseudofunctor.id (A.data.obj γ)))
   rw [A.data.map₂_id]
   exact congr_arg_heq (fun H => 𝟙 H) (A.data.map_id γ)
noncomputable def variableSectionFiber
 (s : TwoFamily.Section (reindex (projectionHigher A.data) A.data)) :=
 TwoFamily.Section.cast (variableFamily_fiber A γ)
  (s.reindex _ (fiberInclusion A.data γ))
noncomputable def closedSectionCast {Ξ : Type u} [Bicategory.{u,u} Ξ] [Strict Ξ]
 {F G : TwoFamily.Family.{u,u,u,u,u,u} Ξ}
 [∀ ξ, IsGroupoid (F.obj ξ)] [∀ ξ, IsLocallyGroupoid (F.obj ξ)]
 [∀ ξ, IsGroupoid (G.obj ξ)] [∀ ξ, IsLocallyGroupoid (G.obj ξ)]
 (e : F = G) (s t : TwoFamily.Section F) (p : TwoFamily.Section (closedId F s t)) :
 TwoFamily.Section (closedId G (TwoFamily.Section.cast e s) (TwoFamily.Section.cast e t)) := by
 cases e
 exact p
local instance : ∀ a : A.data.obj γ, IsGroupoid ((constantFamily (A.data.obj γ) (A.data.obj γ)).obj a) :=
 fun _ => A.groupoid γ
local instance : ∀ a : A.data.obj γ, IsLocallyGroupoid ((constantFamily (A.data.obj γ) (A.data.obj γ)).obj a) :=
 fun _ => A.locallyGroupoid γ
noncomputable def variableComparisonFiber
 (s t : TwoFamily.Section (reindex (projectionHigher A.data) A.data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher A.data) A.data) s t)) :=
 closedSectionCast (variableFamily_fiber A γ) _ _
  (TwoFamily.Section.cast
   (closedId_reindex (reindex (projectionHigher A.data) A.data) (fiberInclusion A.data γ) s t)
   (p.reindex _ (fiberInclusion A.data γ)))
noncomputable def variableStrongFiber
 (s t : TwoFamily.Section (reindex (projectionHigher A.data) A.data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher A.data) A.data) s t)) :=
 closedComparison (constantFamily (A.data.obj γ) (A.data.obj γ))
  (variableSectionFiber A γ s) (variableSectionFiber A γ t)
  (variableComparisonFiber A γ s t p)
end SquareKit.Internal.PathTransport.HigherInterpretation

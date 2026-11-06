import SquareKit.Internal.PathTransport.TwoFamilyContractionLift
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws
import SquareKit.Internal.PathTransport.TwoStrongTransport
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uA vA wA uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor) [∀x, IsIso (η.app x)]
variable (E : Family.{u,v,w,uE,vE,wE} Γ) [∀x, IsLocallyGroupoid (E.obj x)]
/-- Pull the dependent variable backwards along the chosen contraction before retracting. -/
noncomputable def contractionRetraction : StrictPseudofunctor (Total E) (Total (reindex i E)) :=
  (contractionBack (r.comp i) η E).comp
    ((familyCast (reindex_comp E i r).symm).comp (reindexHigher (reindex i E) r))

private theorem comp_assoc {X Y Z W : Type*} [Bicategory X] [Bicategory Y]
    [Bicategory Z] [Bicategory W] (f : StrictPseudofunctor X Y)
    (g : StrictPseudofunctor Y Z) (h : StrictPseudofunctor Z W) :
    (f.comp g).comp h = f.comp (g.comp h) := StrictTwoTransformation.functor_ext rfl

theorem contractionRetraction_inclusion :
    (contractionRetraction i r η E).comp (reindexHigher E i) = contractionLift (r.comp i) η E := by
  unfold contractionRetraction
  rw [comp_assoc, comp_assoc, reindexHigher_comp_cast]
  rfl

private def castStrongSource {X Y : Type*} [Bicategory X] [Bicategory Y]
    {F F' G : StrictPseudofunctor X Y} (e : F = F')
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G.toPseudofunctor) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor := by cases e; exact θ

noncomputable def contractionRetractionHomotopy :
    Pseudofunctor.StrongTrans
      ((contractionRetraction i r η E).comp (reindexHigher E i)).toPseudofunctor
      (StrictPseudofunctor.id (Total E)).toPseudofunctor :=
  castStrongSource (contractionRetraction_inclusion i r η E)
    (liftedContraction E (r.comp i) η)

end SquareKit.Internal.PathTransport.TwoFamily

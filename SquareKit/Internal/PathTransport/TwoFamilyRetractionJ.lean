import SquareKit.Internal.PathTransport.TwoStrongTransport
import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uA vA wA uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor)
/-- A coherent retraction extends every higher motive section, with no Π assumption. -/
noncomputable def retractionJ (E : Family.{u,v,w,uE,vE,wE} Γ)
    (d : Section (reindex i E)) : Section E := by
  let pulled : Section (reindex (r.comp i) E) :=
    Section.cast (reindex_comp E i r) (d.reindex (reindex i E) r)
  exact Section.cast (reindex_id E) (Section.transport E η pulled)
end SquareKit.Internal.PathTransport.TwoFamily

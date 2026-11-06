import SquareKit.Internal.PathTransport.TwoFamilyRetractionJ
import SquareKit.Internal.PathTransport.TwoFamilySectionHEq
import SquareKit.Internal.PathTransport.TwoStrongCongr
import SquareKit.Internal.PathTransport.TwoStrongInverseIdentity
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uA vA wA uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (hi : i.comp r = StrictPseudofunctor.id A)
variable (hη : HEq (strongPrecomp η i) (Pseudofunctor.StrongTrans.id i.toPseudofunctor))
variable (E : Family.{u,v,w,uE,vE,wE} Γ)

include hi
theorem contraction_reflexive_source : i.comp (r.comp i) = i := by
  rw [← strictFunctor_comp_assoc, hi, StrictTwoTransformation.functor_id_comp]

theorem retractionJSource_beta : reindex i (reindex (r.comp i) E) = reindex i E :=
  (reindex_comp E (r.comp i) i).trans
    (congrArg (fun K => reindex K E) (contraction_reflexive_source i r hi))

omit hi in
theorem retractionJTarget_beta : reindex i (reindex (StrictPseudofunctor.id Γ) E) = reindex i E :=
  congrArg (reindex i) (reindex_id E)

include hη in
theorem retractionJMotive_beta :
    HEq (strongPrecomp (strongPostcomp η E) i)
      (Pseudofunctor.StrongTrans.id (reindex i E).toPseudofunctor) := by
  have h1 := (strongPostcomp_precomp η i E).symm
  have h2 := strongPostcomp_heq (contraction_reflexive_source i r hi)
    (StrictTwoTransformation.functor_comp_id i) (strongPrecomp η i)
    (Pseudofunctor.StrongTrans.id i.toPseudofunctor) hη E
  have h3 := heq_of_eq (strongPostcomp_id i E)
  exact h1.trans (h2.trans h3)

theorem retractionJInput_beta (d : Section (reindex i E)) :
    HEq ((Section.cast (reindex_comp E i r) (d.reindex _ r)).reindex _ i) d := by
  have h1 := (Section.reindex_heq (reindex_comp E i r) (d.reindex _ r)
    (Section.cast (reindex_comp E i r) (d.reindex _ r))
    (Section.cast_heq (reindex_comp E i r) (d.reindex _ r)).symm i).symm
  have h2 := Section.reindex_comp_heq d r i
  have h3 := Section.reindex_functor_heq d hi
  have h4 := (Section.cast_heq (reindex_id (reindex i E)) (d.reindex _ (StrictPseudofunctor.id A))).symm.trans
    (heq_of_eq (Section.reindex_id (reindex i E) d))
  exact h1.trans (h2.trans (h3.trans h4))

include hη in
/-- Reflexive normalization of the contraction gives whole-section computation. -/
theorem retractionJ_beta (d : Section (reindex i E)) :
    (retractionJ i r η E d).reindex E i = d := by
  let s := Section.cast (reindex_comp E i r) (d.reindex _ r)
  let θ := strongPostcomp η E
  have h1 := (Section.reindex_heq (reindex_id E) (s.map θ) (retractionJ i r η E d)
    (Section.cast_heq (reindex_id E) (s.map θ)).symm i).symm
  have h2 := heq_of_eq (Section.map_reindex θ i s)
  have h3 := Section.map_heq (retractionJSource_beta i r hi E) (retractionJTarget_beta i E)
    (strongPrecomp θ i) (Pseudofunctor.StrongTrans.id (reindex i E).toPseudofunctor)
    (retractionJMotive_beta i r η hi hη E) (s.reindex _ i) d
    (retractionJInput_beta i r hi E d)
  have h4 := heq_of_eq (Section.map_identity (reindex i E) d)
  exact eq_of_heq (h1.trans (h2.trans (h3.trans h4)))

end SquareKit.Internal.PathTransport.TwoFamily

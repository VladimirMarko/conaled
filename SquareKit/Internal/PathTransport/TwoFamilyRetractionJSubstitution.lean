import SquareKit.Internal.PathTransport.TwoFamilyRetractionJBeta
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uD vD wD uA vA wA uB vB wB uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable {B : Type uB} [Bicategory.{wB,vB} B] [Strict B]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (i' : StrictPseudofunctor B Δ) (r' : StrictPseudofunctor Δ B)
variable (σ : StrictPseudofunctor Δ Γ) (σ₀ : StrictPseudofunctor B A)
variable (hi : i'.comp σ = σ₀.comp i) (hr : r'.comp σ₀ = σ.comp r)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (η' : Pseudofunctor.StrongTrans (r'.comp i').toPseudofunctor (StrictPseudofunctor.id Δ).toPseudofunctor)
variable (hη : HEq (strongPostcomp η' σ) (strongPrecomp η σ))
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
include hi in
theorem retractionBranch_family : reindex σ₀ (reindex i E) = reindex i' (reindex σ E) :=
  (reindex_comp E i σ₀).trans ((congrArg (fun K => reindex K E) hi.symm).trans (reindex_comp E σ i').symm)

def retractionBranchReindex (d : Section (reindex i E)) : Section (reindex i' (reindex σ E)) :=
  Section.cast (retractionBranch_family i i' σ σ₀ hi E) (d.reindex _ σ₀)
include hi hr in
theorem retractionSource_square : (r'.comp i').comp σ = σ.comp (r.comp i) := by
  rw [strictFunctor_comp_assoc, hi, ← strictFunctor_comp_assoc, hr, strictFunctor_comp_assoc]

include hi hr in
theorem retractionJSource_reindex : reindex (r'.comp i') (reindex σ E) = reindex σ (reindex (r.comp i) E) :=
  (reindex_comp E σ (r'.comp i')).trans ((congrArg (fun K => reindex K E)
    (retractionSource_square i r i' r' σ σ₀ hi hr)).trans (reindex_comp E (r.comp i) σ).symm)

theorem retractionJTarget_reindex : reindex (StrictPseudofunctor.id Δ) (reindex σ E) =
    reindex σ (reindex (StrictPseudofunctor.id Γ) E) :=
  (reindex_id (reindex σ E)).trans (congrArg (reindex σ) (reindex_id E)).symm

include hi hr hη in
theorem retractionJMotive_reindex : HEq (strongPostcomp η' (reindex σ E))
    (strongPrecomp (strongPostcomp η E) σ) := by
  have h1 := (strongPostcomp_comp η' σ E).symm
  have h2 := strongPostcomp_heq (retractionSource_square i r i' r' σ σ₀ hi hr)
    ((StrictTwoTransformation.functor_id_comp σ).trans (StrictTwoTransformation.functor_comp_id σ).symm)
    (strongPostcomp η' σ) (strongPrecomp η σ) hη E
  have h3 := strongPostcomp_precomp η σ E
  exact h1.trans (h2.trans h3)
include hi hr in
theorem retractionJInput_reindex (d : Section (reindex i E)) :
    HEq (Section.cast (reindex_comp (reindex σ E) i' r')
      ((retractionBranchReindex i i' σ σ₀ hi E d).reindex _ r'))
      ((Section.cast (reindex_comp E i r) (d.reindex _ r)).reindex _ σ) := by
  let d' := retractionBranchReindex i i' σ σ₀ hi E d
  have h1 := Section.cast_heq (reindex_comp (reindex σ E) i' r') (d'.reindex _ r')
  have h2 := (Section.reindex_heq (retractionBranch_family i i' σ σ₀ hi E)
    (d.reindex _ σ₀) d' (Section.cast_heq (retractionBranch_family i i' σ σ₀ hi E) (d.reindex _ σ₀)).symm r').symm
  have h3 := Section.reindex_comp_heq d σ₀ r'
  have h4 := Section.reindex_functor_heq d hr
  have h5 := (Section.reindex_comp_heq d r σ).symm
  have h6 := Section.reindex_heq (reindex_comp E i r) (d.reindex _ r)
    (Section.cast (reindex_comp E i r) (d.reindex _ r))
    (Section.cast_heq (reindex_comp E i r) (d.reindex _ r)).symm σ
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

include hi hr hη in
/-- Coherent substitution of the chosen contraction data preserves every higher eliminator. -/
theorem retractionJ_reindex (d : Section (reindex i E)) :
    (retractionJ i r η E d).reindex E σ =
      retractionJ i' r' η' (reindex σ E) (retractionBranchReindex i i' σ σ₀ hi E d) := by
  let d' := retractionBranchReindex i i' σ σ₀ hi E d
  let s := Section.cast (reindex_comp E i r) (d.reindex _ r)
  let s' := Section.cast (reindex_comp (reindex σ E) i' r') (d'.reindex _ r')
  let θ := strongPostcomp η E
  let θ' := strongPostcomp η' (reindex σ E)
  have h1 := Section.cast_heq (reindex_id (reindex σ E)) (s'.map θ')
  have h2 := Section.map_heq (retractionJSource_reindex i r i' r' σ σ₀ hi hr E)
    (retractionJTarget_reindex σ E) θ' (strongPrecomp θ σ)
    (retractionJMotive_reindex i r i' r' σ σ₀ hi hr η η' hη E)
    s' (s.reindex _ σ) (retractionJInput_reindex i r i' r' σ σ₀ hi hr E d)
  have h3 := (heq_of_eq (Section.map_reindex θ σ s)).symm
  have h4 := Section.reindex_heq (reindex_id E) (s.map θ) (retractionJ i r η E d)
    (Section.cast_heq (reindex_id E) (s.map θ)).symm σ
  exact (eq_of_heq (h1.trans (h2.trans (h3.trans h4)))).symm

end SquareKit.Internal.PathTransport.TwoFamily

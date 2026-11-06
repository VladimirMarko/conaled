import SquareKit.Internal.PathTransport.TwoFamilyRetractionJSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyContractionBackSubstitution
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

variable [IsLocallyGroupoid Γ] [IsLocallyGroupoid Δ]
variable [∀x, IsIso (η.app x)] [∀x, IsIso (η'.app x)]
variable [∀x, IsLocallyGroupoid (E.obj x)]

def contractionBranchSubstitution := familySubstitution (reindex i E) σ₀
  (retractionBranch_family i i' σ σ₀ hi E).symm

include hi in
theorem contractionInclusion_reindex :
    (reindexHigher (reindex σ E) i').comp (reindexHigher E σ) =
      (contractionBranchSubstitution i i' σ σ₀ hi E).comp (reindexHigher E i) := by
  unfold contractionBranchSubstitution
  rw [← familySubstitution_reindex (reindex σ E) i', ← familySubstitution_reindex E σ,
    ← familySubstitution_reindex E i, familySubstitution_comp, familySubstitution_comp]
  exact familySubstitution_congr E hi _ _

include hi hr hη in
theorem contractionRetraction_reindex :
    (contractionRetraction i' r' η' (reindex σ E)).comp
      (contractionBranchSubstitution i i' σ σ₀ hi E) =
      (reindexHigher E σ).comp (contractionRetraction i r η E) := by
  let hR := retractionSource_square i r i' r' σ σ₀ hi hr
  have hb := contractionBack_reindex (r.comp i) (r'.comp i') σ hR η η' hη E
  change ((contractionBack (r'.comp i') η' (reindex σ E)).comp
    (familySubstitution (reindex i' (reindex σ E)) r' (reindex_comp (reindex σ E) i' r').symm)).comp
    (familySubstitution (reindex i E) σ₀ (retractionBranch_family i i' σ σ₀ hi E).symm) =
    (reindexHigher E σ).comp ((contractionBack (r.comp i) η E).comp
      (familySubstitution (reindex i E) r (reindex_comp E i r).symm))
  rw [strictFunctor_comp_assoc, familySubstitution_comp,
    ← strictFunctor_comp_assoc, ← hb, strictFunctor_comp_assoc, familySubstitution_comp]
  congr 1
  exact familySubstitution_congr (reindex i E) hr _ _
end SquareKit.Internal.PathTransport.TwoFamily

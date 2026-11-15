import SquareKit.Internal.PathTransport.TwoFamilyRetractionJBeta
import SquareKit.Internal.PathTransport.TwoFamilyContractionRetraction
import SquareKit.Internal.PathTransport.TwoStrongInverseSubstitution
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uA vA wA uB vB wB uE vE wE
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable {B : Type uB} [Bicategory.{wB,vB} B] [Strict B]
variable {C : Type*} [Bicategory C] [Strict C]
theorem strongPrecomp_heq {F G F' G' : StrictPseudofunctor A B}
    (eF : F = F') (eG : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq η θ) (K : StrictPseudofunctor C A) :
    HEq (strongPrecomp η K) (strongPrecomp θ K) := by
  cases eF; cases eG; cases eq_of_heq h; rfl

theorem strongInverse_heq {F G F' G' : StrictPseudofunctor A B}
    (eF : F = F') (eG : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    [iη : ∀x, IsIso (η.app x)] [iθ : ∀x, IsIso (θ.app x)] (h : HEq η θ) :
    HEq (strongInverse η) (strongInverse θ) := by
  cases eF; cases eG; cases eq_of_heq h; rfl

namespace TwoFamily
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor) [∀x, IsIso (η.app x)]
variable (hi : i.comp r = StrictPseudofunctor.id A)
variable (hη : HEq (strongPrecomp η i) (Pseudofunctor.StrongTrans.id i.toPseudofunctor))
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
include hi hη

theorem forwardFamilyContraction_reflexive :
    HEq (strongPrecomp (forwardFamilyContraction (r.comp i) η E) i)
      (Pseudofunctor.StrongTrans.id (reindex i E).toPseudofunctor) := by
  have h1 := strongPrecomp_heq rfl (StrictTwoTransformation.functor_id_comp E).symm
    (forwardFamilyContraction (r.comp i) η E) (strongPostcomp η E)
    (forwardFamilyContraction_heq (r.comp i) η E) i
  exact h1.trans (retractionJMotive_beta i r η hi hη E)

theorem inverseFamilyContraction_reflexive :
    HEq (strongPrecomp (inverseFamilyContraction (r.comp i) η E) i)
      (Pseudofunctor.StrongTrans.id (reindex i E).toPseudofunctor) := by
  let α := forwardFamilyContraction (r.comp i) η E
  let iα : ∀x, IsIso ((strongPrecomp α i).app x) := fun x =>
    inferInstanceAs (IsIso (α.app (i.obj x)))
  have h1 := strongInverse_precomp α i
  have h2 := strongInverse_heq (iη := iα) (iθ := fun x => strongId_isIso x) (retractionJSource_beta i r hi E) rfl
    (strongPrecomp α i) (Pseudofunctor.StrongTrans.id (reindex i E).toPseudofunctor)
    (forwardFamilyContraction_reflexive i r η hi hη E)
  have h3 := heq_of_eq (strongInverse_id (F := reindex i E))
  exact (heq_of_eq h1.symm).trans (h2.trans h3)
section CastSquares
omit hi hη
variable {Γ' : Type*} [Bicategory Γ'] [Strict Γ']
variable {Δ' : Type*} [Bicategory Δ'] [Strict Δ']
variable {F G : Family.{_,_,_,uE,vE,wE} Γ'}

theorem familyCast_reindex_square (e : F = G) (σ : StrictPseudofunctor Δ' Γ') :
    (reindexHigher F σ).comp (familyCast e) =
      (familyCast (congrArg (reindex σ) e)).comp (reindexHigher G σ) := by
  cases e
  exact (StrictTwoTransformation.functor_comp_id _).trans
    (StrictTwoTransformation.functor_id_comp _).symm

theorem strongMap_eq_familyCast (e : F = G)
    (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (h : HEq α (Pseudofunctor.StrongTrans.id F.toPseudofunctor)) :
    StrongMap.toHigher α = familyCast e := by
  cases e
  cases eq_of_heq h
  exact StrongMap.toHigher_id F
end CastSquares

include hi hη in
theorem contractionRetraction_reflexive [∀x, IsLocallyGroupoid (E.obj x)] :
    (reindexHigher E i).comp (contractionRetraction i r η E) =
      StrictPseudofunctor.id (Total (reindex i E)) := by
  let α := inverseFamilyContraction (r.comp i) η E
  have hs := strongMap_eq_familyCast (retractionJSource_beta i r hi E).symm
    (strongPrecomp α i) (inverseFamilyContraction_reflexive i r η hi hη E)
  have hsquare := StrongMap.reindex_square α i
  have hc := familyCast_reindex_square (reindex_comp E i r).symm i
  have hform : (reindexHigher E i).comp (contractionRetraction i r η E) =
      (familyCast (retractionJSource_beta i r hi E).symm).comp
        ((familyCast (congrArg (reindex i) (reindex_comp E i r).symm)).comp
          ((reindexHigher (reindex r (reindex i E)) i).comp (reindexHigher (reindex i E) r))) := by
    unfold contractionRetraction
    change (reindexHigher E i).comp ((StrongMap.toHigher α).comp _) = _
    rw [← strictFunctor_comp_assoc, ← hsquare]
    erw [hs]
    change ((familyCast (retractionJSource_beta i r hi E).symm).comp
      (reindexHigher (reindex (r.comp i) E) i)).comp
        ((familyCast (reindex_comp E i r).symm).comp (reindexHigher (reindex i E) r)) = _
    simp only [strictFunctor_comp_assoc]
    rw [← strictFunctor_comp_assoc (reindexHigher (reindex (r.comp i) E) i), hc]
    simp only [strictFunctor_comp_assoc]
  rw [hform]
  have h1 := familyCast_precomp_heq (retractionJSource_beta i r hi E).symm
    ((familyCast (congrArg (reindex i) (reindex_comp E i r).symm)).comp
      ((reindexHigher (reindex r (reindex i E)) i).comp (reindexHigher (reindex i E) r)))
  have h2 := familyCast_precomp_heq (congrArg (reindex i) (reindex_comp E i r).symm)
    ((reindexHigher (reindex r (reindex i E)) i).comp (reindexHigher (reindex i E) r))
  have h3 := reindexHigher_comp_heq (reindex i E) r i
  have h4 := congr_arg_heq (fun σ => reindexHigher (reindex i E) σ) hi
  have h5 := reindexHigher_id_heq (reindex i E)
  exact eq_of_heq (h1.trans (h2.trans (h3.trans (h4.trans h5))))

end TwoFamily
end SquareKit.Internal.PathTransport

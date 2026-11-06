import SquareKit.Internal.PathTransport.TwoFamilyContractionRetractionSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyCartesianReindex
import SquareKit.Internal.PathTransport.TwoStrongCongr
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


private theorem strongApp_heq {X Y : Type*} [Bicategory X] [Bicategory Y]
    {F G F' G' : StrictPseudofunctor X Y} (eF : F = F') (eG : G = G')
    (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (β : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq α β) (x : X) : HEq (α.app x) (β.app x) := by
  cases eF; cases eG; cases eq_of_heq h; rfl
private theorem strongCell_heq {X Y : Type*} [Bicategory X] [Bicategory Y]
    {F G F' G' : StrictPseudofunctor X Y} (eF : F = F') (eG : G = G')
    (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (β : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (h : HEq α β) {x y : X} (p : x ⟶ y) :
    HEq (α.naturality p).hom (β.naturality p).hom := by
  cases eF; cases eG; cases eq_of_heq h; rfl
include hi hr hη in
theorem rawContraction_reindex :
    HEq (strongPostcomp
      (strongPrecomp (coherentLift η' (reindex σ E)) (contractionBack (r'.comp i') η' (reindex σ E)))
      (reindexHigher E σ))
      (strongPrecomp (strongPrecomp (coherentLift η E) (contractionBack (r.comp i) η E))
        (reindexHigher E σ)) := by
  let k := reindexHigher E σ
  let b := contractionBack (r.comp i) η E
  let b' := contractionBack (r'.comp i') η' (reindex σ E)
  have eF : (b'.comp (coherentLiftLeft (F := r'.comp i') (reindex σ E))).comp k =
      k.comp (b.comp (coherentLiftLeft (F := r.comp i) E)) := by
    change (contractionLift (r'.comp i') η' (reindex σ E)).comp k = k.comp (contractionLift (r.comp i) η E)
    rw [← contractionRetraction_inclusion i' r' η' (reindex σ E),
      ← contractionRetraction_inclusion i r η E, strictFunctor_comp_assoc,
      contractionInclusion_reindex i i' σ σ₀ hi E, ← strictFunctor_comp_assoc,
      contractionRetraction_reindex i r i' r' σ σ₀ hi hr η η' hη E,
      strictFunctor_comp_assoc]
  have eG : (b'.comp (coherentLiftRight η' (reindex σ E))).comp k =
      k.comp (b.comp (coherentLiftRight η E)) := by
    rw [contractionLift_target, contractionLift_target]
    exact (StrictTwoTransformation.functor_id_comp k).trans
      (StrictTwoTransformation.functor_comp_id k).symm
  apply cartesianStrong_hext E eF eG
  · intro x
    change HEq (σ.map (η'.app x.base)) (η.app (σ.obj x.base))
    exact strongApp_heq (retractionSource_square i r i' r' σ σ₀ hi hr)
      ((StrictTwoTransformation.functor_id_comp σ).trans (StrictTwoTransformation.functor_comp_id σ).symm)
      _ _ hη x.base
  · intro x
    exact equalityHomFiber_reindex E σ _ (equalityHomFiber_cartesian (reindex σ E) _ _)
  · intro x
    exact equalityHomFiber_cartesian E _ _
  · intro x y p
    have h1 := postcompReindex_comparison_base E σ
      (strongPrecomp (coherentLift η' (reindex σ E)) b') p
    have h2 := (strongPostcomp_naturality_heq η' σ p.base).symm
    have h3 := strongCell_heq (retractionSource_square i r i' r' σ σ₀ hi hr)
      ((StrictTwoTransformation.functor_id_comp σ).trans (StrictTwoTransformation.functor_comp_id σ).symm)
      _ _ hη p.base
    exact h1.trans (h2.trans h3)
  · intro x y p
    exact postcompReindex_equalityFiber E σ _ p (coherentLiftCell_equalityFiber η' (reindex σ E) (b'.map p))
  · intro x y p
    exact coherentLiftCell_equalityFiber η E (b.map (k.map p))
include hi hr hη in
theorem contractionRetractionHomotopy_reindex :
    HEq (strongPostcomp (contractionRetractionHomotopy i' r' η' (reindex σ E)) (reindexHigher E σ))
      (strongPrecomp (contractionRetractionHomotopy i r η E) (reindexHigher E σ)) := by
  have h0' := (contractionRetractionHomotopy_heq i' r' η' (reindex σ E)).trans
    (liftedContraction_heq (reindex σ E) (r'.comp i') η')
  have h1 := strongPostcomp_heq (contractionRetraction_inclusion i' r' η' (reindex σ E))
    (contractionLift_target (reindex σ E) (r'.comp i') η').symm
    (contractionRetractionHomotopy i' r' η' (reindex σ E))
    (strongPrecomp (coherentLift η' (reindex σ E)) (contractionBack (r'.comp i') η' (reindex σ E)))
    h0' (reindexHigher E σ)
  have h0 := (contractionRetractionHomotopy_heq i r η E).trans
    (liftedContraction_heq E (r.comp i) η)
  have h2 := strongPrecomp_heq (contractionRetraction_inclusion i r η E)
    (contractionLift_target E (r.comp i) η).symm
    (contractionRetractionHomotopy i r η E)
    (strongPrecomp (coherentLift η E) (contractionBack (r.comp i) η E))
    h0 (reindexHigher E σ)
  exact h1.trans ((rawContraction_reindex i r i' r' σ σ₀ hi hr η η' hη E).trans h2.symm)
end SquareKit.Internal.PathTransport.TwoFamily

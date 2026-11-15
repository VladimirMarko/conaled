import SquareKit.Internal.PathTransport.TwoFamilyCartesianStrong
import SquareKit.Internal.PathTransport.TwoFamilyContractionNormalization
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
variable {A : Type*} [Bicategory A] [Strict A] (i : StrictPseudofunctor A Γ)
section RawNormalization
variable [IsLocallyGroupoid Γ]
variable (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
  (StrictPseudofunctor.id Γ).toPseudofunctor) [∀x, IsIso (η.app x)]
variable (hi : i.comp r = StrictPseudofunctor.id A)
variable (hη : HEq (strongPrecomp η i) (Pseudofunctor.StrongTrans.id i.toPseudofunctor))
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
include hi hη in
theorem rawLift_reflexive :
    HEq (strongPrecomp (strongPrecomp (coherentLift η E) (contractionBack (r.comp i) η E))
      (reindexHigher E i))
      (Pseudofunctor.StrongTrans.id (reindexHigher E i).toPseudofunctor) := by
  let k := reindexHigher E i
  let b := contractionBack (r.comp i) η E
  have eF : k.comp (b.comp (coherentLiftLeft (F := r.comp i) E)) = k := by
    change k.comp (contractionLift (r.comp i) η E) = k
    rw [← contractionRetraction_inclusion i r η E, ← strictFunctor_comp_assoc]
    rw [contractionRetraction_reflexive i r η hi hη E]
    exact StrictTwoTransformation.functor_id_comp k
  have eG : k.comp (b.comp (coherentLiftRight η E)) = k := by
    change k.comp ((contractionBack (r.comp i) η E).comp (coherentLiftRight η E)) = k
    rw [contractionLift_target]
    exact StrictTwoTransformation.functor_comp_id k
  apply cartesianStrong_hext E eF eG
  · intro x
    change HEq (η.app (i.obj x.base)) (𝟙 (i.obj x.base))
    exact strongApp_heq (contraction_reflexive_source i r hi)
      (StrictTwoTransformation.functor_comp_id i) _ _ hη x.base
  · intro x
    exact equalityHomFiber_cartesian E _ _
  · intro x
    exact equalityHomFiber_identity E _
  · intro x y p
    change HEq (η.naturality (i.map p.base)).hom _
    exact (strongCell_heq (contraction_reflexive_source i r hi)
      (StrictTwoTransformation.functor_comp_id i) _ _ hη p.base).trans
        (identityReindex_comparison_base E i p).symm
  · intro x y p
    exact coherentLiftCell_equalityFiber η E (b.map (k.map p))
  · intro x y p
    exact identityStrong_equalityFiber E k p
include hi hη in
theorem contractionRetractionHomotopy_reflexive :
    HEq (strongPrecomp (contractionRetractionHomotopy i r η E) (reindexHigher E i))
      (Pseudofunctor.StrongTrans.id (reindexHigher E i).toPseudofunctor) := by
  have h0 := (contractionRetractionHomotopy_heq i r η E).trans
    (liftedContraction_heq E (r.comp i) η)
  have h1 := strongPrecomp_heq (contractionRetraction_inclusion i r η E)
    (contractionLift_target E (r.comp i) η).symm
    (contractionRetractionHomotopy i r η E)
    (strongPrecomp (coherentLift η E) (contractionBack (r.comp i) η E)) h0 (reindexHigher E i)
  exact h1.trans (rawLift_reflexive E i r η hi hη)

end RawNormalization

end SquareKit.Internal.PathTransport.TwoFamily

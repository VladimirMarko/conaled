import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReflexive
import SquareKit.Internal.PathTransport.TwoStrongCongr
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
private theorem identity_boundary_heq {C : Type*} [Category C] {a b c : C}
    (e : a = b) (h : a = c) : HEq (eqToHom e) (𝟙 c) := by cases h; cases e; rfl
theorem strongId_naturality_heq {A B : Type*} [Bicategory A] [Bicategory B] [Strict B]
    (F : StrictPseudofunctor A B) {x y : A} (p : x ⟶ y) :
    HEq ((Pseudofunctor.StrongTrans.id F.toPseudofunctor).naturality p).hom (𝟙 (F.map p)) := by
  simp only [Pseudofunctor.StrongTrans.id, Strict.rightUnitor_eqToIso,
    Strict.leftUnitor_eqToIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans]
  exact identity_boundary_heq _ (Category.comp_id _)
namespace TwoFamily
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀x, IsGroupoid (F.obj x)] [∀x, IsLocallyGroupoid (F.obj x)]
theorem pathContraction_first :
    HEq (strongPostcomp (pathContraction F) (pathFirst F))
      (Pseudofunctor.StrongTrans.id (pathFirst F).toPseudofunctor) := by
  have hF : (contractionRetract F).comp (pathFirst F) = pathFirst F := by
    change ((pathFirst F).comp (pathReflexivity F)).comp (pathFirst F) = _
    rw [strictFunctor_comp_assoc, pathReflexivity_first, StrictTwoTransformation.functor_comp_id]
  apply strongTrans_hext (congrArg (fun K => K.toPseudofunctor) hF)
    (congrArg (fun K => K.toPseudofunctor) (StrictTwoTransformation.functor_id_comp (pathFirst F)))
  · intro x
    exact heq_of_eq (pathFirst_contractionComponent F x)
  · intro x y p
    have h1 := strongPostcomp_naturality_heq (pathContraction F) (pathFirst F) p
    have h2 := contractionNaturalityCell_first_heq F p
    have h3 := (strongId_naturality_heq (pathFirst F) p).symm
    exact h1.trans (h2.trans h3)
end TwoFamily
end SquareKit.Internal.PathTransport

import SquareKit.Internal.PathTransport.SignatureCylinder

/-! Postcomposition of a selected signature cylinder. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D E : Grpd.{u,u}} (F : C ⥤ D) (K : D ⥤ E)

def postcompose : Cylinder F ⥤ Cylinder (F ⋙ K) where
  obj x := ⟨x.source, K.obj x.target, K.mapIso x.arrow⟩
  map f := InducedCategory.homMk f.hom

theorem postcompose_projection : postcompose F K ⋙ projection (F ⋙ K) = projection F := rfl

theorem postcompose_evaluation :
    postcompose F K ⋙ evaluation (F ⋙ K) = evaluation F ⋙ K := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  intro x y f
  simp [postcompose, evaluation]

theorem inclusion_postcompose :
    inclusion F ⋙ postcompose F K = inclusion (F ⋙ K) := by
  fapply CategoryTheory.Functor.ext
  · intro x
    change (⟨x, K.obj (F.obj x), K.mapIso (Iso.refl _)⟩ : Object (F ⋙ K)) = _
    simp [inclusion]
  intro x y f
  apply InducedCategory.hom_ext
  simp [inclusion, postcompose]

theorem endpoint_postcompose {G : C ⥤ D} (η : F ≅ G) :
    endpoint F η ⋙ postcompose F K = endpoint (F ⋙ K) (isoWhiskerRight η K) := rfl

variable (P : C ⥤ Type u)
def postcomposeSignature : Signature.{u} :=
  ⟨⟨Grpd.of (Cylinder F), Grpd.of (Cylinder (F ⋙ K)), postcompose F K⟩,
    projection F ⋙ P, projection (F ⋙ K) ⋙ P, 𝟙 _⟩

theorem inclusion_postcompose_signature :
    (inclusionSignature F P).horizontal (postcomposeSignature F K P) rfl HEq.rfl =
      inclusionSignature (F ⋙ K) P := by
  apply signature_eq (inclusion_postcompose F K)
  apply NatTrans.ext
  funext c
  simp

theorem endpoint_postcompose_signature {G : C ⥤ D} (η : F ≅ G) :
    (endpointSignature F P η).horizontal (postcomposeSignature F K P) rfl HEq.rfl =
      endpointSignature (F ⋙ K) P (isoWhiskerRight η K) := by
  apply signature_eq (endpoint_postcompose F K η)
  apply NatTrans.ext
  funext c
  simp

theorem postcompose_projection_signature :
    (postcomposeSignature F K P).horizontal (projectionSignature (F ⋙ K) P) rfl HEq.rfl =
      projectionSignature F P := by
  apply signature_eq (postcompose_projection F K)
  apply NatTrans.ext
  funext c
  simp

variable (Q : D ⥤ Type u) (R : E ⥤ Type u) (α : P ⟶ F ⋙ Q) (κ : Q ⟶ K ⋙ R)
theorem postcompose_evaluation_signature :
    (postcomposeSignature F K P).horizontal
        (evaluationSignature (F ⋙ K) P R (α ≫ whiskerLeft F κ)) rfl HEq.rfl =
      (evaluationSignature F P Q α).horizontal
        (Signature.mk (Context.mk D E K) Q R κ) rfl HEq.rfl := by
  apply signature_eq (postcompose_evaluation F K)
  apply NatTrans.ext
  funext c
  simp [evaluationFiber, postcompose, eqToHom_app, Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder

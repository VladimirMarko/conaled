import SquareKit.Internal.PathTransport.SignatureCylinder

/-! Precomposition of selected signature cylinders, including arbitrary fiber maps. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B C D : Grpd.{u,u}} (K : B ⥤ C) (F : C ⥤ D)

def precompose : Cylinder (K ⋙ F) ⥤ Cylinder F where
  obj x := ⟨K.obj x.source, x.target, x.arrow⟩
  map f := InducedCategory.homMk (K.map f.hom)

theorem precompose_projection : precompose K F ⋙ projection F = projection (K ⋙ F) ⋙ K := rfl
theorem precompose_evaluation : precompose K F ⋙ evaluation F = evaluation (K ⋙ F) := rfl
theorem inclusion_precompose : inclusion (K ⋙ F) ⋙ precompose K F = K ⋙ inclusion F := rfl
theorem endpoint_precompose {G : C ⥤ D} (η : F ≅ G) :
    endpoint (K ⋙ F) (isoWhiskerLeft K η) ⋙ precompose K F = K ⋙ endpoint F η := rfl

variable (O : B ⥤ Type u) (P : C ⥤ Type u) (κ : O ⟶ K ⋙ P)
def precomposeSignature : Signature.{u} :=
  ⟨⟨Grpd.of (Cylinder (K ⋙ F)), Grpd.of (Cylinder F), precompose K F⟩,
    projection (K ⋙ F) ⋙ O, projection F ⋙ P, whiskerLeft (projection (K ⋙ F)) κ⟩

theorem inclusion_precompose_signature :
    (inclusionSignature (K ⋙ F) O).horizontal (precomposeSignature K F O P κ) rfl HEq.rfl =
      (Signature.mk (Context.mk B C K) O P κ).horizontal (inclusionSignature F P) rfl HEq.rfl := by
  apply signature_eq (inclusion_precompose K F)
  apply NatTrans.ext
  funext c
  simp [projection, inclusion]

theorem endpoint_precompose_signature {G : C ⥤ D} (η : F ≅ G) :
    (endpointSignature (K ⋙ F) O (isoWhiskerLeft K η)).horizontal
        (precomposeSignature K F O P κ) rfl HEq.rfl =
      (Signature.mk (Context.mk B C K) O P κ).horizontal (endpointSignature F P η) rfl HEq.rfl := by
  apply signature_eq (endpoint_precompose K F η)
  apply NatTrans.ext
  funext c
  simp [projection, endpoint]

theorem precompose_projection_signature :
    (precomposeSignature K F O P κ).horizontal (projectionSignature F P) rfl HEq.rfl =
      (projectionSignature (K ⋙ F) O).horizontal
        (Signature.mk (Context.mk B C K) O P κ) rfl HEq.rfl := by
  apply signature_eq (precompose_projection K F)
  apply NatTrans.ext
  funext c
  simp [projection]

theorem precompose_evaluation_signature (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) :
    (precomposeSignature K F O P κ).horizontal (evaluationSignature F P Q α) rfl HEq.rfl =
      evaluationSignature (K ⋙ F) O Q (κ ≫ whiskerLeft K α) := by
  apply signature_eq (precompose_evaluation K F)
  apply NatTrans.ext
  funext c
  simp [evaluationFiber, precompose, projection, Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder

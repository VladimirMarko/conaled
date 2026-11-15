import SquareKit.Internal.PathTransport.SignatureCylinder

/-! Changing the reference endpoint of a selected signature cylinder. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {F G H : C ⥤ D} (η : F ≅ G)

/-- Transport the cylinder's reference arrow, retaining its source and target. -/
def changeReference : Cylinder G ⥤ Cylinder F where
  obj x := ⟨x.source, x.target, η.app x.source ≪≫ x.arrow⟩
  map f := InducedCategory.homMk f.hom

theorem changeReference_projection : changeReference η ⋙ projection F = projection G := rfl

theorem changeReference_evaluation : changeReference η ⋙ evaluation F = evaluation G := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  intro x y f
  dsimp [changeReference, evaluation]
  simp only [Category.assoc]
  rw [η.hom.naturality_assoc]
  simp

theorem inclusion_changeReference : inclusion G ⋙ changeReference η = endpoint F η := by
  fapply CategoryTheory.Functor.ext
  · intro x
    change (⟨x, G.obj x, η.app x ≪≫ Iso.refl _⟩ : Object F) =
      ⟨x, G.obj x, η.app x⟩
    simp
  intro x y f
  apply InducedCategory.hom_ext
  simp [inclusion, changeReference, endpoint]

theorem endpoint_changeReference (θ : G ≅ H) :
    endpoint G θ ⋙ changeReference η = endpoint F (η ≪≫ θ) := rfl

variable (P : C ⥤ Type u)
def changeReferenceSignature : Signature.{u} :=
  ⟨⟨Grpd.of (Cylinder G), Grpd.of (Cylinder F), changeReference η⟩,
    projection G ⋙ P, projection F ⋙ P, 𝟙 _⟩

theorem inclusion_changeReference_signature :
    (inclusionSignature G P).horizontal (changeReferenceSignature η P) rfl HEq.rfl =
      endpointSignature F P η := by
  apply signature_eq (inclusion_changeReference η)
  apply NatTrans.ext
  funext c
  simp

theorem endpoint_changeReference_signature (θ : G ≅ H) :
    (endpointSignature G P θ).horizontal (changeReferenceSignature η P) rfl HEq.rfl =
      endpointSignature F P (η ≪≫ θ) := by
  apply signature_eq (endpoint_changeReference η θ)
  apply NatTrans.ext
  funext c
  simp

theorem changeReference_projection_signature :
    (changeReferenceSignature η P).horizontal (projectionSignature F P) rfl HEq.rfl =
      projectionSignature G P := by
  apply signature_eq (changeReference_projection η)
  apply NatTrans.ext
  funext c
  simp

theorem changeReference_evaluation_signature (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) :
    (changeReferenceSignature η P).horizontal (evaluationSignature F P Q α) rfl HEq.rfl =
      evaluationSignature G P Q (α ≫ whiskerRight η.hom Q) := by
  apply signature_eq (changeReference_evaluation η)
  apply NatTrans.ext
  funext c
  simp [evaluationFiber, changeReference, Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder

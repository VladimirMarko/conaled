import SquareKit.Internal.PathTransport.UniversalTransfer
import SquareKit.Internal.PathTransport.GeneratedCylinderTerms

/-! The selected comparison acts on the unchanged source-derived transfer proof. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.Typed.Authoring.UniversalTransfer
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

def type :=
  (TransferApplication.motive_raw context fixed moving last first second element) ▸
    TyDeriv.sub (TransferFrame.command context fixed).motive.typing
      (TransferApplication.sourceEndpoint context fixed moving last first second element)

end SquareKit.Internal.PathTransport.Typed.Authoring.UniversalTransfer

namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u) {G : C ⥤ D} (η : F ≅ G)
variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (h : α ≫ whiskerRight η.hom Q = β)

/-- The original authoring wrapper is consumed as a generated source derivation. -/
theorem universalTransferComparison :
    SectionCoherence F P η Q α β h Typed.Authoring.UniversalTransfer.context
      Typed.Authoring.UniversalTransfer.type Typed.Authoring.UniversalTransfer.proof :=
  sectionCoherence F P η Q α β h Typed.Authoring.UniversalTransfer.context
    Typed.Authoring.UniversalTransfer.type Typed.Authoring.UniversalTransfer.proof

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder

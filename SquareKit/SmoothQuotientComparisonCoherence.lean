import SquareKit.SmoothQuotientComparison
import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction

/-! Primitive identity and composition of the restriction signature. Generated
context/family coherence is a further closure theorem over these equalities. -/
noncomputable section
namespace SquareKit.SmoothQuotientComparison
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open Internal.PathTransport GroupoidModel
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M}

/-- Identity signature on the exact lifted direct-model base and fibers. -/
def identitySignature (a : Action (locallyConstantGroup H) M) (X : Sheaf topology Type) :
    Comparison.Signature.{1} where
  base := ⟨Grpd.of (AsSmall (Object a X)), Grpd.of (AsSmall (Object a X)), 𝟭 _⟩
  leftFiber := Instance.liftedFamily (Object a X) (family a X)
  rightFiber := Instance.liftedFamily (Object a X) (family a X)
  fiberMap := 𝟙 _

/-- Compose the actual primitive restriction functor and fiber transformation. -/
def compositeSignature (f : Y ⟶ X) (g : Z ⟶ Y) : Comparison.Signature.{1} where
  base := ⟨(signature (a := a) f).base.left, (signature g).base.right,
    (signature f).base.map ⋙ (signature g).base.map⟩
  leftFiber := (signature f).leftFiber
  rightFiber := (signature g).rightFiber
  fiberMap := (signature f).fiberMap ≫ whiskerLeft (signature f).base.map (signature g).fiberMap

theorem signature_id : signature (a := a) (𝟙 X) = identitySignature a X := by
  rfl

theorem signature_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    signature (a := a) (g ≫ f) = compositeSignature (a := a) f g := by
  rfl

end SquareKit.SmoothQuotientComparison

import SquareKit.Internal.PathTransport.ComparisonUniverses
import SquareKit.Internal.PathTransport.SignatureInterpretationMaps

/-! Signature-aware projections of the comparison interpretation. All signature
laws are constructed from its base/fiber definitions. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
universe u
variable (S : Signature.{u})

def leftSignatureMap : Typed.SignatureMap (fullModel S)
    (Instance.fullModel S.base.left S.leftFiber) where
  toModelMap := leftModelMap S
  base _ := rfl
  fiber _ := rfl

def rightSignatureMap : Typed.SignatureMap (fullModel S)
    (Instance.fullModel S.base.right S.rightFiber) where
  toModelMap := rightModelMap S
  base _ := rfl
  fiber _ := rfl

/-- The existing recursive interpreter agrees with the left projection. -/
theorem interpret_left (h : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    HEq ((leftSignatureMap S).mapTm (Typed.interpretTm (fullModel S) h))
      (Typed.interpretTm (Instance.fullModel S.base.left S.leftFiber) h) :=
  (leftSignatureMap S).interpretTm h

/-- The existing recursive interpreter agrees with the right projection. -/
theorem interpret_right (h : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    HEq ((rightSignatureMap S).mapTm (Typed.interpretTm (fullModel S) h))
      (Typed.interpretTm (Instance.fullModel S.base.right S.rightFiber) h) :=
  (rightSignatureMap S).interpretTm h

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

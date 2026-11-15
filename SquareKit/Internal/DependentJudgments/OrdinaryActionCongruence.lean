import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics

/-! Ordinary action respects explicit family and selected-input identifications. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed
universe u
variable (M : Model.{u}) {Γ : M.Context}

theorem ordinaryApValue_congr {A A' C C' : M.Family Γ}
    (hA : A = A') (hC : C = C')
    {t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A))}
    {t' : M.Section (M.extend Γ A') (M.subTy C' (M.weaken Γ A'))}
    {x y : M.Section Γ A} {x' y' : M.Section Γ A'}
    {p : M.Section Γ (M.identity A x y)} {p' : M.Section Γ (M.identity A' x' y')}
    (ht : HEq t t') (hx : HEq x x') (hy : HEq y y') (hp : HEq p p') :
    HEq (ordinaryApValue M A C t x y p) (ordinaryApValue M A' C' t' x' y' p') := by
  cases hA; cases hC; cases ht; cases hx; cases hy; cases hp; rfl

end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics

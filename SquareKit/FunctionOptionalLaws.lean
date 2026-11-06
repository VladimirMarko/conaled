import SquareKit.FunctionOptional

/-! Function coproduct and distribution laws for shared law transport. -/
namespace SquareKit.FunctionCategory
universe u

theorem coproductLaws : CoproductLaws ops.{u} (equality _) coproducts where
  left _ _ := rfl
  right _ _ := rfl
  eta f := by funext x; cases x <;> rfl

theorem distributionLaws : DistributionLaws ops.{u} (equality _) products coproducts distribution where
  collect_distribute _ _ _ := by funext p; rcases p with ⟨a, b | c⟩ <;> rfl
  distribute_collect _ _ _ := by funext p; cases p <;> rfl
end SquareKit.FunctionCategory

import Examples.TwoFamilyFrozenPointData
/-! Observe the selected source homotopy at the concrete frozen assignment.
The whole-object retention theorem supplies the actual source section value. -/
namespace Examples.TwoFamilyFrozenPoint
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2000
-- Inference avoids expanding the eight dependent binders in a repeated header.
set_option linter.defProp false

/-- The selected source value has integer observation `k`. -/
def observation (k : ℤ) :=
  congrArg (fun t : LocallyDiscrete (Discrete (Multiplicative ℤ)) => t.as.as)
    (@eq_of_heq (LocallyDiscrete (Discrete (Multiplicative ℤ))) _ _ (retained k))

private theorem neq_of_observed {α : Sort*} {a b c d : α}
    (ha : c = a) (hb : d = b) (h : c ≠ d) : a ≠ b := by
  intro e
  exact h (ha.trans (e.trans hb.symm))

/-- At assignment `1`, the selected source homotopy is distinguished from zero. -/
def selected_nonzero := neq_of_observed (observation 1).symm
  (rfl : Multiplicative.ofAdd (0:ℤ) = Multiplicative.ofAdd 0)
  (show Multiplicative.ofAdd (1:ℤ) ≠ Multiplicative.ofAdd 0 from
    fun e => Int.one_ne_zero (congrArg Multiplicative.toAdd e))
end Examples.TwoFamilyFrozenPoint

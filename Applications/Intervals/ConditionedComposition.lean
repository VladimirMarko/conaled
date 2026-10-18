import Applications.Intervals.Arithmetic
import SquareKit.ConditionedRelations

/-! Output nonnegativity through interval containment and an arbitrary realization.
No interval decoder or selected contained value is required. -/
namespace IntervalAnalysis
open Relational

/-- `R` may admit several intervals; `T` may admit several final outputs.
`0 ≤ z` depends only on the fixed output, not the interval or contained point. -/
theorem nonnegative_composition {A : Type} (R : A → Interval → Prop)
    (T : ℚ → ℚ → Prop) (a : A) (z : ℚ) :
    (0 ≤ z ∧ compRel (compRel R representation.Rel) T a z) ↔
      ∃ I, 0 ≤ z ∧ R a I ∧ compRel representation.Rel T I z :=
  compRel_condition R representation.Rel T (fun z => 0 ≤ z) a z
end IntervalAnalysis

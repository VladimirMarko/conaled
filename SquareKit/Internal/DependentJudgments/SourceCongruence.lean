import SquareKit.Internal.DependentJudgments.SourceSubstitution

/-! Congruence through a raw source recipe. The premises are derived source
equalities; no interpretation equality is reflected into syntax. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
variable {V W : Type} {Ω : List (Judgment V)}

noncomputable def Equal.recipe (r : Expression W) (s t : W → Expression V)
    (h : ∀ w, Equal (Ω := Ω) (s w) (t w)) : Equal (Ω := Ω) (r.subst s) (r.subst t) := by
  induction r with
  | leaf w => exact h w
  | node op args ih => exact Derivation.congruence op ih

end SquareKit.Internal.DependentJudgments.Contextual

import SquareKit.RelationComposition
import SquareKit.Internal.ConditionedComposition

/-! Ordinary relation consumers of the interpreted Frobenius/reassociation proof. -/
namespace Relational
universe u
variable {A B C D : Type u}

/-- Move an output condition through composition without dropping any edge.
The condition has only the final output as argument, not either intermediate. -/
theorem compRel_condition (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (H : D → Prop) (a : A) (d : D) :
    (H d ∧ CompRel (CompRel R S) T a d) ↔
      ∃ b, H d ∧ R a b ∧ CompRel S T b d :=
  SquareKit.Internal.ConditionedComposition.in_set R S T H a d
end Relational

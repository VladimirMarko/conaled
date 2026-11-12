import SquareKit.TrackedRecursionClients

/-! Classical serial relations need not have computable realizing transformers. -/
namespace Realizability.TrackedRecursion
open Nat.Partrec (Code)

noncomputable def avoid (p : Computation) : Computation := by
  classical
  exact if p = constant 0 then constant 1 else constant 0

theorem avoid_ne (p : Computation) : avoid p ≠ p := by
  classical
  by_cases h : p = constant 0
  · subst p
    simpa [avoid] using (show constant 1 ≠ constant 0 from
      fun h => Nat.one_ne_zero (constant_injective h))
  · simpa [avoid, h] using Ne.symm h

/-- Inhabited fibers alone are insufficient in the native classical setting. -/
def AvoidRelation (p q : Computation) : Prop := q = avoid p

theorem avoidRelation_serial (p : Computation) : ∃ q, AvoidRelation p q :=
  ⟨avoid p, rfl⟩

theorem avoidRelation_no_fixed : ¬ ∃ p, AvoidRelation p p := by
  rintro ⟨p, hp⟩
  exact avoid_ne p hp.symm

theorem avoidRelation_no_realizer : ¬ ∃ F : Code → Code,
    Computable F ∧ ∀ c, AvoidRelation (represented c) (represented (F c)) := by
  rintro ⟨F, hF, hR⟩
  exact avoidRelation_no_fixed (realized_recursion AvoidRelation F hF hR)

/-- The tempting classical diagonal choice exists but is not a uniform family. -/
theorem avoid_diagonal_not_uniform : ¬ Uniform (fun n => avoid (row n n)) := by
  intro h
  exact avoidRelation_no_fixed (selected_diagonal AvoidRelation _ h (fun _ => rfl))

theorem row_not_surjective : ¬ Function.Surjective row := by
  intro h
  obtain ⟨k, hk⟩ := h (fun n => avoid (row n n))
  exact avoid_ne (row k k) (congrFun hk k).symm

/-- The existing Boolean contrast remains a separate general enumeration obstruction. -/
theorem boolean_enumeration_impossible (e : Nat → Nat → Bool) :
    ¬ Function.Surjective e := SquareKit.DiagonalConstruction.no_boolean_surjection e

end Realizability.TrackedRecursion

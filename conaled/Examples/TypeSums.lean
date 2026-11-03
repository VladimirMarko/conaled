import SquareKit.TypeFamilySum

/-! Experimental dependent Fin consumer of the split Sigma comparison.
The existing source families and certified operations remain unchanged. -/
noncomputable section
namespace Examples.TypeSums
open CategoryTheory SquareKit.Family SquareKit.TypeFamily
open DependentSquares.Example

abbrev secondNative := DependentSquares.app tighten lastIndex
abbrev paired := SquareKit.Family.Sum.pairTerm (display AS) (display BS) (asSection AS lastIndex)
  (SquareKit.TypeFamily.Sum.secondSection AS BS lastIndex secondNative)

theorem pair_native : paired = SquareKit.TypeFamily.Sum.sumSection AS BS
    (DependentSquares.pairTerm lastIndex secondNative) :=
  SquareKit.TypeFamily.Sum.pairing AS BS lastIndex secondNative

theorem first_value (n : Nat) :
    ((SquareKit.Family.Sum.first (display AS) (display BS) paired).val n).2.val = n := by
  have h := (congrArg (SquareKit.Family.Sum.first (display AS) (display BS)) pair_native).trans
    (SquareKit.TypeFamily.Sum.first_projection AS BS (DependentSquares.pairTerm lastIndex secondNative))
  exact congrArg (fun t : Term (display AS) => (t.val n).2.val) h

theorem second_value (n : Nat) :
    ((comparison (display BS) (SquareKit.Family.Sum.first (display AS) (display BS) paired).val)
      ((SquareKit.Family.Sum.second (display AS) (display BS) paired).val n)).2.val = n := by
  have h := SquareKit.Family.Sum.second_comparison (display AS) (display BS) paired
  exact (congrArg (fun f : Nat ⟶ DependentSquares.Ext (DependentSquares.Ext Nat AS) BS =>
    (f n).2.val) h).trans
      (congrArg (fun t : Term (display BS ≫ display AS) => (t.val n).2.val) pair_native)

/-- Successor substitution uses the existing pair_subst through the new comparison. -/
theorem successor_pair :
    SquareKit.TypeFamily.Sum.sumSection (DependentSquares.tySub AS Nat.succ)
      (DependentSquares.tySub BS (DependentSquares.lift Nat.succ))
      (DependentSquares.tmSub (DependentSquares.pairTerm lastIndex secondNative) Nat.succ) =
    SquareKit.Family.Sum.pairTerm (display (DependentSquares.tySub AS Nat.succ))
      (display (DependentSquares.tySub BS (DependentSquares.lift Nat.succ)))
      (asSection _ (DependentSquares.tmSub lastIndex Nat.succ))
      (SquareKit.TypeFamily.Sum.secondSection _ _ (DependentSquares.tmSub lastIndex Nat.succ)
        (DependentSquares.tmSub secondNative Nat.succ)) :=
  SquareKit.TypeFamily.Sum.split_pair_substitution AS BS Nat.succ lastIndex secondNative
end Examples.TypeSums

import Applications.Resources.FoldedPrune
import Examples.WholeListTrimContract
set_option autoImplicit false
set_option warningAsError true
namespace Resources.FoldedPruneContract
open WholeListTrimContract

-- Ordinary single-stage prefix witnesses, independent of a prune runner.
theorem stage (p : List Nat → Bool) (xs out : List Nat)
    (hp : out <+: xs) (ha : WholeListTrim.Accept p out)
    (hm : ∀ i : Fin (xs.length + 1), WholeListTrim.Accept p (xs.take i.val) →
      i.val ≤ out.length) : WholeListTrim.Spec p xs out :=
  WholeListTrim.Spec.of_checks p xs out hp ha hm

example : FoldedPrune.Spec nondecreasing [3,7,8,2,3] [3,7,8] := by
  apply FoldedPrune.Spec.cons (old := [7,8])
  · apply FoldedPrune.Spec.cons (old := [8])
    · apply FoldedPrune.Spec.cons (old := [2,3])
      · apply FoldedPrune.Spec.cons (old := [3])
        · exact .cons .nil (stage _ _ _ (by decide) (by unfold WholeListTrim.Accept; decide)
            (by unfold WholeListTrim.Accept; decide))
        · exact stage _ _ _ (by decide) (by unfold WholeListTrim.Accept; decide)
            (by unfold WholeListTrim.Accept; decide)
      · exact stage _ _ _ (by decide) (by unfold WholeListTrim.Accept; decide)
          (by unfold WholeListTrim.Accept; decide)
    · exact stage _ _ _ (by decide) (by unfold WholeListTrim.Accept; decide)
        (by unfold WholeListTrim.Accept; decide)
  · exact stage _ _ _ (by decide) (by unfold WholeListTrim.Accept; decide)
      (by unfold WholeListTrim.Accept; decide)

example : (2+3+12+3+4 : Nat) = 24 ∧ 3+6+9+6+9 = 33 ∧ 24+9 = 33 ∧ 24+7 = 31 := by decide
example : (2+3+9 : Nat) = 14 ∧ 14+5 = 19 := by decide
example : (4+9 : Nat) = 4+9 := rfl
example : ¬ FoldedPrune.TailClosed onlyOneTwo := by
  intro h
  have hn : ¬ WholeListTrim.Accept onlyOneTwo [2] := by unfold WholeListTrim.Accept; decide
  exact hn (h 1 [2] (by decide))
end Resources.FoldedPruneContract

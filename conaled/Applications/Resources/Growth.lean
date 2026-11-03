import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic

/-! Natural measured counts use the standard asymptotic interface after real casting. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources

/-- An explicit natural bound gives the same eventual bound on real-cast counts. -/
theorem isBigO_of_nat_bound (f g : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * g n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(C : ℝ), Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (bound n hn)

end Resources

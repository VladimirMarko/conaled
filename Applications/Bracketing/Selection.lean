import Applications.Bracketing.Basic
import Applications.Optimization.Thinning

/-! The shared total selector realizes the nonempty source selector exactly.
The source first-minimum contract includes strict inequality before the chosen
occurrence, which is stronger than merely retaining a minimal head. -/
namespace Bracketing
variable {α : Type}

theorem argmin_eq_sourceMinWith (score : α → Nat) (xs : List α) (hn : xs ≠ []) :
    Optimization.Thinning.argmin score xs = some (sourceMinWith score xs hn) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [Optimization.Thinning.argmin, ih (by simp)]
      rfl

theorem argmin_firstMinimum (score : α → Nat) (xs : List α) (x : α)
    (hx : Optimization.Thinning.argmin score xs = some x) : FirstMinimum score xs x := by
  have hn : xs ≠ [] := by
    intro he
    subst xs
    contradiction
  rw [argmin_eq_sourceMinWith score xs hn] at hx
  exact Option.some.inj hx ▸ sourceMinWith_first score xs hn

end Bracketing

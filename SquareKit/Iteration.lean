/-! A first-hit iteration trace: every preceding state fails the stopping test. -/
set_option autoImplicit false
set_option warningAsError true
namespace Iteration
universe u
variable {α : Type u}
inductive UntilSpec (p : α → Bool) (f : α → α) : α → α → Prop
  | stop {x : α} : p x = true → UntilSpec p f x x
  | step {x y : α} : p x = false → UntilSpec p f (f x) y → UntilSpec p f x y

theorem UntilSpec.stopping {p : α → Bool} {f : α → α} {x y : α}
    (h : UntilSpec p f x y) : p y = true := by
  induction h with
  | stop hp => exact hp
  | step _ _ ih => exact ih
end Iteration

import Examples.WeakMachine
import SquareKit.WeakMachine.Canonicity
import SquareKit.WeakMachine.OpaqueControl

namespace Examples.WeakCanonicity
open SquareKit.HigherOrderComparison (Ty empty)
open SquareKit.WeakHigherOrder
open SquareKit.WeakMachine

/-- Duplicate a function argument, using nested beta reductions. -/
def twice : Term [] .ground :=
  .app (.lam (.app (.var .here) (.app (.var .here) (.lit 7))))
    (.lam (.var .here) : Term [] (.arr .ground .ground))

theorem twice_admitted : NoOmega twice := by trivial

/-- Uses structural coverage, existing recovery, and operational adequacy. -/
theorem twice_returns : SquareKit.WeakMachine.Returns twice 7 := admitted_returns twice twice_admitted

example : ∃ n, SquareKit.WeakMachine.Returns twice n ∧
    (∀ m, SquareKit.WeakMachine.Returns twice m → m = n) ∧
    ∃ bound, ∀ fuel, bound ≤ fuel → execute fuel twice = .terminal (.lit n) .lit :=
  canonicity twice twice_admitted

example : execute 0 twice = .timeout twice := rfl
example : Examples.WeakMachine.numeral (execute 2 twice) = none := rfl
example : execute 3 twice = .terminal (.lit 7) .lit := rfl
example : execute 0 (.lit 7) = .terminal (.lit 7) .lit := rfl

example : ¬ NoOmega (.omega : Term [] .ground) := id

def ignoredOmega : Term [] .ground :=
  .app (.lam (.lit 0 : Term [.arr .ground .ground] .ground))
    (.lam (.omega : Term [.ground] .ground))

theorem ignoredOmega_returns : SquareKit.WeakMachine.Returns ignoredOmega 0 :=
  .cons (.beta .lam) .refl

theorem ignoredOmega_rejected : ¬ NoOmega ignoredOmega := fun h => h.2

example : execute 1 ignoredOmega = .terminal (.lit 0) .lit := rfl

/-- Admission is sufficient, not necessary even at closed ground type. -/
theorem admission_conservative : ∃ t : Term [] .ground,
    SquareKit.WeakMachine.Returns t 0 ∧ ¬ NoOmega t :=
  ⟨ignoredOmega, ignoredOmega_returns, ignoredOmega_rejected⟩

example : back (embed (.lit true 7 : SquareKit.HigherOrderComparison.Term [] .ground))
    (embed_admitted _) ≠ .lit true 7 := by intro h; cases h

example : embed (.lit true 7 : SquareKit.HigherOrderComparison.Term [] .ground) =
    embed (.lit false 7) := rfl

/-- A substitution with an unforced partial body is not structurally admitted. -/
example : ¬ AdmittedSub (singleSub (loopingFunction : Term [] (.arr .ground .ground))) :=
  fun h => h .here

example : NoOmega (subst (singleSub (identity : Term [] (.arr .ground .ground)))
    (.app (.var .here) (.lit 7))) :=
  NoOmega.subst (by trivial) (by intro a v; cases v with
    | here => trivial
    | there v => exact nomatch v)

end Examples.WeakCanonicity

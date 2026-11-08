import SquareKit.WeakMachine.Adequacy

namespace Examples.WeakMachine
open SquareKit.HigherOrderComparison (Ty Ctx Var Env extend empty)
open SquareKit.WeakHigherOrder
open SquareKit.WeakMachine

/-- The executable observation distinguishes terminal naturals from timeout;
none remains inconclusive, not a divergence verdict. -/
def numeral : Result .ground → Option Nat
  | .terminal t _ => match t with | .lit n => some n | _ => none
  | .timeout _ => none

def isTerminal : Result a → Bool
  | .terminal _ _ => true
  | .timeout _ => false

example : next (zero : Term [] .ground) = none := rfl
example : next (redex : Term [] .ground) = some zero := rfl
example : numeral (execute 0 zero) = some 0 := rfl
example : numeral (execute 0 redex) = none := rfl
example : execute 0 redex = .timeout redex := rfl
example : numeral (execute 1 redex) = some 0 := rfl
example : numeral (execute 20 (.omega : Term [] .ground)) = none := rfl

theorem omega_infinite : Infinite (.omega : Term [] a) := self_infinite .loop

theorem redex_returns : SquareKit.WeakMachine.Returns redex 0 :=
  .cons (.beta .lit) .refl

theorem redex_same_returns (n : Nat) :
    SquareKit.WeakMachine.Returns redex n ↔ SquareKit.WeakMachine.Returns zero n :=
  context_returns .hole redex_equal n

theorem timeout_inconclusive : numeral (execute 0 redex) = numeral (execute 0 (.omega)) ∧
    SquareKit.WeakMachine.Returns redex 0 ∧ Infinite (.omega : Term [] .ground) :=
  ⟨rfl,redex_returns,omega_infinite⟩

theorem identity_related : Related (.arr a a) (identity : Term [] (.arr a a))
    (fun v => .done 0 v) := by
  refine ⟨.var .here,rfl,?_⟩
  intro x v hx
  exact behavior_now hx

/-- Generic related-input application, including higher-order arguments. -/
theorem identity_application (hx : Related a x v) :
    Behavior (Related a) (.app identity x) (.done 1 v) :=
  related_application identity_related hx

example : Behavior (Related (.arr .ground .ground)) (.app identity identity)
    (.done 1 (fun n => .done 0 n)) := identity_application identity_related

example : numeral (execute 2 (client identity)) = some 0 := rfl
example : isTerminal (execute 0 loopingFunction) = true := rfl

theorem invoked_loop : Infinite (client loopingFunction) :=
  prefix_infinite (.cons (.beta .lam) (.cons (.beta .lit) .refl)) omega_infinite

def discardLoop : Term [] .ground := .app (.lam (.lit 0 : Term [.ground] .ground)) .omega

theorem discard_infinite : Infinite discardLoop := self_infinite (.right .lam .loop)
example : numeral (execute 10 discardLoop) = none := rfl

def functionFirst : Term [] .ground := .app (.app identity identity) redex
example : next functionFirst = some (.app identity redex) := rfl
example : execute 1 functionFirst = .timeout (.app identity redex) := rfl

def argumentBeforeBody : Term [] .ground := .app loopingFunction redex
example : next argumentBeforeBody = some (.app loopingFunction zero) := rfl

example : numeral (execute 3 (client (subst closeSeven openRedex))) = some 7 := rfl
example : numeral (execute 2 (client (subst closeSeven openIdentity))) = some 7 := rfl

theorem bound_operational (n : Nat) :
    SquareKit.WeakMachine.Returns (client (subst closeSeven openRedex)) n ↔
      SquareKit.WeakMachine.Returns (client (subst closeSeven openIdentity)) n :=
  context_returns invokeContext bound_functions_equal n

/-- The pre-existing total fragment remains available through its embedding. -/
theorem recovered (t : SquareKit.HigherOrderComparison.Term [] .ground) :
    SquareKit.WeakMachine.Returns (embed t) (SquareKit.HigherOrderComparison.denote t empty) :=
  (return_denotation _ _).mpr (recovery_meaning t)

end Examples.WeakMachine

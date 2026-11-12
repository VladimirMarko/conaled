import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Int.Basic

/-! Direct state-package conjugation retained beside the cubical transport
consumer. Its connection to universe-path transport is a separate obligation. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalStateTransport
universe u v

structure StatePackage (A : Type u) where
  initial : A
  step : A → A
  invariant : A → Prop
  initial_valid : invariant initial
  preserves : ∀ a, invariant a → invariant (step a)

/-- Change every carrier-dependent component, including preservation evidence. -/
def StatePackage.conjugate {A : Type u} {B : Type v} (e : A ≃ B)
    (s : StatePackage A) : StatePackage B where
  initial := e s.initial
  step b := e (s.step (e.symm b))
  invariant b := s.invariant (e.symm b)
  initial_valid := by simpa using s.initial_valid
  preserves b h := by simpa using s.preserves (e.symm b) h

def successor : Int ≃ Int where
  toFun n := n + 1
  invFun n := n - 1
  left_inv n := by dsimp; omega
  right_inv n := by dsimp; omega

def evenPackage : StatePackage Int where
  initial := 0
  step n := n + 2
  invariant n := n % 2 = 0
  initial_valid := rfl
  preserves n h := by omega

def oddPackage : StatePackage Int := evenPackage.conjugate successor

theorem odd_initial : oddPackage.initial = 1 := rfl

theorem odd_step (n : Int) : oddPackage.step n = n + 2 := by
  change (n - 1 + 2) + 1 = n + 2
  omega

theorem odd_invariant (n : Int) : oddPackage.invariant n ↔ n % 2 = 1 := by
  change (n - 1) % 2 = 0 ↔ n % 2 = 1
  omega

theorem successor_observation : successor 3 = 4 := rfl

theorem predecessor_observation : successor.symm 3 = 2 := rfl

end Examples.CubicalStateTransport

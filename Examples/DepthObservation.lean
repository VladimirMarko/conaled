import SquareKit.FiniteObservation
import Mathlib.Tactic

/-! A non-parser observation client: bounded commands increment a retained
counter. A redundant flag is hidden, but the complete counter is observable. -/
namespace Examples.DepthObservation
open SquareKit.IndexedCompositional
abbrev behavior : Behavior Nat where
  Output _ := Nat
  Request n := match n with | 0 => PEmpty | _+1 => Nat
  next n _ := n-1

def counter : behavior.Coalgebra (fun _ => Nat)
  | 0, s => (s, fun c => nomatch c)
  | _+1, s => (s, fun c => s+c)

def flagged : behavior.Coalgebra (fun _ => Nat × Bool)
  | 0, s => (s.1, fun c => nomatch c)
  | _+1, s => (s.1, fun c => (s.1+c, !s.2))

def decode : ∀ _n : Nat, (Nat × Bool) → Nat := fun _ s => s.1

theorem decodes : behavior.Morphism flagged counter decode where
  output n s := by cases n <;> rfl
  next n s c := by cases n with
    | zero => exact nomatch c
    | succ => rfl

def commands : {n : Nat} → (cs : List Nat) → cs.length ≤ n → behavior.Observation n Nat
  | n, [], _ => ⟨n, .stop, id⟩
  | 0, _::_, h => False.elim (Nat.not_succ_le_zero _ h)
  | n+1, c::cs, h =>
    let rest := commands (n := n) cs (Nat.le_of_succ_le_succ h)
    ⟨rest.endpoint, .step c rest.path, rest.decode⟩

theorem read_counter {n} (cs : List Nat) (h : cs.length ≤ n) (s : Nat) :
    (commands cs h).read counter s = s + cs.sum := by
  induction cs generalizing n s with
  | nil => cases n <;> rfl
  | cons c cs ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ n =>
      change (commands cs _).read counter (s+c) = _
      rw [ih]
      simp [Nat.add_assoc]

theorem read_flagged {n} (cs : List Nat) (h : cs.length ≤ n) (s : Nat × Bool) :
    (commands cs h).read flagged s = s.1 + cs.sum := by
  rw [← (commands cs h).read_morphism flagged counter decode decodes s]
  exact read_counter cs h s.1

example : (commands (n := 4) [2,3,1] (by decide)).read flagged (7,true) = 13 := by
  rw [read_flagged]
  rfl

end Examples.DepthObservation

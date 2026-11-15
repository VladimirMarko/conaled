import Mathlib.Tactic

/-! Independent mathematical specification for the prospective #357 trial.
No author-route construction or compiler proof is included here. -/
namespace Examples.IncrementalDependentTrialSpec

inductive Op where
  | successor
  | double
  deriving DecidableEq, Repr

def step : Op → Nat → Nat
  | .successor, n => n + 1
  | .double, n => 2 * n

def run (ops : List Op) (n : Nat) : Nat := ops.foldl (fun x op => step op x) n

abbrev Packet := (k : Nat) × Fin (k + 2)

def selected (ops : List Op) (n : Nat) : Packet :=
  ⟨run ops n + 1, ⟨run ops n + 1, by omega⟩⟩

def sigma (n : Nat) := n + 1
def tau (n : Nat) := 2 * n

def demo : List Op := [.double, .successor, .successor, .double, .successor]
def demoAnswer : Packet := ⟨18, ⟨18, by decide⟩⟩
def substitutedAnswer : Packet := ⟨34, ⟨34, by decide⟩⟩
def wrongAnswer : Packet := ⟨34, ⟨0, by decide⟩⟩

end Examples.IncrementalDependentTrialSpec

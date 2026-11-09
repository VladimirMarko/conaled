import Applications.Optimization.Choice.Evidence
import Applications.Resources.Prepared

namespace Examples.RealizationChoice
open Optimization.Choice

def context : Context := ⟨"synthetic-v1", "test", "allowed-results", "root", "one-total", [], ["a","b"]⟩
def identify : Bool → String | false => "a" | true => "b"
def fixed : Bool → Nat | false => 0 | true => 1

def observations : Except String Epoch := do
  let a ← (Epoch.start context 1).record context ⟨"a",0,20,true⟩
  a.record context ⟨"b",0,10,true⟩

def trained := observations.toOption
example : choose [false,true] (fun _ => True) identify context 1 fixed none = some false := by decide
example : choose [false,true] (fun _ => True) identify context 1 fixed trained = some true := by decide
example : choose [false,true] (fun c => c = false) identify context 1 fixed trained = some false := by decide
example : choose [false,true] (fun _ => False) identify context 1 fixed trained = none := by decide
example : choose [false,true] (fun _ => True) identify {context with target := "other"} 1 fixed trained = some false := by decide

/-- Distinct observable answers satisfy an allowed-outcome contract. The shared
selection law does not silently demand equality between them. -/
def answer (candidate : Bool) : Nat := if candidate then 12 else 10

theorem allowed {evidence : Option Epoch} {c : Bool}
    (h : choose [false,true] (fun _ => True) identify context 1 fixed evidence = some c) :
    10 ≤ answer c ∧ answer c ≤ 12 :=
  choose_contract (fun c => 10 ≤ answer c ∧ answer c ≤ 12)
    (by intro c _ _; cases c <;> decide) h

example : answer false ≠ answer true := by decide
example : 10 ≤ answer true ∧ answer true ≤ 12 := allowed (by decide :
    choose [false,true] (fun _ => True) identify context 1 fixed trained = some true)

/-- Mapping into a surrounding operation retains the first tied witness. -/
example : select ([1,2].map (fun n : Nat => n+3)) (fun _ => True) (fun _ => (0 : Nat)) = some 4 := by
  rw [select_map]
  rfl

end Examples.RealizationChoice

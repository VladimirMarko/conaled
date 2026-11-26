import SquareKit.RelationalSemanticBoundary
import Mathlib.Tactic

namespace Relational.SemanticBoundary.Examples
open Squares.SemanticBoundary

inductive Poss where
  | left | both | right | dead
  deriving DecidableEq

def Accepts : Poss → Bool → Prop
  | .left, b => b = false
  | .both, _ => True
  | .right, b => b = true
  | .dead, _ => False

def direct : RelRep := ⟨Poss, Bool, Accepts⟩
def redundant : RelRep := ⟨Poss × Bool, Bool, fun r b => Accepts r.1 b⟩

def strip : RelSquare redundant direct := ⟨Prod.fst, id, id⟩
def decorate : RelSquare direct redundant := ⟨fun p => (p, true), id, id⟩

def swap : Poss → Poss
  | .left => .right
  | .right => .left
  | p => p

def flip : RelSquare redundant redundant where
  impl r := (swap r.1, !r.2)
  spec := Bool.not
  preserves := by rintro ⟨p, f⟩ b h; cases p <;> cases b <;> simp_all [redundant, Accepts, swap]

/-- A second local operation may hide possibilities while retaining the selected witness. -/
def widen : RelSquare redundant redundant where
  impl r := (.both, !r.2)
  spec := id
  preserves _ := trivial

def selected (p : Poss) (b flag : Bool) (h : Accepts p b) : Selected redundant :=
  pack (⟨((p, flag), b), h⟩ : (witness redundant).R)

theorem selected_client (p : Poss) (b flag : Bool) (h : Accepts p b) :
    meaning (selectedMap (Relational.compose widen flip) (selected p b flag h)) = !b := by
  rw [selectedMap_meaning]
  rfl

theorem replacement (x : Selected redundant) :
    selectedMap decorate (selectedMap strip x) = x := by
  induction x using Quotient.inductionOn with
  | h x => exact Quotient.sound rfl

/-- Arbitrary pure selected clients cannot recover the redundant flag. -/
theorem selected_no_flag : ¬ ∃ c : Selected redundant → Bool,
    ∀ flag, c (selected .both false flag trivial) = flag := by
  rintro ⟨c, h⟩
  have same : selected .both false false trivial = selected .both false true trivial :=
    Quotient.sound rfl
  have := congrArg c same
  rw [h, h] at this
  cases this

/-- Ambiguous alternatives remain distinct when selection is observable. -/
theorem selections_distinct : selected .both false false trivial ≠ selected .both true false trivial := by
  intro h
  have := congrArg meaning h
  change false = true at this
  cases this

def Shares (p q : Poss) := ∃ b, Accepts p b ∧ Accepts q b

example : Shares .left .both ∧ Shares .both .right ∧ ¬ Shares .left .right := by
  refine ⟨⟨false, rfl, trivial⟩, ⟨true, trivial, rfl⟩, ?_⟩
  rintro ⟨b, hb, hc⟩
  cases b <;> simp_all [Accepts]

/-- No single decoder preserves every possible meaning of an ambiguous input. -/
example : ¬ ∃ decode : Poss → Bool, ∀ p b, Accepts p b → decode p = b := by
  rintro ⟨d, h⟩
  have := (h .both false trivial).symm.trans (h .both true trivial)
  cases this

example : ¬ ∃ b, Accepts .dead b := by simp [Accepts]

/-- Forward simulation alone cannot justify descent to possible-set observations. -/
def fixedFalse : RelRep := ⟨Bool, Bool, fun _ b => b = false⟩
def forwardOnly : RelSquare fixedFalse direct where
  impl := fun (b : Bool) => if b then .both else .left
  spec := id
  preserves := by intro r s h; cases r <;> simp_all [direct, fixedFalse, Accepts]

theorem no_possibility_descent : ¬ ∃ f : Handle fixedFalse → Handle direct,
    ∀ r, f (pack r) = pack (forwardOnly.impl r) := by
  rintro ⟨f, h⟩
  have hs : (pack false : Handle fixedFalse) = pack true := Quotient.sound rfl
  have he := congrArg f hs
  rw [h false, h true] at he
  have hm := congrArg meaning he
  change ({b | Accepts .left b} : Set Bool) = {b | Accepts .both b} at hm
  have ht : true ∈ ({b | Accepts .both b} : Set Bool) := trivial
  have hf : true ∈ ({b | Accepts .left b} : Set Bool) := hm ▸ ht
  cases hf

end Relational.SemanticBoundary.Examples

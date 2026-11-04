import Mathlib.Data.List.Basic

/-! Concrete inputs for the #293 author trial. No generalized requirement interface. -/
namespace ProofRequirementTrial

namespace Source

/-- Concrete source argument for the equational task. -/
theorem reverseBlocks (_ambient : ∀ t : List Nat, t ++ [] = t)
    (x y z : List Nat) :
    (x ++ (y ++ z)).reverse = (z.reverse ++ y.reverse) ++ x.reverse := by
  calc
    (x ++ (y ++ z)).reverse =
        ((x.reverse.reverse) ++ (y ++ z)).reverse :=
      congrArg (fun t => (t ++ (y ++ z)).reverse) (List.reverse_reverse x).symm
    _ = (x ++ (y ++ z)).reverse :=
      congrArg (fun t => (t ++ (y ++ z)).reverse) (List.reverse_reverse x)
    _ = (y ++ z).reverse ++ x.reverse := List.reverse_append
    _ = (z.reverse ++ y.reverse) ++ x.reverse :=
      congrArg (fun t => t ++ x.reverse) List.reverse_append

/-- A selected list, with only its length constrained by the proof component. -/
def selected (x : List Nat) : { y : List Nat // y.length = (x ++ []).length } :=
  ⟨x, congrArg List.length (List.append_nil x).symm⟩

theorem selected_value (x : List Nat) : (selected x).val = x := rfl

end Source

namespace Targets

def listOp (x y : List Nat) : List Nat := x ++ y
def listFlip (x : List Nat) : List Nat := x.reverse
def listUnit : List Nat := []
def listObserve (x : List Nat) : Nat := x.length

def boolOp (x y : Bool) : Bool := Bool.xor x y
def boolFlip (x : Bool) : Bool := x
def boolUnit : Bool := false
def boolObserve (x : Bool) : Bool := x

/-- Operation supplied for a negative target check. -/
def badOp (x _y : Bool) : Bool := x

end Targets
end ProofRequirementTrial

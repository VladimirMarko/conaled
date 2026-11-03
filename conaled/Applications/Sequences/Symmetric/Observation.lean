import Applications.Sequences.Symmetric.Finite
import SquareKit.Relations

/-! Valid raw pairs interpreted as ordinary sequences. Consumers paste existing
relational squares; they do not normalize the represented data between steps. -/
namespace Sequences.Symmetric
universe u
variable {α : Type u}
open Relational

def representation (α : Type u) : RelRep where
  R := SymList α
  S := List α
  Rel s xs := Inv s ∧ fromSL s = xs

def snocSquare (x : α) : RelSquare (representation α) (representation α) where
  impl := snocSL x
  spec := fun (xs : List α) => xs ++ [x]
  preserves := fun ⟨h, he⟩ => ⟨inv_snocSL _ _, (fromSL_snocSL _ _ h).trans (congrArg (· ++ [x]) he)⟩

def tailSquare : RelSquare (representation α) (representation α) where
  impl := tailSL
  spec := List.tail
  preserves := fun ⟨h, he⟩ => ⟨inv_tailSL _ h, (fromSL_tailSL _ h).trans (congrArg List.tail he)⟩

def endpointRepresentation (α : Type u) : RelRep where
  R := Option α
  S := Option α
  Rel := Eq

def headSquare : RelSquare (representation α) (endpointRepresentation α) where
  impl := headSL
  spec := List.head?
  preserves := fun ⟨h, he⟩ => (headSL_eq_head _ h).trans (congrArg List.head? he)

/-- Append an endpoint, remove the first element, and observe the next head. -/
def editHead (x : α) : RelSquare (representation α) (endpointRepresentation α) :=
  compose headSquare (compose tailSquare (snocSquare x))

theorem editHead_correct (x : α) (s : SymList α) (h : Inv s) :
    (editHead x).impl s = ((fromSL s ++ [x]).tail).head? :=
  (show _ = _ from (editHead x).preserves ⟨h, rfl⟩)

def prefixRepresentation (α : Type u) : RelRep where
  R := SymList (SymList α)
  S := List (List α)
  Rel s xss := Inv s ∧ (∀ t ∈ fromSL s, Inv t) ∧ (fromSL s).map fromSL = xss

def prefixesSquare : RelSquare (representation α) (prefixRepresentation α) where
  impl := initsSL
  spec := List.inits
  preserves := fun ⟨h, he⟩ => ⟨inv_initsSL _, initsSL_members_valid _ h,
    (fromSL_initsSL _ h).trans (congrArg List.inits he)⟩

/-- ULift respects the existing same-universe relational interface. -/
def lengthsRepresentation : RelRep.{u} where
  R := ULift.{u} (List Nat)
  S := ULift.{u} (List Nat)
  Rel := Eq

def lengthsSquare : RelSquare (prefixRepresentation α) lengthsRepresentation where
  impl s := ⟨(fromSL s).map lengthSL⟩
  spec xss := ⟨xss.map List.length⟩
  preserves := by
    rintro s xss ⟨_, _, he⟩
    subst xss
    change ULift.up _ = ULift.up _
    congr 1
    simp only [List.map_map, Function.comp_def, length_fromSL]

def prefixLengths : RelSquare (representation α) lengthsRepresentation :=
  compose lengthsSquare prefixesSquare

theorem lengths_inits (xs : List α) : xs.inits.map List.length = List.range (xs.length + 1) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_inits, List.length_take, List.getElem_range]
    simp only [List.length_map, List.length_inits] at hi
    omega

theorem prefixLengths_correct (s : SymList α) (h : Inv s) :
    ((prefixLengths (α := α)).impl s).down = List.range (lengthSL s + 1) := by
  have he := congrArg ULift.down ((prefixLengths (α := α)).preserves ⟨h, rfl⟩)
  change ((prefixLengths (α := α)).impl s).down = (fromSL s).inits.map List.length at he
  exact he.trans (by rw [lengths_inits, length_fromSL])

end Sequences.Symmetric

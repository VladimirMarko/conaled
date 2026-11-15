import SquareKit.Relations
import SquareKit.SemanticBoundary
import Mathlib.Data.Set.Basic

/-! Two distinct boundaries for relational meanings: sets of possibilities and
selected relation witnesses. Neither chooses a decoder into a single meaning. -/
namespace Relational.SemanticBoundary
open Squares
universe u

/-- Retain the entire fiber, including empty and many-valued fibers. -/
def possibilities (A : RelRep.{u}) : Rep.{u} where
  R := A.R
  S := Set A.S
  decode r := {s | A.Rel r s}

abbrev Handle (A : RelRep.{u}) := Squares.SemanticBoundary.Handle (possibilities A)
abbrev Selected (A : RelRep.{u}) := Squares.SemanticBoundary.Handle (witness A)

/-- Every pure client respects equality of the full possible-meaning sets. -/
theorem client_invariant {A : RelRep.{u}} {T : Sort v} (client : Handle A → T)
    {r t : A.R} (h : ∀ s, A.Rel r s ↔ A.Rel t s) :
    client (Squares.SemanticBoundary.pack r) = client (Squares.SemanticBoundary.pack t) :=
  Squares.SemanticBoundary.client_invariant client (Set.ext h)

/-- Ordinary forward relational preservation suffices on selected witnesses. -/
def selectedMap {A B : RelRep.{u}} (f : RelSquare A B) : Selected A → Selected B :=
  Squares.SemanticBoundary.lift (witnessSquare f)

theorem selectedMap_meaning {A B : RelRep.{u}} (f : RelSquare A B) (x : Selected A) :
    Squares.SemanticBoundary.meaning (selectedMap f x) =
      f.spec (Squares.SemanticBoundary.meaning x) :=
  Squares.SemanticBoundary.lift_meaning _ _

theorem selectedMap_compose {A B C : RelRep.{u}} (g : RelSquare B C)
    (f : RelSquare A B) (x : Selected A) :
    selectedMap (Relational.compose g f) x = selectedMap g (selectedMap f x) := by
  unfold selectedMap
  rw [witness_compose]
  exact Squares.SemanticBoundary.lift_compose _ _ _

/-- Exact possible-set operations supply a stronger contract than forward simulation. -/
abbrev PossibilityMap (A B : RelRep.{u}) := Square (possibilities A) (possibilities B)

/-- Graph interpretations recover precisely the existing exact equivalence. -/
theorem graph_fibers_iff (A : Rep.{u}) (x y : A.R) :
    (possibilities (graph A)).decode x = (possibilities (graph A)).decode y ↔
      A.decode x = A.decode y := by
  change ({s | A.decode x = s} : Set A.S) = {s | A.decode y = s} ↔ _
  constructor
  · intro h
    have hmem : A.decode x ∈ ({s | A.decode y = s} : Set A.S) :=
      h ▸ (show A.decode x ∈ ({s | A.decode x = s} : Set A.S) from rfl)
    exact hmem.symm
  · intro h
    ext s
    change (A.decode x = s) ↔ (A.decode y = s)
    rw [h]

/-- No new quotient is forced on an exact interpretation. -/
def graphEquiv (A : Rep.{u}) : Handle (graph A) ≃ Squares.SemanticBoundary.Handle A where
  toFun := Quotient.map id (fun {x y} h => (graph_fibers_iff A x y).mp h)
  invFun := Quotient.map id (fun {x y} h => (graph_fibers_iff A x y).mpr h)
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv x := Quotient.inductionOn x (fun _ => rfl)

end Relational.SemanticBoundary

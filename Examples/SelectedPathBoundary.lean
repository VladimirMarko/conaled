import SquareKit.SelectedPathBoundary
import Examples.GroupoidRoutes
import Examples.TwoFamilySelectedPathObservation

/-! Bounded first-identity clients and retention of an existing selected two-cell.
These reuse the actual groupoid transport and two-family source witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.SelectedPathBoundary
open CategoryTheory Squares Squares.SemanticBoundary
open SquareKit.GroupoidTransport SquareKit.GroupoidTransport.SelectedBoundary
open Examples.GroupoidTransport Examples.GroupoidRoutes

/-- Independently chosen generator and value: the required transport sends 0 to 1. -/
def input (n : ZMod 4) (b : ZMod 2) (flag : Bool) :
    Handle (flagged (Input binary point point)) := pack ((label n, b), flag)

theorem chosen_transport :
    meaning (lift (transport binary point point) (input 1 0 false)) = (label 1, 1) := by
  rw [lift_meaning]
  exact Prod.ext rfl generator_zero

/-- Two nonidentity routes retain both path label and selected dependent value. -/
theorem two_routes (n : ZMod 4) (b : ZMod 2) (flag : Bool) :
    meaning (lift (routeInput binary flipRoute point point)
      (lift (routeInput binary flipRoute point point) (input n b flag))) = (label n, b) := by
  calc
    _ = meaning (lift (routeInput binary doubleRoute point point) (input n b flag)) :=
      congrArg (fun h : Handle (flagged (Input binary point point)) => meaning h)
        (route_compose binary flipRoute flipRoute point point (input n b flag)).symm
    _ = _ := by
      rw [lift_meaning]
      exact Prod.ext (double_label n) (double_fiber b)

theorem transported_routes (n : ZMod 4) (b : ZMod 2) (flag : Bool) :
    lift (routeOutput binary doubleRoute point point)
      (lift (transport binary point point) (input n b flag)) =
    lift (transport binary point point)
      (lift (routeInput binary doubleRoute point point) (input n b flag)) :=
  route_transport binary doubleRoute point point _

/-- Two base substitutions retain the chosen path, not just its endpoints. -/
theorem two_substitutions (n : ZMod 4) :
    ((doubleRoute.reindex reverseBase).reindex reverseBase).base.map (label n) = label n := by
  change doubleRoute.base.map (label (-(-n))) = label n
  rw [neg_neg, double_label]

theorem dependent_substitution (n : ZMod 4) (b : ZMod 2) :
    ((doubleRoute.reindex reverseBase).reindex reverseBase).fiber.app point
      ((reverseBase ⋙ reverseBase ⋙ binary).map (label n) b) =
    binary.map (((doubleRoute.reindex reverseBase).reindex reverseBase).base.map (label n))
      (doubleRoute.fiber.app point b) :=
  substituted_transport (reverseBase ⋙ binary) (doubleRoute.reindex reverseBase) reverseBase _ _

/-- All pure clients ignore only the representation flag. -/
theorem flag_invariant {T : Sort u} (c : Handle (flagged (Input binary point point)) → T)
    (n : ZMod 4) (b : ZMod 2) : c (input n b false) = c (input n b true) :=
  client_invariant c rfl

/-- Equal endpoints cannot recover path-dependent behavior. -/
theorem no_endpoint_only_transport : ¬ ∃ observe : Unit → ZMod 2,
    ∀ n : ZMod 4, observe () = binary.map (label n) 0 := by
  rintro ⟨f, h⟩
  have h0 := h 0
  have h1 := h 1
  rw [generator_zero] at h1
  have hzero : binary.map (label 0) (0 : ZMod 2) = 0 := rfl
  rw [hzero] at h0
  exact (by decide : (0 : ZMod 2) ≠ 1) (h0.symm.trans h1)

/-- Even ineffective transport does not identify distinct selected paths. -/
theorem selected_paths_distinct : input 2 0 false ≠ input 0 0 false := by
  intro h
  have hp := congrArg (fun x : Handle (flagged (Input binary point point)) => (meaning x).1) h
  exact (by decide : (2 : ZMod 4) ≠ 0) (labels_injective hp)

example (n : ZMod 4) (b : ZMod 2) :
    lift (addFlag (Input binary point point))
      (lift (removeFlag (Input binary point point)) (input n b false)) = input n b false :=
  replacement _

end Examples.SelectedPathBoundary

namespace Examples.SelectedTwoCellBoundary
open CategoryTheory Bicategory Squares Squares.SemanticBoundary
open SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.GroupoidTransport.SelectedBoundary
open Examples.TwoFamilyFrozenPoint Examples.FrozenMemoStages Examples.TwoFamilyModelData

/-- Preserve the full normalized selected two-cell object, not merely Nonempty. -/
abbrev Cell := LocallyDiscrete (Discrete (Multiplicative ℤ))

def chosen (k : ℤ) : Cell := ⟨⟨Multiplicative.ofAdd k⟩⟩
def handle (k : ℤ) (flag : Bool) : Handle (flagged Cell) := pack (chosen k, flag)

theorem meaning_retained (k : ℤ) (flag : Bool) : meaning (handle k flag) = chosen k := rfl

/-- The existing two-weakening theorem connects the original source witness to this handle. -/
theorem source_witness_retained (k : ℤ) (flag : Bool) :
    HEq (sectionValue
      (inputPaths (structuralModel integerContext integerContext) emptyA emptyB).toParallel.identity
      (inputPaths (structuralModel integerContext integerContext) emptyA emptyB).h (assignedPoint k))
      (meaning (handle k flag)) := by
  exact normalizedPathOperands_retained k

example : handle 0 false ≠ handle 1 false := by
  intro h
  have hi := congrArg (fun h : Handle (flagged Cell) => (meaning h).as.as.toAdd) h
  change (0 : ℤ) = 1 at hi
  omega

end Examples.SelectedTwoCellBoundary

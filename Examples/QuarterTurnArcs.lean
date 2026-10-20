import SquareKit.SmoothQuotientTransport

/-! The disk's infinitesimal arcs, actual quotient arrows, and classical rotation. -/
noncomputable section
open CategoryTheory Opposite
open scoped Manifold
namespace Examples.QuarterTurnArcs
open SquareKit SquareKit.SmoothQuarterTurnArcs SquareKit.SmoothQuarterTurnQuotient
open Orbifolds.QuarterTurn

/-- Arbitrary sheaf parameters see the open base point and two free velocities. -/
def diskArcComparison (X : Sheaf SmoothOpenSite.topology Type) :
    (SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ diskSheaf) ≃
      (X ⟶ SheafRelation.product diskSheaf (SmoothOpenSite.scalarPower 2)) :=
  SmoothOpenArcs.parameterCoefficients diskDomain X

/-- This finite calculation uses the same coefficient action as the all-stage
sheaf comparison, rather than a second rotation formula. -/
theorem quarter_turn_coefficients (v : Fin 2 → ℝ) :
    coefficientAction quarterTurn v = ![-v 1, v 0] := by
  funext i
  fin_cases i <;> simp [coefficientAction, quarterTurn]

theorem quarter_turn_derivative (z : Disk) (v : Fin 2 → ℝ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => quarterTurn • w) z (complexCoordinates v) =
      complexCoordinates ![-v 1, v 0] := by
  rw [← disk_coefficients_classical, quarter_turn_coefficients]

theorem quotient_origin_has_four_arrows :
    Nat.card (SheafActionQuotient.Arrow
      (SheafActionQuotient.chart diskRepresentation.action (point coordinateOrigin))
      (SheafActionQuotient.chart diskRepresentation.action (point coordinateOrigin))) = 4 :=
  origin_arrow_count

/-- The ineffective action has four arrows even though every tangent map is the identity. -/
theorem ineffective_has_four_arrows (m : realBase ⟶ SmoothOpenSite.scalar) :
    Nat.card (SheafActionQuotient.Arrow
      (SheafActionQuotient.chart ineffectiveRepresentation.action m)
      (SheafActionQuotient.chart ineffectiveRepresentation.action m)) = 4 :=
  (Nat.card_congr (ineffectiveArrowEquiv m)).trans card_C4

theorem ineffective_tangent_identity (g : C4) (X : Sheaf SmoothOpenSite.topology Type)
    (h : SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ SmoothOpenSite.scalar) :
    SmoothGeometricKL.coefficients (h ≫ ineffectiveScalarAction g) = SmoothGeometricKL.coefficients h :=
  ineffective_coefficients g X h

/-- The singular quotient still has a discrete fixed-lift tangent fiber, with
two real-coordinate velocities over every sheaf parameter. -/
def diskFixedFiberComparison (X : Sheaf SmoothOpenSite.topology Type) (m : X ⟶ diskSheaf) :
    Discrete (X ⟶ SmoothOpenSite.scalarPower 2) ≌
      QuotientFixedArcs.Fiber diskRepresentation.action (SmoothOpenSite.parameterZero X) m :=
  SmoothQuotientTransport.openFixedFiberEquivalence diskDomain diskRepresentation.action X m

/-- An actual quotient arrow transports an actual fixed arc by the quarter-turn
matrix; this is the forward boundary transport, not merely an arrow-label formula. -/
theorem actual_quarter_turn_transport
    (h : QuotientFixedArcs.Arcs (SmoothOpenSite.parameterZero realBase) (point coordinateOrigin))
    (A : SmoothPresentationSite.Code) (x : realBase.obj.obj (SmoothGeometricKL.atStage A)) :
    ((SmoothOpenArcs.parameterCoefficients diskDomain realBase
      (SmoothQuotientTransport.forwardArcTransport (originActionArrow quarterTurn) h).val).hom.app
        (SmoothGeometricKL.atStage A) x).2 =
      coefficientAction quarterTurn
        ((SmoothOpenArcs.parameterCoefficients diskDomain realBase h.val).hom.app
          (SmoothGeometricKL.atStage A) x).2 :=
  SmoothQuotientTransport.origin_forward_coefficients quarterTurn h A x

theorem actual_ineffective_transport (m : realBase ⟶ SmoothOpenSite.scalar)
    (h : QuotientFixedArcs.Arcs (SmoothOpenSite.parameterZero realBase) m) :
    SmoothQuotientTransport.forwardArcTransport
      (SmoothQuotientTransport.ineffectiveActionArrow quarterTurn m) h = h :=
  SmoothQuotientTransport.ineffective_forward_identity quarterTurn m h

end Examples.QuarterTurnArcs

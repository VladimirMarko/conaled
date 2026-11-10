import SquareKit.SmoothQuotientDeformationCharts
import SquareKit.SmoothQuotientDeformationFiber

/-! Source-derived transport composition and its classical fixed-lift
comparison. Descent of the parameter-indexed interpretation is a separate
obligation; these consumers do not assert that it is already established. -/
noncomputable section
namespace SquareKit.SmoothQuotientSource
open CategoryTheory SheafActionQuotient SmoothOpenSite SmoothQuotientDeformations
open SmoothQuarterTurnArcs SmoothQuarterTurnQuotient SmoothQuotientTransport
open Orbifolds.QuarterTurn
open scoped Manifold
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M : Sheaf topology Type}

/-- The unchanged all-rule source interpreter on the whole quotient groupoid
and constructed deformation family, with explicit universe lifts. -/
abbrev model (a : Action (locallyConstantGroup H) M) (X : Sheaf topology Type) :=
  Internal.PathTransport.GroupoidModel.Instance.universeModel (Object a X) (family a X)

/-- The ordinary tangent consumer follows from the retained source proof,
then the existing fixed-lift and classical derivative comparisons. -/
theorem origin_classical_composition (g k : C4)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) (point coordinateOrigin))
    (x : realBase.obj.obj (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0))) :
    complexCoordinates (fun i => realEvaluation
      (((SmoothOpenArcs.parameterCoefficients diskDomain realBase
        (forwardArcTransport (originActionArrow g ≫ originActionArrow k) h).val).hom.app
          (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) x).2 i)) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => k • w) origin
        (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => g • w) origin
          (complexCoordinates (fun i => realEvaluation
            (((SmoothOpenArcs.parameterCoefficients diskDomain realBase h.val).hom.app
              (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) x).2 i)))) := by
  rw [source_arc_composition, origin_forward_classical, origin_forward_classical]

/-- Distinct ineffective quotient loops still have identity source-derived
transport. The arrows are not identified by the action on tangent fibers. -/
theorem ineffective_composition (g k : C4) (m : realBase ⟶ scalar)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) m) :
    forwardArcTransport (ineffectiveActionArrow g m ≫ ineffectiveActionArrow k m) h = h := by
  rw [source_arc_composition, ineffective_forward_identity, ineffective_forward_identity]

end SquareKit.SmoothQuotientSource

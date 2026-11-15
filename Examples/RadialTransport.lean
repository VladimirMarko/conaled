import Applications.Geometry.RadialTransport
import SquareKit.SmoothQuarterTurnArcs

/-! Selected circle and hold observations for the fixed radial metric. The
closing labels remain separate from the transport maps and their actions. -/
noncomputable section
namespace Examples.RadialTransport
open RadialMetric Complex Orbifolds.QuarterTurn

/-- Both selected paths close with the identity arrow at radius 1/4. -/
def circleClosing : C4 := 1
def holdClosing : C4 := 1

theorem same_endpoint_and_closing :
    circle (1/4) 0 = (1/4 : ℂ) ∧ circle (1/4) (2*Real.pi) = (1/4 : ℂ) ∧
    (circleClosing.val : ℂ)*(1/4 : ℂ) = (1/4 : ℂ) ∧ circleClosing = holdClosing := by
  exact ⟨by simpa using circle_initial (1/4),by simpa using circle_closed (1/4),by simp [circleClosing],rfl⟩

/-- The same endpoint, duration, and closing label do not determine transport. -/
theorem circle_hold_transport_distinct :
    (circleClosing.val : ℂ)*circleTransport (1/4) (2*Real.pi) 1 ≠
      (holdClosing.val : ℂ)*1 := by
  simpa [circleClosing,holdClosing] using
    circleTransport_nontrivial (r := 1/4) (by norm_num) (by norm_num)

theorem actual_circle_transport (v : ℂ) :
    circleTransport (1/4) 0 v = v ∧
    ∀ t : ℝ, HasDerivAt (fun s => circleTransport (1/4) s v)
      (-gamma (circle (1/4) t) (I*circle (1/4) t) (circleTransport (1/4) t v)) t :=
  ⟨circleTransport_initial _ _, fun t => circleTransport_derivative _ _ _⟩

theorem actual_hold_transport (v : ℂ) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => v) (-gamma (1/4 : ℂ) 0 v) t := holdTransport_derivative _ _ _

/-- At the singular point, a closing symmetry may fix position and rotate tangent. -/
theorem singular_closing_control : (quarterTurn.val : ℂ)*0 = 0 ∧
    (quarterTurn.val : ℂ)*1 ≠ 1 := by
  constructor
  · simp
  · simp only [quarterTurn_scalar,mul_one]
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi

/-- The existing ineffective family retains distinct labels with identical action.
This does not assert that the tangent action of this metric is ineffective. -/
theorem ineffective_label_control : quarterTurn ≠ (1 : C4) ∧
    SquareKit.SmoothQuarterTurnArcs.ineffectiveScalarAction quarterTurn =
      SquareKit.SmoothQuarterTurnArcs.ineffectiveScalarAction 1 :=
  SquareKit.SmoothQuarterTurnArcs.ineffective_distinct_labels

end Examples.RadialTransport

import Applications.Orbifold.TransportSegments
import Applications.Orbifold.QuarterTurn
import Applications.Orbifold.MatrixDisk

/-! Experimental coordinate comparisons for constructed disk transport.
C4 labels remain in the existing action groupoid. Ellipse coordinates use the
ordinary manifold coordinate change from #41. -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Orbifold.DiskTransport
open DiskConnection

/-- Unit complex rotations preserve the connection coefficient. -/
theorem rotation_coefficient (a z u : ℂ) (ha : Complex.normSq a = 1) :
    coefficient (a * z) (a * u) = coefficient z u := by
  have h : conj a * a = 1 := by rw [mul_comm, Complex.mul_conj, ha]; norm_num
  simp only [coefficient, gap, map_mul, ha, one_mul]
  rw [show 2 * (conj a * conj z) * (a * u) = (conj a * a) * (2 * conj z * u) by ring, h, one_mul]

namespace Segment
variable {x y : Disk}

def rotate (g : QuarterTurn.C4) (s : Segment x y) : Segment (g • x) (g • y) where
  duration := s.duration
  nonneg := s.nonneg
  curve := fun t => (g.val : ℂ) * s.curve t
  velocity := fun t => (g.val : ℂ) * s.velocity t
  source := by rw [s.source]; rfl
  target := by rw [s.target]; rfl
  inside := fun t ht => by simpa [map_mul, QuarterTurn.phase_unit] using s.inside t ht
  derivative := fun t ht => (s.derivative t ht).const_mul _
  factor := s.factor
  nonzero := s.nonzero
  equation := by
    intro t ht
    rw [rotation_coefficient _ _ _ (QuarterTurn.phase_unit g)]
    exact s.equation t ht

/-- Both sides use constructed transport. The derivative of the shared C4
coordinate action is multiplication by the same labeled unit scalar. -/
theorem rotate_transport (g : QuarterTurn.C4) (s : Segment x y) (v : ℂ) :
    (g.val : ℂ) * s.transport v = (s.rotate g).transport ((g.val : ℂ) * v) := by
  simp [transport, rotate, ParallelTransport.scalar]; ring

end Segment

namespace Path
variable {x y : Disk}

def rotate (g : QuarterTurn.C4) : {x y : Disk} → Path x y → Path (g • x) (g • y)
  | _, _, .nil _ => .nil _
  | _, _, .cons s p => .cons (s.rotate g) (p.rotate g)

theorem rotate_transport (g : QuarterTurn.C4) (p : Path x y) (v : ℂ) :
    (g.val : ℂ) * p.transport v = (p.rotate g).transport ((g.val : ℂ) * v) := by
  induction p generalizing v with
  | nil => rfl
  | cons s p ih =>
    change (g.val : ℂ) * p.transport (s.transport v) =
      (p.rotate g).transport ((s.rotate g).transport ((g.val : ℂ) * v))
    rw [ih, s.rotate_transport]

end Path

/-- Independently expressed ellipse Christoffel term. The disk coordinates are
`(q.re/2,q.im)` and tangent coordinates are `(u.re/2,u.im)`. -/
def ellipseGamma (q u v : ℂ) : ℂ :=
  let b := ConnectionAssessment.gamma
    (ConnectionAssessment.diskGradient (q.re / 2) q.im) (u.re / 2, u.im) (v.re / 2, v.im)
  ⟨2 * b.1, b.2⟩

def ellipseMetric (q u v : ℂ) : ℝ :=
  metric (Orbifolds.QuarterTurn.stretch.symm q)
    (Orbifolds.QuarterTurn.stretch.symm u) (Orbifolds.QuarterTurn.stretch.symm v)

theorem ellipse_connection_preserved (z u v : ℂ) (hz : gap z ≠ 0) :
    Orbifolds.QuarterTurn.stretch (christoffel z u v) =
      ellipseGamma (Orbifolds.QuarterTurn.stretch z)
        (Orbifolds.QuarterTurn.stretch u) (Orbifolds.QuarterTurn.stretch v) := by
  have h := conformal_coefficient z u v hz
  apply Complex.ext
  · have h1 := congrArg Prod.fst h
    simpa [ellipseGamma, Orbifolds.QuarterTurn.stretch] using congrArg (fun r : ℝ => 2 * r) h1
  · have h2 := congrArg Prod.snd h
    simpa [ellipseGamma, Orbifolds.QuarterTurn.stretch] using h2

/-- Coordinate evaluation of an ellipse field, independent of linear-map composition. -/
def ellipseField {x y : Disk} (s : Segment x y) (v : ℂ) (t : ℝ) : ℂ :=
  let q := s.factor t / s.factor 0
  ⟨q.re * v.re - 2 * q.im * v.im, q.im * v.re / 2 + q.re * v.im⟩

theorem ellipse_field_agreement {x y : Disk} (s : Segment x y) (v : ℂ) (t : ℝ) :
    ellipseField s (Orbifolds.QuarterTurn.stretch v) t =
      Orbifolds.QuarterTurn.stretch (s.field v t) := by
  apply Complex.ext <;>
    simp [ellipseField, Segment.field, Orbifolds.QuarterTurn.stretch, Complex.mul_re, Complex.mul_im] <;> ring

theorem ellipse_field_parallel {x y : Disk} (s : Segment x y) (v : ℂ)
    (t : ℝ) (ht : t ∈ Icc 0 s.duration) :
    HasDerivAt (fun r => ellipseField s (Orbifolds.QuarterTurn.stretch v) r)
      (-ellipseGamma (Orbifolds.QuarterTurn.stretch (s.curve t))
        (Orbifolds.QuarterTurn.stretch (s.velocity t))
        (ellipseField s (Orbifolds.QuarterTurn.stretch v) t)) t := by
  have hd := Orbifolds.QuarterTurn.stretch.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (s.field_parallel v t ht)
  have hg := ellipse_connection_preserved (s.curve t) (s.velocity t) (s.field v t)
    (ne_of_gt (sub_pos.mpr (s.inside t ht)))
  simp only [christoffel] at hg
  convert hd using 1
  · funext r; exact ellipse_field_agreement s v r
  · rw [ellipse_field_agreement, ← hg, ← map_neg]; simp only [neg_mul]; rfl

/-- The independently specified ellipse coefficient agrees with conjugation of
the disk equation by the derivative of the existing coordinate diffeomorphism. -/
theorem ellipse_conjugate (z u w : ℂ) (hz : gap z ≠ 0) :
    ellipseGamma (Orbifolds.QuarterTurn.stretch z) (Orbifolds.QuarterTurn.stretch u) w =
      ParallelTransport.conjugateCoefficient Orbifolds.QuarterTurn.stretch (coefficient z u) w := by
  have h := ellipse_connection_preserved z u (Orbifolds.QuarterTurn.stretch.symm w) hz
  change ellipseGamma (Orbifolds.QuarterTurn.stretch z) (Orbifolds.QuarterTurn.stretch u) w =
    Orbifolds.QuarterTurn.stretch (coefficient z u * Orbifolds.QuarterTurn.stretch.symm w)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, christoffel] using h.symm

/-- The endpoint agreement also follows through the reusable connection
comparison theorem and uniqueness, rather than only coordinate simplification. -/
theorem ellipse_transport_comparison {x y : Disk} (s : Segment x y) (v : ℂ) :
    Orbifolds.QuarterTurn.stretch (s.transport v) =
      ellipseField s (Orbifolds.QuarterTurn.stretch v) s.duration := by
  apply ParallelTransport.linear_comparison Orbifolds.QuarterTurn.stretch s.nonneg
    s.nonzero s.equation
  · intro t ht
    have h := ellipse_field_parallel s v t ht
    rw [ellipse_conjugate _ _ _ (ne_of_gt (sub_pos.mpr (s.inside t ht)))] at h
    exact h
  · rw [ellipse_field_agreement, s.field_initial]

/-- The endpoint square uses the independently expressed ellipse field. -/
def ellipseSquare {x y : Disk} (s : Segment x y) :
    Squares.Square ⟨ℂ, ℂ, Orbifolds.QuarterTurn.stretch⟩
      ⟨ℂ, ℂ, Orbifolds.QuarterTurn.stretch⟩ where
  impl := s.transport
  spec := fun v => ellipseField s v s.duration
  commutes v := ellipse_transport_comparison s v

open scoped Manifold in
/-- The C4 comparison in the actual manifold tangent API used by #41. -/
theorem Path.manifold_rotate_transport {x y : Disk} (g : QuarterTurn.C4)
    (p : Path x y) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Disk => g • z) y (p.transport v) =
      (p.rotate g).transport
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Disk => g • z) x v) := by
  rw [Orbifolds.QuarterTurn.disk_tangent, Orbifolds.QuarterTurn.disk_tangent]
  exact p.rotate_transport g v

open scoped Manifold in
/-- The ellipse comparison uses the derivative of the existing diffeomorphism. -/
theorem manifold_ellipse_transport {x y : Disk} (s : Segment x y) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Orbifolds.QuarterTurn.diskEllipse y (s.transport v) =
      ellipseField s
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Orbifolds.QuarterTurn.diskEllipse x v) s.duration := by
  rw [Orbifolds.QuarterTurn.diskEllipse_derivative, Orbifolds.QuarterTurn.diskEllipse_derivative]
  exact ellipse_transport_comparison s v

/-- The ellipse endpoint equivalence on the existing real tangent coordinates. -/
def Path.ellipseTransport {x y : Disk} (p : Path x y) : ℂ ≃ₗ[ℝ] ℂ :=
  (Orbifolds.QuarterTurn.stretch.symm.toLinearEquiv.trans p.transport).trans
    Orbifolds.QuarterTurn.stretch.toLinearEquiv

theorem Path.ellipse_transport_square {x y : Disk} (p : Path x y) (v : ℂ) :
    p.ellipseTransport (Orbifolds.QuarterTurn.stretch v) =
      Orbifolds.QuarterTurn.stretch (p.transport v) := by
  simp [Path.ellipseTransport]

theorem Path.ellipse_metric_preserved {x y : Disk} (p : Path x y) (v w : ℂ) :
    ellipseMetric (Orbifolds.QuarterTurn.stretch y.val)
      (p.ellipseTransport v) (p.ellipseTransport w) =
    ellipseMetric (Orbifolds.QuarterTurn.stretch x.val) v w := by
  simp only [ellipseMetric, Path.ellipseTransport, LinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.symm_apply_apply]
  exact p.metric_pair_preserved _ _

theorem Path.ellipse_append {x y z : Disk} (p : Path x y) (q : Path y z) :
    (p.append q).ellipseTransport = p.ellipseTransport.trans q.ellipseTransport := by
  ext v
  simp [Path.ellipseTransport, Path.append_transport]

/-- On a single segment the ellipse equivalence equals the independent formula
whose parallel equation and uniqueness are checked above. -/
theorem ellipse_segment_transport {x y : Disk} (s : Segment x y) (v : ℂ) :
    (Path.cons s (.nil _)).ellipseTransport v = ellipseField s v s.duration := by
  have h := ellipse_transport_comparison s (Orbifolds.QuarterTurn.stretch.symm v)
  simpa [Path.ellipseTransport, Path.transport] using h

end Orbifold.DiskTransport

import Applications.Orbifold.TransportFrames
import Applications.Orbifold.DiskCurvature
import Applications.Geometry.VariableCurvature

/-! Checked uses of experimental path transport: actual equations, time,
composition, holonomy, representative changes, and independent realizations. -/
noncomputable section
open Set CategoryTheory MulAction
open scoped Manifold
namespace Examples.PathTransport
open Orbifold Orbifold.DiskTransport

/-- Nonconstant radial motion has the independently calculated scale 3/4. -/
example : halfRadial.curve 0 ≠ halfRadial.curve halfRadial.duration ∧
    halfRadial.transport 1 = 3 / 4 := by
  exact ⟨halfRadial_nonconstant, by simpa using halfRadial_transport 1⟩

def outAndBack := Path.cons halfRadial (Path.cons halfRadial.reverse (.nil _))

example : outAndBack.transport = LinearEquiv.refl ℝ ℂ := by
  ext v
  simp [outAndBack, Path.transport, Segment.reverse_transport]

example : outAndBack.duration = 1 := by
  norm_num [outAndBack, Path.duration, Segment.reverse, halfRadial, radial]

example (v : ℂ) : Path.ParallelField outAndBack v v := by
  have h := outAndBack.transport_parallel v
  simpa [outAndBack, Path.transport, Segment.reverse_transport] using h

example : (Segment.hold Orbifolds.QuarterTurn.origin 3 (by norm_num)).duration = 3 ∧
    (Segment.hold Orbifolds.QuarterTurn.origin 3 (by norm_num)).transport 1 = 1 := by
  exact ⟨rfl, by rw [Segment.hold_transport]; rfl⟩

/-- Endpoint equality cannot serve as the semantics of paths. -/
example : turnPoint loopPoint (2 * Real.pi) = loopPoint ∧
    (circle loopPoint loopPoint_radius (2 * Real.pi) (by positivity)).transport 1 = -1 := by
  exact ⟨loop_endpoint, by simpa using loop_transport 1⟩

/-- Representative changes use actual manifold derivatives, even at the apex. -/
example :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun z : Disk => Orbifolds.QuarterTurn.quarterTurn • z)
      Orbifolds.QuarterTurn.origin
      ((Segment.hold Orbifolds.QuarterTurn.origin 1 (by norm_num)).transport 1) = Complex.I := by
  rw [Orbifolds.QuarterTurn.disk_tangent, Segment.hold_transport]
  simp [Orbifolds.QuarterTurn.quarterTurn_scalar] <;> rfl

example :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun z : Disk => Orbifolds.QuarterTurn.quarterTurn • z)
      Orbifolds.QuarterTurn.half
      ((Segment.hold Orbifolds.QuarterTurn.half 1 (by norm_num)).transport 1) = Complex.I := by
  rw [Orbifolds.QuarterTurn.disk_tangent, Segment.hold_transport]
  simp [Orbifolds.QuarterTurn.quarterTurn_scalar] <;> rfl

/-- Both representative changes intertwine every admitted path, not only holds. -/
example {x y : Disk} (p : DiskTransport.Path x y) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun z : Disk => Orbifolds.QuarterTurn.quarterTurn • z) y (p.transport v) =
    (p.rotate Orbifolds.QuarterTurn.quarterTurn).transport
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (fun z : Disk => Orbifolds.QuarterTurn.quarterTurn • z) x v) :=
  p.manifold_rotate_transport _ v

example : (ellipseSquare halfRadial).spec (2 + Complex.I) = 3 / 2 + (3 / 4) * Complex.I := by
  change ellipseField halfRadial (2 + Complex.I) halfRadial.duration = ((3 / 2 : ℂ) + (3 / 4 : ℂ) * Complex.I)
  norm_num [ellipseField, halfRadial, radial]
  apply Complex.ext <;> norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

example (v : ℂ) :
    VariableCurvature.transport 1 0 1 v = Complex.exp (-2 * Complex.I) * v := by
  simp [VariableCurvature.transport, ParallelTransport.scalar, VariableCurvature.factor]

example :
    ConformalConnection.gaussian VariableCurvature.scale VariableCurvature.coefficient 0 ≠
    ConformalConnection.gaussian VariableCurvature.scale VariableCurvature.coefficient 1 :=
  VariableCurvature.curvature_nonconstant

/-- A stationary lift can have a nontrivial closing symmetry. Its transport is
identity; the labeled closing arrow contributes the quarter turn. -/
def apexClosed : Path.ClosedLift Orbifolds.QuarterTurn.origin where
  endpoint := Orbifolds.QuarterTurn.origin
  path := .cons (Segment.hold _ 1 (by norm_num)) (.nil _)
  closing := Functor.Elements.homMk Orbifolds.QuarterTurn.quarterTurn (by
    change Orbifolds.QuarterTurn.quarterTurn • Orbifolds.QuarterTurn.origin = Orbifolds.QuarterTurn.origin
    apply Subtype.ext
    simp [Orbifolds.QuarterTurn.disk_smul_coe, Orbifolds.QuarterTurn.origin])

example : apexClosed.path.transport 1 = 1 ∧ apexClosed.endomorphism 1 = Complex.I := by
  simp [apexClosed, Path.transport, Path.ClosedLift.endomorphism, Path.ClosedLift.label,
    Segment.hold_transport, Orbifolds.QuarterTurn.quarterTurn_scalar]

/-- The closing arrow survives the disk/ellipse action-groupoid comparison. -/
example : (Orbifolds.QuarterTurn.coordinateChange.functor.map apexClosed.closing).hom =
    apexClosed.closing.hom := rfl

example {x y : Disk} (p : DiskTransport.Path x y) (q : Pose) (hx : q.a = x.val) (w : ℂ) :
    MatrixDisk.frameAction (p.terminalPose q hx).matrix 0 (w / 2) =
      p.transport (q.frame w) := p.terminal_matrix_frame q hx w

def inverseQuarter : QuarterTurn.C4 := Orbifolds.QuarterTurn.quarterTurn⁻¹

/-- A regular lift closes only after the inverse quarter-turn identification. -/
def quarterClosed : Path.ClosedLift loopPoint where
  endpoint := turnPoint loopPoint (Real.pi / 2)
  path := .cons (circle loopPoint loopPoint_radius (Real.pi / 2) (by positivity)) (.nil _)
  closing := Functor.Elements.homMk inverseQuarter (by
    apply Subtype.ext
    change ((Orbifolds.QuarterTurn.quarterTurn⁻¹).val : ℂ) *
      (loopPoint.val * DiskTransport.turn (Real.pi / 2)) = loopPoint.val
    have hi : ((Orbifolds.QuarterTurn.quarterTurn⁻¹).val : ℂ) = -Complex.I := by
      simp [Orbifolds.QuarterTurn.quarterTurn, Units.val_inv_eq_inv_val]
    have ht : DiskTransport.turn (Real.pi / 2) = Complex.I := by simp [DiskTransport.turn]
    rw [hi, ht]
    have hI := Complex.I_sq
    linear_combination -loopPoint.val * hI)

example : quarterClosed.endpoint ≠ loopPoint := by
  intro he
  have h := congrArg Subtype.val he
  change loopPoint.val * DiskTransport.turn (Real.pi / 2) = loopPoint.val at h
  have ht : DiskTransport.turn (Real.pi / 2) = Complex.I := by simp [DiskTransport.turn]
  rw [ht] at h
  have hn : loopPoint.val ≠ 0 := by
    intro hz
    have hr := loopPoint_radius
    rw [hz, map_zero] at hr
    norm_num at hr
  have hi := mul_left_cancel₀ hn (h.trans (mul_one _).symm)
  have hh := congrArg Complex.im hi
  norm_num at hh

example : quarterClosed.label = Orbifolds.QuarterTurn.quarterTurn⁻¹ := rfl

example (v : ℂ) : quarterClosed.endomorphism v =
    -Complex.I * (turn (-(Real.pi / 2) / 2) * v) := by
  change ((Orbifolds.QuarterTurn.quarterTurn⁻¹).val : ℂ) *
    (circle loopPoint loopPoint_radius (Real.pi / 2) _).transport v = _
  rw [circle_transport]
  have hi : ((Orbifolds.QuarterTurn.quarterTurn⁻¹).val : ℂ) = -Complex.I := by
    simp [Orbifolds.QuarterTurn.quarterTurn, Units.val_inv_eq_inv_val]
  rw [hi]

open Orbifold.DiskConnection in
/-- A checked specialization of the full coordinate-change theorem, including
actual first and second derivatives. The target field is the independent ellipse
formula, and its uniqueness comes from the proved integrating-factor theorem. -/
theorem ellipse_general_comparison {x y : Disk} (s : Segment x y) (v : ℂ) :
    Orbifolds.QuarterTurn.stretch (s.transport v) =
      ellipseField s (Orbifolds.QuarterTurn.stretch v) s.duration := by
  let L := Orbifolds.QuarterTurn.stretch
  let G := fun z u : ℂ => ContinuousLinearMap.mul ℝ ℂ (coefficient z u)
  let H := fun z u : ℂ => ParallelTransport.conjugateCoefficient L
    (coefficient (L.symm z) (L.symm u))
  have hQ (w : ℂ) (t : ℝ) (ht : t ∈ Icc 0 s.duration) :
      HasDerivAt (fun r => ellipseField s w r)
        (-H (L (s.curve t)) (L (s.velocity t)) (ellipseField s w t)) t := by
    have h := ellipse_field_parallel s (L.symm w) t ht
    rw [show Orbifolds.QuarterTurn.stretch (L.symm w) = w from L.apply_symm_apply w] at h
    rw [ellipse_conjugate _ _ _ (ne_of_gt (sub_pos.mpr (s.inside t ht)))] at h
    simpa only [H, L.symm_apply_apply] using h
  have hiQ (w : ℂ) : ellipseField s w 0 = w := by
    have h := ellipse_field_agreement s (L.symm w) 0
    change ellipseField s (L (L.symm w)) 0 = L (s.field (L.symm w) 0) at h
    simpa only [L.apply_symm_apply, s.field_initial] using h
  have result := ParallelTransport.coordinate_transport
    (G := G) (H := H) (phi := L) (dphi := fun _ => L.toContinuousLinearMap)
    (ddphi := fun _ => 0) (U := Set.univ)
    (by intro z hz u w; simp [G, H,
      ParallelTransport.conjugateCoefficient])
    (c := s.curve) (velocity := s.velocity) (s := Icc 0 s.duration)
    (a := 0) (b := s.duration)
    (fun _ _ => Set.mem_univ _) s.derivative
    (fun z _ => L.toContinuousLinearMap.hasFDerivAt)
    (fun z _ => hasFDerivAt_const L.toContinuousLinearMap z)
    s.field (fun w t => ellipseField s w t)
    (by intro w t ht; simpa only [G, ContinuousLinearMap.mul_apply', neg_mul] using s.field_parallel w t ht)
    hQ s.field_initial hiQ
    (by
      intro f g hf hg h0
      have hf' : ∀ t ∈ Icc 0 s.duration,
          HasDerivAt f (-ParallelTransport.conjugateCoefficient L
            (coefficient (s.curve t) (s.velocity t)) (f t)) t := by
        intro t ht
        have hh := hf t ht
        change HasDerivAt f (-H (L (s.curve t)) (L (s.velocity t)) (f t)) t at hh
        simpa only [H, L.symm_apply_apply] using hh
      have hg' : ∀ t ∈ Icc 0 s.duration,
          HasDerivAt g (-ParallelTransport.conjugateCoefficient L
            (coefficient (s.curve t) (s.velocity t)) (g t)) t := by
        intro t ht
        have hh := hg t ht
        change HasDerivAt g (-H (L (s.curve t)) (L (s.velocity t)) (g t)) t at hh
        simpa only [H, L.symm_apply_apply] using hh
      rw [ParallelTransport.conjugate_unique L s.nonzero s.equation hf' ⟨s.nonneg, le_rfl⟩,
        ParallelTransport.conjugate_unique L s.nonzero s.equation hg' ⟨s.nonneg, le_rfl⟩, h0]) v
  exact result

end Examples.PathTransport

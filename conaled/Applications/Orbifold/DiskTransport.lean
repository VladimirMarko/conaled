import Applications.Geometry.ParallelTransport
import Applications.Orbifold.DiskConnection

/-! Experimental exact disk transport for finite words of timed analytic segments.
A segment supplies a scalar solution of the connection equation, not transport
laws. Constructors below discharge that analytic certificate by explicit formulas. -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Orbifold.DiskTransport
open DiskConnection

/-- A chart path with an explicitly solved scalar equation on its closed time interval.
Endpoint derivatives refer to smooth extensions; joints need only be continuous. -/
structure Segment (x y : Disk) where
  duration : ℝ
  nonneg : 0 ≤ duration
  curve : ℝ → ℂ
  velocity : ℝ → ℂ
  source : curve 0 = x.val
  target : curve duration = y.val
  inside : ∀ t ∈ Icc 0 duration, Complex.normSq (curve t) < 1
  derivative : ∀ t ∈ Icc 0 duration, HasDerivAt curve (velocity t) t
  factor : ℝ → ℂ
  nonzero : ∀ t ∈ Icc 0 duration, factor t ≠ 0
  equation : ∀ t ∈ Icc 0 duration,
    HasDerivAt factor (-coefficient (curve t) (velocity t) * factor t) t

namespace Segment
variable {x y z : Disk}

def transport (s : Segment x y) : ℂ ≃ₗ[ℝ] ℂ :=
  ParallelTransport.scalar s.factor 0 s.duration
    (s.nonzero 0 ⟨le_rfl, s.nonneg⟩) (s.nonzero s.duration ⟨s.nonneg, le_rfl⟩)

def field (s : Segment x y) (v : ℂ) (t : ℝ) : ℂ := s.factor t / s.factor 0 * v

@[simp] theorem field_initial (s : Segment x y) (v : ℂ) : s.field v 0 = v := by
  simp [field, s.nonzero 0 ⟨le_rfl, s.nonneg⟩]

@[simp] theorem field_final (s : Segment x y) (v : ℂ) :
    s.field v s.duration = s.transport v := rfl

theorem field_parallel (s : Segment x y) (v : ℂ) (t : ℝ) (ht : t ∈ Icc 0 s.duration) :
    HasDerivAt (s.field v) (-coefficient (s.curve t) (s.velocity t) * s.field v t) t :=
  ParallelTransport.scalar_solves (q := s.factor) (k := fun t => coefficient (s.curve t) (s.velocity t))
    (a := 0) (s.equation t ht) v

theorem field_unique (s : Segment x y) (w : ℝ → ℂ)
    (hw : ∀ t ∈ Icc 0 s.duration,
      HasDerivAt w (-coefficient (s.curve t) (s.velocity t) * w t) t)
    (t : ℝ) (ht : t ∈ Icc 0 s.duration) : w t = s.field (w 0) t :=
  ParallelTransport.scalar_unique s.nonzero s.equation hw ht

/-- Metric preservation follows from differentiating the metric, rather than
being a certificate carried by the segment. -/
theorem metric_preserved (s : Segment x y) (v : ℂ) :
    metric y.val (s.transport v) (s.transport v) = metric x.val v v := by
  have hd : ∀ t ∈ Icc 0 s.duration,
      HasDerivAt (fun t => metric (s.curve t) (s.field v t) (s.field v t)) 0 t := by
    intro t ht
    exact parallel_metric_derivative (s.derivative t ht)
      (ne_of_gt (sub_pos.mpr (s.inside t ht))) (s.field_parallel v t ht)
  have he := constant_of_has_deriv_right_zero
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (mem_Icc_of_Ico ht)).hasDerivWithinAt)
    s.duration ⟨s.nonneg, le_rfl⟩
  simpa only [s.source, s.target, field_initial, field_final] using he

/-- A hold preserves its prescribed elapsed time. -/
def hold (x : Disk) (T : ℝ) (hT : 0 ≤ T) : Segment x x where
  duration := T
  nonneg := hT
  curve := fun _ => x.val
  velocity := fun _ => 0
  source := rfl
  target := rfl
  inside := fun _ _ => (disk_mem _).mp x.property
  derivative := fun t _ => hasDerivAt_const t _
  factor := fun _ => 1
  nonzero := fun _ _ => one_ne_zero
  equation := fun t _ => by simpa [coefficient] using hasDerivAt_const t (1 : ℂ)

@[simp] theorem hold_transport (x : Disk) (T : ℝ) (hT) :
    (hold x T hT).transport = LinearEquiv.refl ℝ ℂ := by
  ext v; simp [transport, hold, ParallelTransport.scalar]

/-- Reversal uses the original clock duration, not a unit-interval rescaling. -/
def reverse (s : Segment x y) : Segment y x where
  duration := s.duration
  nonneg := s.nonneg
  curve := fun t => s.curve (s.duration - t)
  velocity := fun t => -s.velocity (s.duration - t)
  source := by simpa using s.target
  target := by simpa using s.source
  inside := fun t ht => s.inside _ ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  derivative := by
    intro t ht
    convert (s.derivative _ ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩).scomp t
      ((hasDerivAt_const t s.duration).sub (hasDerivAt_id t)) using 1 <;> first | rfl | simp
  factor := fun t => s.factor (s.duration - t)
  nonzero := fun t ht => s.nonzero _ ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  equation := by
    intro t ht
    convert (s.equation _ ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩).scomp t
      ((hasDerivAt_const t s.duration).sub (hasDerivAt_id t)) using 1 <;> first | rfl | (simp only [coefficient, mul_neg, neg_mul, neg_div, neg_neg, zero_sub, neg_smul, one_smul])

@[simp] theorem reverse_transport (s : Segment x y) :
    s.reverse.transport = s.transport.symm := by
  ext v; simp [transport, reverse, ParallelTransport.scalar]

/-- Any zero-velocity segment has identity transport, irrespective of the
chosen scalar solution certificate and irrespective of elapsed duration. -/
theorem constant_transport (s : Segment x y)
    (hv : ∀ t ∈ Icc 0 s.duration, s.velocity t = 0) :
    s.transport = LinearEquiv.refl ℝ ℂ := by
  ext v
  have h := s.field_unique (fun _ => v) (by
    intro t ht
    rw [hv t ht]
    simpa [coefficient] using hasDerivAt_const t v) s.duration ⟨s.nonneg, le_rfl⟩
  exact h.symm

end Segment

/-- Endpoint-indexed finite concatenations. The clocks remain local to segments. -/
inductive Path : Disk → Disk → Type
  | nil (x : Disk) : Path x x
  | cons {x y z : Disk} (segment : Segment x y) (rest : Path y z) : Path x z

namespace Path
variable {x y z w : Disk}

def duration : {x y : Disk} → Path x y → ℝ
  | _, _, .nil _ => 0
  | _, _, .cons s p => s.duration + p.duration

def transport : {x y : Disk} → Path x y → ℂ ≃ₗ[ℝ] ℂ
  | _, _, .nil _ => LinearEquiv.refl ℝ ℂ
  | _, _, .cons s p => s.transport.trans p.transport

def append : {x y z : Disk} → Path x y → Path y z → Path x z
  | _, _, _, .nil _, q => q
  | _, _, _, .cons s p, q => .cons s (p.append q)

theorem append_duration (p : Path x y) (q : Path y z) :
    (p.append q).duration = p.duration + q.duration := by
  induction p with
  | nil => simp [append, duration]
  | cons s p ih => simp [append, duration, ih, add_assoc]

theorem append_transport (p : Path x y) (q : Path y z) :
    (p.append q).transport = p.transport.trans q.transport := by
  induction p with
  | nil => rfl
  | cons s p ih => rw [append, transport, ih]; rfl

def reverse : {x y : Disk} → Path x y → Path y x
  | _, _, .nil x => .nil x
  | _, _, .cons s p => p.reverse.append (.cons s.reverse (.nil _))

theorem reverse_transport (p : Path x y) : p.reverse.transport = p.transport.symm := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    rw [reverse, append_transport, ih]
    ext v
    simp [transport, Segment.reverse_transport]

theorem reverse_duration (p : Path x y) : p.reverse.duration = p.duration := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [reverse, append_duration, duration, Segment.reverse, ih, add_comm]

theorem metric_preserved (p : Path x y) (v : ℂ) :
    metric y.val (p.transport v) (p.transport v) = metric x.val v v := by
  induction p generalizing v with
  | nil => rfl
  | cons s p ih => exact (ih (s.transport v)).trans (s.metric_preserved v)

/-- A piecewise parallel field matches values at each segment boundary.
This exposes the connection equation for every segment in a finite path. -/
def ParallelField : {x y : Disk} → Path x y → ℂ → ℂ → Prop
  | _, _, .nil _, v, w => w = v
  | _, _, .cons s p, v, w => ∃ f : ℝ → ℂ,
      f 0 = v ∧
      (∀ t ∈ Icc 0 s.duration,
        HasDerivAt f (-coefficient (s.curve t) (s.velocity t) * f t) t) ∧
      ParallelField p (f s.duration) w

theorem transport_parallel (p : Path x y) (v : ℂ) : ParallelField p v (p.transport v) := by
  induction p generalizing v with
  | nil => rfl
  | cons s p ih =>
    exact ⟨s.field v, s.field_initial v, s.field_parallel v,
      by simpa only [Segment.field_final, transport, LinearEquiv.trans_apply] using ih (s.transport v)⟩

theorem transport_unique (p : Path x y) (v w : ℂ) (h : ParallelField p v w) :
    w = p.transport v := by
  induction p generalizing v w with
  | nil => exact h
  | cons s p ih =>
    obtain ⟨f, h0, hf, hp⟩ := h
    have he := s.field_unique f hf s.duration ⟨s.nonneg, le_rfl⟩
    rw [h0, Segment.field_final] at he
    rw [he] at hp
    exact ih _ _ hp

/-- Real linearity and polarization upgrade norm preservation to preservation
of the full bilinear metric. -/
theorem metric_pair_preserved (p : Path x y) (v w : ℂ) :
    metric y.val (p.transport v) (p.transport w) = metric x.val v w := by
  have polar (z a b : ℂ) : metric z (a + b) (a + b) =
      metric z a a + 2 * metric z a b + metric z b b := by
    simp [metric, Complex.mul_re, Complex.mul_im]; ring
  have h := p.metric_preserved (v + w)
  rw [map_add, polar, polar, p.metric_preserved v, p.metric_preserved w] at h
  linarith

end Path
end Orbifold.DiskTransport

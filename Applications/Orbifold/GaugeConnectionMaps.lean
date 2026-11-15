import Applications.Orbifold.FrameGauge

/-! Connection-preserving maps are specified by a differential equation.
Their endpoint squares are derived from local uniqueness. -/
noncomputable section
open Set
namespace Orbifold.FrameGauge
open DiskTransport

/-- A map along a fixed physical segment, not an assumed endpoint square. -/
structure ConnectionMap {x y : Disk} (s : Segment x y) (g h : Gauge) where
  value : ℝ → ℂ
  velocity : ℝ → ℂ
  derivative : ∀ t ∈ Icc 0 s.duration, HasDerivAt value (velocity t) t
  preserves : ∀ t ∈ Icc 0 s.duration,
    velocity t + h.connection (s.curve t) (s.velocity t) * value t =
      value t * g.connection (s.curve t) (s.velocity t)

namespace ConnectionMap
variable {x y : Disk} {s : Segment x y} {f g h : Gauge}

def identity (s : Segment x y) (g : Gauge) : ConnectionMap s g g where
  value _ := 1
  velocity _ := 0
  derivative t _ := hasDerivAt_const t 1
  preserves t _ := by simp

def comp (F : ConnectionMap s f g) (G : ConnectionMap s g h) : ConnectionMap s f h where
  value t := G.value t * F.value t
  velocity t := G.velocity t * F.value t + G.value t * F.velocity t
  derivative t ht := (G.derivative t ht).mul (F.derivative t ht)
  preserves t ht := by
    have hf := F.preserves t ht
    have hg := G.preserves t ht
    linear_combination G.value t * hf + F.value t * hg

/-- The product rule is the passage from connection preservation to fields. -/
theorem map_parallel (F : ConnectionMap s g h) {w : ℝ → ℂ} {t : ℝ}
    (ht : t ∈ Icc 0 s.duration)
    (hw : HasDerivAt w (-g.connection (s.curve t) (s.velocity t) * w t) t) :
    HasDerivAt (fun r => F.value r * w r)
      (-h.connection (s.curve t) (s.velocity t) * (F.value t * w t)) t := by
  convert (F.derivative t ht).mul hw using 1
  have hp := F.preserves t ht
  linear_combination -w t * hp

/-- Local fields are built from the proved fundamental solution. -/
def field (g : Gauge) (s : Segment x y) (a : ℝ) (v : ℂ) (t : ℝ) : ℂ :=
  factor g s t / factor g s a * v

theorem field_equation (g : Gauge) (s : Segment x y) (a : ℝ) (v : ℂ)
    {t : ℝ} (ht : t ∈ Icc 0 s.duration) :
    HasDerivAt (field g s a v)
      (-g.connection (s.curve t) (s.velocity t) * field g s a v t) t :=
  ParallelTransport.scalar_solves (q := factor g s)
    (k := fun t => g.connection (s.curve t) (s.velocity t)) (a := a)
    (factor_equation g s ht) v

theorem transport (F : ConnectionMap s g h) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
    (hab : a ≤ b) (v : ℂ) :
    F.value b * localTransport g s a b ha hb v =
      localTransport h s a b ha hb (F.value a * v) := by
  have he := local_unique h s a b ha hb hab
    (fun t => F.value t * field g s a v t) (by
      intro t ht
      have hi : t ∈ Icc 0 s.duration := ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
      exact F.map_parallel hi (field_equation g s a v hi))
  simpa only [field, localTransport, ParallelTransport.scalar_apply, div_self (factor_nonzero g s ha), one_mul] using he

/-- Identity and successive changes retain the actual selected map. -/
theorem identity_value (t : ℝ) : (identity s g).value t = 1 := rfl

theorem comp_value (F : ConnectionMap s f g) (G : ConnectionMap s g h) (t : ℝ) :
    (F.comp G).value t = G.value t * F.value t := rfl

/-- The atlas overlap itself is a connection-preserving map. The derivative
is the quotient rule; compatibility includes both frame derivatives. -/
def overlap (s : Segment x y) (g h : Gauge) : ConnectionMap s g h where
  value t := g.frame (s.curve t) / h.frame (s.curve t)
  velocity t := (g.differential (s.curve t) (s.velocity t) * h.frame (s.curve t) -
    g.frame (s.curve t) * h.differential (s.curve t) (s.velocity t)) /
      (h.frame (s.curve t)) ^ 2
  derivative t ht := (g.derivative (s.derivative t ht)).div
    (h.derivative (s.derivative t ht)) (h.nonzero _ (s.inside t ht))
  preserves t ht := by
    unfold Gauge.connection
    field_simp [g.nonzero _ (s.inside t ht), h.nonzero _ (s.inside t ht)]
    <;> ring

theorem overlap_transport (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
    (hab : a ≤ b) (v : ℂ) :
    g.transition h (s.curve b) * localTransport g s a b ha hb v =
      localTransport h s a b ha hb (g.transition h (s.curve a) * v) :=
  (overlap s g h).transport a b ha hb hab v

end ConnectionMap
end Orbifold.FrameGauge

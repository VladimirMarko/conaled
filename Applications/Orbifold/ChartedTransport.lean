import Applications.Orbifold.GaugeConnectionMaps

/-! Finite atlas descent with explicit overlap transitions and witnessed
subdivisions. Construction executes local transports before comparison. -/
noncomputable section
open Set
namespace Orbifold.FrameGauge
open DiskTransport

def Gauge.frameMap (g : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) : ℂ ≃ₗ[ℝ] ℂ where
  toFun v := g.frame z * v
  invFun v := v / g.frame z
  left_inv v := by field_simp [g.nonzero z hz]
  right_inv v := by field_simp [g.nonzero z hz]
  map_add' v w := by ring
  map_smul' r v := by simp [Complex.real_smul]; ring

def Gauge.overlap (g h : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) : ℂ ≃ₗ[ℝ] ℂ :=
  (g.frameMap z hz).trans (h.frameMap z hz).symm

theorem overlap_apply (g h : Gauge) (z : ℂ) (hz) (v : ℂ) :
    g.overlap h z hz v = g.transition h z * v := by
  simp [Gauge.overlap, Gauge.frameMap, Gauge.transition]; ring

/-- Typed linear equivalence composition fixes the order independently of
commutativity of the particular phase group. -/
theorem equiv_cocycle {E F G H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
    (e : E ≃ₗ[ℝ] H) (f : F ≃ₗ[ℝ] H) (g : G ≃ₗ[ℝ] H) :
    (e.trans f.symm).trans (f.trans g.symm) = e.trans g.symm := by
  ext v
  simp

/-- Inserting or removing an overlap at the same physical point preserves
its typed map, even for noncommuting linear coordinate maps. -/
theorem overlap_comp (f g h : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    (f.overlap g z hz).trans (g.overlap h z hz) = f.overlap h z hz :=
  equiv_cocycle (f.frameMap z hz) (g.frameMap z hz) (h.frameMap z hz)

theorem overlap_identity (g : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    g.overlap g z hz = LinearEquiv.refl ℝ ℂ := by
  ext v
  simp [Gauge.overlap]

theorem overlap_inverse (g h : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    (g.overlap h z hz).trans (h.overlap g z hz) = LinearEquiv.refl ℝ ℂ := by
  rw [overlap_comp, overlap_identity]

/-- Every subinterval lies in its chosen open chart. Endpoints and times are
retained; no compactness subdivision or selected global transport is assumed. -/
inductive Charting {x y : Disk} (s : Segment x y) : ℝ → ℝ → Type
  | nil (a : ℝ) (ha : a ∈ Icc 0 s.duration) : Charting s a a
  | cons {a b c : ℝ} (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
      (hab : a ≤ b) (i : Bool) (covered : ∀ t ∈ Icc a b, s.curve t ∈ chartDomain i)
      (rest : Charting s b c) : Charting s a c

namespace Charting
variable {x y : Disk} {s : Segment x y} {a b : ℝ}

theorem start : Charting s a b → a ∈ Icc 0 s.duration
  | .nil _ h => h
  | .cons h _ _ _ _ _ => h

theorem finish : {a b : ℝ} → Charting s a b → b ∈ Icc 0 s.duration
  | _, _, .nil _ h => h
  | _, _, .cons _ _ _ _ _ r => r.finish

/-- One covered piece, with the terminal overlap still explicit. -/
def single (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
    (hab : a ≤ b) (i : Bool) (covered : ∀ t ∈ Icc a b, s.curve t ∈ chartDomain i) :
    Charting s a b := .cons ha hb hab i covered (.nil b hb)

/-- Insert a second witnessed chart at an actual subdivision time. -/
def split (m : ℝ) (ha : a ∈ Icc 0 s.duration) (hm : m ∈ Icc 0 s.duration)
    (hb : b ∈ Icc 0 s.duration) (ham : a ≤ m) (hmb : m ≤ b) (i j : Bool)
    (hi : ∀ t ∈ Icc a m, s.curve t ∈ chartDomain i)
    (hj : ∀ t ∈ Icc m b, s.curve t ∈ chartDomain j) : Charting s a b :=
  .cons ha hm ham i hi (.cons hm hb hmb j hj (.nil b hb))

/-- Execute the overlaps, local segment solution, and remaining charted path. -/
def transport : {a b : ℝ} → (p : Charting s a b) → (g h : Gauge) → ℂ ≃ₗ[ℝ] ℂ
  | _, _, .nil t ht, g, h => g.overlap h (s.curve t) (s.inside t ht)
  | _, _, .cons ha hb _ i _ r, g, h =>
      ((g.overlap (chart i) _ (s.inside _ ha)).trans
        (localTransport (chart i) s _ _ ha hb)).trans (r.transport (chart i) h)

theorem decode (p : Charting s a b) (g h : Gauge) (v : ℂ) :
    h.frame (s.curve b) * p.transport g h v =
      s.factor b / s.factor a * (g.frame (s.curve a) * v) := by
  induction p generalizing g h v with
  | nil a ha =>
    simp only [transport, overlap_apply, Gauge.transition]
    field_simp [h.nonzero _ (s.inside a ha), s.nonzero a ha]
    <;> ring
  | @cons a b c ha hb hab i covered r ih =>
    simp only [transport, LinearEquiv.trans_apply]
    rw [ih, local_decode]
    rw [overlap_apply]
    unfold Gauge.transition
    field_simp [(chart i).nonzero _ (s.inside a ha), s.nonzero a ha, s.nonzero b hb]
    <;> ring

/-- Independence covers any two witnessed subdivisions, including insertion
of chart switches and zero-length pieces. It does not erase the physical curve. -/
theorem independent (p q : Charting s a b) (g h : Gauge) :
    p.transport g h = q.transport g h := by
  ext v
  apply mul_left_cancel₀ (h.nonzero _ (s.inside b p.finish))
  rw [p.decode, q.decode]

/-- An arbitrary local gluing is unique if each piece solves the local equation
and its boundary values use the actual overlap. -/
def Parallel : {a b : ℝ} → (p : Charting s a b) → Gauge → Gauge → ℂ → ℂ → Prop
  | _, _, .nil t ht, g, h, v, w => w = g.overlap h (s.curve t) (s.inside t ht) v
  | _, _, @Charting.cons _ _ _ a b _ ha hb _ i _ r, g, h, v, w =>
      ∃ f : ℝ → ℂ,
        f a = g.overlap (chart i) _ (s.inside a ha) v ∧
        (∀ t ∈ Icc a b, HasDerivAt f (-(chart i).connection (s.curve t) (s.velocity t) * f t) t) ∧
        r.Parallel (chart i) h (f b) w

theorem unique (p : Charting s a b) (g h : Gauge) (v w : ℂ)
    (hp : p.Parallel g h v w) : w = p.transport g h v := by
  induction p generalizing g h v w with
  | nil a ha => exact hp
  | @cons a b c ha hb hab i covered r ih =>
    obtain ⟨f, hf, he, hr⟩ := hp
    have hb' := local_unique (chart i) s a b ha hb hab f he
    rw [hf] at hb'
    rw [hb'] at hr
    exact ih _ _ _ _ hr

/-- Every executed charting supplies local solutions satisfying its overlap
boundary conditions; uniqueness is therefore nonvacuous. -/
theorem parallel (p : Charting s a b) (g h : Gauge) (v : ℂ) :
    p.Parallel g h v (p.transport g h v) := by
  induction p generalizing g h v with
  | nil a ha => rfl
  | @cons a b c ha hb hab i covered r ih =>
    let u := g.overlap (chart i) (s.curve a) (s.inside a ha) v
    refine ⟨ConnectionMap.field (chart i) s a u, ?_, ?_, ?_⟩
    · simp [ConnectionMap.field, div_self (factor_nonzero (chart i) s ha), u]
    · intro t ht
      exact ConnectionMap.field_equation (chart i) s a u
        ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    · exact ih (chart i) h (localTransport (chart i) s a b ha hb u)


def physical (p : Charting s a b) : ℂ ≃ₗ[ℝ] ℂ :=
  ((standard.frameMap _ (s.inside a p.start)).symm.trans (p.transport standard standard)).trans
    (standard.frameMap _ (s.inside b p.finish))

theorem physical_apply (p : Charting s a b) (v : ℂ) :
    p.physical v = s.factor b / s.factor a * v := by
  change standard.frame (s.curve b) * p.transport standard standard
    (v / standard.frame (s.curve a)) = _
  rw [p.decode]
  congr 1
  field_simp [standard.nonzero _ (s.inside a p.start)]

theorem full_agreement (p : Charting s 0 s.duration) : p.physical = s.transport := by
  ext v
  exact p.physical_apply v

/-- A connection-preserving change of local frame data commutes at both ends.
The frame-square proof precedes this composition consequence. -/
theorem change (p : Charting s a b) (g h g' h' : Gauge) :
    (g.overlap g' _ (s.inside a p.start)).trans (p.transport g' h') =
      (p.transport g h).trans (h.overlap h' _ (s.inside b p.finish)) := by
  ext v
  apply mul_left_cancel₀ (h'.nonzero _ (s.inside b p.finish))
  simp only [LinearEquiv.trans_apply, overlap_apply, Gauge.transition]
  rw [p.decode]
  have hh := p.decode g h v
  field_simp [g'.nonzero _ (s.inside a p.start), h'.nonzero _ (s.inside b p.finish),
    h.nonzero _ (s.inside b p.finish)] at *
  linear_combination -hh

end Charting

/-- A full path retains its original segments and a charting for each. -/
inductive AtlasPath : {x y : Disk} → DiskTransport.Path x y → Type
  | nil (x : Disk) : AtlasPath (.nil x)
  | cons {x y z : Disk} {s : Segment x y} {p : DiskTransport.Path y z}
      (c : Charting s 0 s.duration) (rest : AtlasPath p) : AtlasPath (.cons s p)

namespace AtlasPath
variable {x y : Disk} {p : DiskTransport.Path x y}

def transport : {x y : Disk} → {p : DiskTransport.Path x y} → AtlasPath p → ℂ ≃ₗ[ℝ] ℂ
  | _, _, _, .nil _ => LinearEquiv.refl ℝ ℂ
  | _, _, _, .cons c r => c.physical.trans r.transport

theorem agreement (c : AtlasPath p) : c.transport = p.transport := by
  induction c with
  | nil => rfl
  | cons c r ih => simp only [transport, Path.transport, c.full_agreement, ih]

theorem independent (c d : AtlasPath p) : c.transport = d.transport :=
  c.agreement.trans d.agreement.symm

def clock (_c : AtlasPath p) : ℝ := p.duration

theorem clock_agreement (c : AtlasPath p) : c.clock = p.duration := rfl

theorem clock_independent (c d : AtlasPath p) : c.clock = d.clock := rfl

theorem terminal_frame (c : AtlasPath p) (q : Pose) (hq : q.a = x.val) (v : ℂ) :
    (p.terminalPose q hq).frame v = c.transport (q.frame v) := by
  rw [c.agreement]
  exact p.terminal_frame q hq v

def closed {x : Disk} (l : Path.ClosedLift x) (c : AtlasPath l.path) (v : ℂ) : ℂ :=
  (l.label.val : ℂ) * c.transport v

theorem closed_agreement {x : Disk} (l : Path.ClosedLift x) (c : AtlasPath l.path) :
    closed l c = l.endomorphism := by
  funext v
  simp only [closed, c.agreement, Path.ClosedLift.endomorphism]

end AtlasPath
end Orbifold.FrameGauge

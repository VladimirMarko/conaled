import Applications.Orbifold.TransportFrames

/-! Local frame coordinates for the disk connection. The coefficient is derived
from the product rule; no transport comparison is a field of the data. -/
noncomputable section
open Set
open scoped ComplexConjugate ContDiff
namespace Orbifold.FrameGauge
open DiskConnection DiskTransport

structure Gauge where
  frame : ℂ → ℂ
  smooth : ContDiff ℝ ∞ frame
  differential : ℂ → ℂ → ℂ
  nonzero : ∀ z, Complex.normSq z < 1 → frame z ≠ 0
  derivative : ∀ {c : ℝ → ℂ} {v : ℂ} {t : ℝ}, HasDerivAt c v t →
    HasDerivAt (fun s => frame (c s)) (differential (c t) v) t

/-- If physical v = e a, then a' = -(k + e'/e) a. -/
def Gauge.connection (g : Gauge) (z v : ℂ) : ℂ :=
  coefficient z v + g.differential z v / g.frame z

def Gauge.transition (g h : Gauge) (z : ℂ) : ℂ := g.frame z / h.frame z

theorem transition_self (g : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    g.transition g z = 1 := div_self (g.nonzero z hz)

theorem transition_comp (f g h : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    g.transition h z * f.transition g z = f.transition h z := by
  unfold Gauge.transition
  field_simp [g.nonzero z hz, h.nonzero z hz]

theorem transition_inverse (g h : Gauge) (z : ℂ) (hz : Complex.normSq z < 1) :
    h.transition g z * g.transition h z = 1 := by
  rw [transition_comp g h g z hz, transition_self g z hz]

/-- Differentiate the actual decoded field, including the frame derivative. -/
theorem decode_parallel (g : Gauge) {c a : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (hz : Complex.normSq (c t) < 1)
    (ha : HasDerivAt a (-g.connection (c t) v * a t) t) :
    HasDerivAt (fun s => g.frame (c s) * a s)
      (-coefficient (c t) v * (g.frame (c t) * a t)) t := by
  convert (g.derivative hc).mul ha using 1
  unfold Gauge.connection
  field_simp [g.nonzero _ hz]
  <;> ring

/-- Encode an independently supplied physical parallel field. -/
theorem encode_parallel (g : Gauge) {c w : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (hz : Complex.normSq (c t) < 1)
    (hw : HasDerivAt w (-coefficient (c t) v * w t) t) :
    HasDerivAt (fun s => w s / g.frame (c s))
      (-g.connection (c t) v * (w t / g.frame (c t))) t := by
  convert hw.div (g.derivative hc) (g.nonzero _ hz) using 1
  unfold Gauge.connection
  field_simp [g.nonzero _ hz]
  <;> ring

/-- The nonvanishing local fundamental solution is obtained by dividing the
physical scalar solution by the frame, not by postulating endpoint agreement. -/
def factor (g : Gauge) {x y : Disk} (s : Segment x y) (t : ℝ) : ℂ :=
  s.factor t / g.frame (s.curve t)

theorem factor_nonzero (g : Gauge) {x y : Disk} (s : Segment x y)
    {t : ℝ} (ht : t ∈ Icc 0 s.duration) : factor g s t ≠ 0 :=
  div_ne_zero (s.nonzero t ht) (g.nonzero _ (s.inside t ht))

theorem factor_equation (g : Gauge) {x y : Disk} (s : Segment x y)
    {t : ℝ} (ht : t ∈ Icc 0 s.duration) :
    HasDerivAt (factor g s) (-g.connection (s.curve t) (s.velocity t) * factor g s t) t :=
  encode_parallel g (s.derivative t ht) (s.inside t ht) (s.equation t ht)

/-- Local transport between two witnessed times of a segment. -/
def localTransport (g : Gauge) {x y : Disk} (s : Segment x y) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration) : ℂ ≃ₗ[ℝ] ℂ :=
  ParallelTransport.scalar (factor g s) a b (factor_nonzero g s ha) (factor_nonzero g s hb)

theorem local_unique (g : Gauge) {x y : Disk} (s : Segment x y) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
    (hab : a ≤ b) (w : ℝ → ℂ)
    (hw : ∀ t ∈ Icc a b,
      HasDerivAt w (-g.connection (s.curve t) (s.velocity t) * w t) t) :
    w b = localTransport g s a b ha hb (w a) := by
  apply ParallelTransport.scalar_unique
    (fun t ht => factor_nonzero g s ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
    (fun t ht => factor_equation g s ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩) hw
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩)

/-- Local uniqueness holds throughout the interval, not only at its endpoint. -/
theorem local_field_unique (g : Gauge) {x y : Disk} (s : Segment x y) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration)
    (u w : ℝ → ℂ)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (-g.connection (s.curve t) (s.velocity t) * u t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (-g.connection (s.curve t) (s.velocity t) * w t) t)
    (h0 : u a = w a) {t : ℝ} (ht : t ∈ Icc a b) : u t = w t := by
  have hi : t ∈ Icc 0 s.duration := ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
  rw [local_unique g s a t ha hi ht.1 u (fun r hr => hu r ⟨hr.1, hr.2.trans ht.2⟩),
    local_unique g s a t ha hi ht.1 w (fun r hr => hw r ⟨hr.1, hr.2.trans ht.2⟩), h0]


theorem local_decode (g : Gauge) {x y : Disk} (s : Segment x y) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration) (v : ℂ) :
    g.frame (s.curve b) * localTransport g s a b ha hb v =
      s.factor b / s.factor a * (g.frame (s.curve a) * v) := by
  simp only [localTransport, ParallelTransport.scalar_apply, factor]
  field_simp [g.nonzero _ (s.inside a ha), g.nonzero _ (s.inside b hb), s.nonzero a ha]
  <;> ring

/-- Explicit local frame square. Its equations were established by product-rule
compatibility and a constructed unique local solution above. -/
theorem local_change (g h : Gauge) {x y : Disk} (s : Segment x y) (a b : ℝ)
    (ha : a ∈ Icc 0 s.duration) (hb : b ∈ Icc 0 s.duration) (v : ℂ) :
    g.transition h (s.curve b) * localTransport g s a b ha hb v =
      localTransport h s a b ha hb (g.transition h (s.curve a) * v) := by
  simp only [Gauge.transition, localTransport, ParallelTransport.scalar_apply, factor]
  field_simp [g.nonzero _ (s.inside a ha), g.nonzero _ (s.inside b hb),
    h.nonzero _ (s.inside a ha), h.nonzero _ (s.inside b hb), s.nonzero a ha]
  <;> ring

/-- Standard normalized oriented frame, followed by a varying unit phase. -/
def scale (z : ℂ) : ℂ := (gap z : ℂ) / 2
def phase (z : ℂ) : ℂ := Complex.exp ((z.re : ℂ) * Complex.I)
def scaleD (z v : ℂ) : ℂ := -((conj z * v).re : ℂ)

theorem scale_derivative {c : ℝ → ℂ} {v : ℂ} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun t => scale (c t)) (scaleD (c t) v) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative h)).ofReal_comp).div_const 2 using 1
  · rfl
  · simp [scaleD]; ring

theorem phase_derivative {c : ℝ → ℂ} {v : ℂ} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun t => phase (c t)) (((v.re : ℂ) * Complex.I) * phase (c t)) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  convert (hr.ofReal_comp.mul_const Complex.I).cexp using 1
  · rfl
  · simp only [phase, Function.comp_apply, Complex.reCLM_apply]
    ring

theorem scale_smooth : ContDiff ℝ ∞ scale := by
  unfold scale gap
  simp only [Complex.normSq_apply]
  have hr : ContDiff ℝ ∞ (fun z : ℂ => 1 - (z.re * z.re + z.im * z.im)) :=
    contDiff_const.sub ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
  exact (Complex.ofRealCLM.contDiff.comp hr).div_const 2

theorem phase_smooth : ContDiff ℝ ∞ phase := by
  unfold phase
  have hr : ContDiff ℝ ∞ (fun z : ℂ => (z.re : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  exact (hr.mul contDiff_const).cexp

theorem varying_smooth : ContDiff ℝ ∞ (fun z => scale z * phase z) :=
  scale_smooth.mul phase_smooth

def standard : Gauge where
  frame := scale
  smooth := scale_smooth
  differential := scaleD
  nonzero z hz := div_ne_zero (by exact_mod_cast ne_of_gt (sub_pos.mpr hz)) (by norm_num)
  derivative := scale_derivative

def varying : Gauge where
  frame z := scale z * phase z
  smooth := varying_smooth
  differential z v := scaleD z v * phase z + scale z * (((v.re : ℂ) * Complex.I) * phase z)
  nonzero z hz := mul_ne_zero (standard.nonzero z hz) (Complex.exp_ne_zero _)
  derivative h := (scale_derivative h).mul (phase_derivative h)

/-- Both selected frames are normalized for the independently fixed disk metric. -/
theorem standard_metric (z v w : ℂ) (hz : Complex.normSq z < 1) :
    metric z (standard.frame z * v) (standard.frame z * w) = (conj v * w).re := by
  have hg : gap z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have hs : scale z = ((gap z / 2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [metric, standard, hs, map_mul, Complex.conj_ofReal]
  simp [Complex.mul_re, Complex.mul_im]
  field_simp [hg]
  <;> ring

theorem phase_unit (z : ℂ) : Complex.normSq (phase z) = 1 := by
  simp [phase, Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem varying_metric (z v w : ℂ) (hz : Complex.normSq z < 1) :
    metric z (varying.frame z * v) (varying.frame z * w) = (conj v * w).re := by
  change metric z (scale z * phase z * v) (scale z * phase z * w) = _
  rw [mul_assoc, mul_assoc]
  change metric z (standard.frame z * (phase z * v)) (standard.frame z * (phase z * w)) = _
  rw [standard_metric z (phase z * v) (phase z * w) hz]
  have hp : conj (phase z) * phase z = 1 := by
    rw [mul_comm, Complex.mul_conj, phase_unit]; norm_num
  rw [map_mul, show conj (phase z) * conj v * (phase z * w) =
    (conj (phase z) * phase z) * (conj v * w) by ring, hp, one_mul]

/-- The extra term is not optional, even though both frames have the same norm. -/
theorem varying_connection (z v : ℂ) (hz : Complex.normSq z < 1) :
    varying.connection z v = standard.connection z v + (v.re : ℂ) * Complex.I := by
  unfold Gauge.connection varying standard
  dsimp
  have hs : scale z ≠ 0 := standard.nonzero z hz
  have hp : phase z ≠ 0 := Complex.exp_ne_zero _
  field_simp [hs, hp]
  <;> ring

theorem unchanged_connection_rejected : varying.connection 0 1 ≠ standard.connection 0 1 := by
  rw [varying_connection 0 1 (by norm_num)]
  simp

theorem transition_standard_varying (z : ℂ) (hz : Complex.normSq z < 1) :
    standard.transition varying z = (phase z)⁻¹ := by
  change scale z / (scale z * phase z) = _
  have hs : scale z ≠ 0 := standard.nonzero z hz
  have hp : phase z ≠ 0 := Complex.exp_ne_zero _
  field_simp [hs, hp]

/-- The atlas is an actual open cover; no chart is the whole disk. -/
def chartDomain : Bool → Set ℂ
  | false => {z | z.re < 1 / 2}
  | true => {z | -(1 / 2) < z.re}

def chart : Bool → Gauge | false => standard | true => varying

theorem chart_open (i : Bool) : IsOpen (chartDomain i) := by
  cases i
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem chart_cover (z : ℂ) : ∃ i, z ∈ chartDomain i := by
  by_cases h : z.re < 1 / 2
  · exact ⟨false, h⟩
  · exact ⟨true, by dsimp [chartDomain]; linarith⟩

theorem disk_chart_open (i : Bool) :
    IsOpen ((fun z : Disk => z.val) ⁻¹' chartDomain i) :=
  (chart_open i).preimage continuous_subtype_val

theorem disk_chart_cover (z : Disk) : ∃ i, z.val ∈ chartDomain i := chart_cover z.val

theorem disk_chart_proper (i : Bool) : ∃ z : Disk, z.val ∉ chartDomain i := by
  cases i
  · refine ⟨⟨(3 / 4 : ℂ), (disk_mem _).mpr ?_⟩, ?_⟩ <;>
      norm_num [chartDomain, Complex.normSq_apply]
  · refine ⟨⟨(-3 / 4 : ℂ), (disk_mem _).mpr ?_⟩, ?_⟩ <;>
      norm_num [chartDomain, Complex.normSq_apply]

/-- Even on the chart overlap the transition cannot be constant. The test
uses its nonzero derivative along the real axis at the origin. -/
theorem transition_nonconstant :
    ¬ ∃ k : ℂ, ∀ z, Complex.normSq z < 1 →
      z ∈ chartDomain false → z ∈ chartDomain true → standard.transition varying z = k := by
  rintro ⟨k, hk⟩
  have he : (fun t : ℝ => (phase (t : ℂ))⁻¹) =ᶠ[nhds 0] (fun _ => k) := by
    filter_upwards [Ioo_mem_nhds (show -(1 / 2 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    have hz : Complex.normSq (t : ℂ) < 1 := by
      simp only [Complex.normSq_ofReal]
      nlinarith [ht.1, ht.2]
    rw [← transition_standard_varying _ hz]
    exact hk _ hz ht.2 ht.1
  have hd := (phase_derivative ((hasDerivAt_id (0 : ℝ)).ofReal_comp)).inv
    (Complex.exp_ne_zero _)
  have hc := he.hasDerivAt_iff.mp hd
  have hzero := hc.unique (hasDerivAt_const (0 : ℝ) k)
  norm_num [phase] at hzero

end Orbifold.FrameGauge

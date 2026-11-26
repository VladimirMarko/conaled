import Applications.AD.SecondOrderAt
import Applications.Orbifold.Kinetic.Legendre
import Applications.Orbifold.Kinetic.Controls

/-! Local compositional AD for the midpoint action and its quartic control. -/
noncomputable section
open scoped ContDiff Topology
namespace Examples.KineticAD
open Orbifold.Kinetic Orbifold.DiskConnection
open Applications.AD

def actionParts (h : ℝ) (p : ℂ × ℂ) : ℝ × ℝ :=
  (2 * Complex.normSq (p.2-p.1), h * gap (midpoint p.1 p.2)^2)

def quotient (p : ℝ × ℝ) : ℝ := p.1 / p.2

theorem actionParts_smooth (h : ℝ) : ContDiff ℝ ∞ (actionParts h) :=
  (contDiff_const.mul (normSq_smooth.comp (contDiff_snd.sub contDiff_fst))).prodMk
    (contDiff_const.mul ((gap_smooth.comp midpoint_smooth).pow 2))

theorem quotient_smooth (p : ℝ × ℝ) (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ quotient p := contDiffAt_fst.div contDiffAt_snd hp

theorem action_compositional (h : ℝ) (p v : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    SecondOrderAt.lift (fun q : ℂ × ℂ => discrete h q.1 q.2) (p,v) =
      SecondOrderAt.lift quotient (SecondOrderAt.lift (actionParts h) (p,v)) :=
  SecondOrderAt.lift_comp (actionParts h) quotient p v
    ((actionParts_smooth h).differentiable (by simp) p)
    ((quotient_smooth _ (mul_ne_zero hh (pow_ne_zero 2 hg))).differentiableAt (by simp))

theorem action_twice_compositional (h : ℝ) (p v u w : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    SecondOrderAt.twice (fun q : ℂ × ℂ => discrete h q.1 q.2) ((p,v),(u,w)) =
      SecondOrderAt.twice quotient (SecondOrderAt.twice (actionParts h) ((p,v),(u,w))) :=
  SecondOrderAt.twice_comp (actionParts h) quotient p v u w
    (actionParts_smooth h).contDiffAt
    (quotient_smooth _ (mul_ne_zero hh (pow_ne_zero 2 hg)))

/-- Recover the vector representing the first endpoint covector from two AD directions. -/
def firstMomentum (h : ℝ) (x y : ℂ) : ℂ :=
  ⟨(SecondOrderAt.lift (fun z => discrete h z y) (x,1)).2,
   (SecondOrderAt.lift (fun z => discrete h z y) (x,Complex.I)).2⟩

def secondMomentum (h : ℝ) (x y : ℂ) : ℂ :=
  ⟨(SecondOrderAt.lift (discrete h x) (y,1)).2,
   (SecondOrderAt.lift (discrete h x) (y,Complex.I)).2⟩

theorem firstMomentum_eq (h : ℝ) (x y : ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint x y) ≠ 0) : firstMomentum h x y = d1 h x y := by
  apply Complex.ext <;> simp [firstMomentum, SecondOrderAt.lift, (discrete_d1 h x y hh hg).fderiv,
    covector]

theorem secondMomentum_eq (h : ℝ) (x y : ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint x y) ≠ 0) : secondMomentum h x y = d2 h x y := by
  apply Complex.ext <;> simp [secondMomentum, SecondOrderAt.lift, (discrete_d2 h x y hh hg).fderiv,
    covector]

theorem action_smooth (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => discrete h q.1 q.2) p :=
  (quotient_smooth _ (mul_ne_zero hh (pow_ne_zero 2 hg))).comp p
    (actionParts_smooth h).contDiffAt

theorem directional_first (h : ℝ) (p : ℂ × ℂ) (v : ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    fderiv ℝ (fun q : ℂ × ℂ => discrete h q.1 q.2) p (v,0) = covector (d1 h p.1 p.2) v := by
  have hd := ((action_smooth h p hh hg).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp p.1 ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
    (hasFDerivAt_const p.2 p.1))
  have he := hc.unique (discrete_d1 h p.1 p.2 hh hg)
  have ev := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) he
  simpa using ev

theorem gap_eventually (p : ℂ × ℂ) (hg : gap (midpoint p.1 p.2) ≠ 0) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 p, gap (midpoint q.1 q.2) ≠ 0 :=
  (gap_smooth.comp midpoint_smooth).continuous.continuousAt.eventually_ne hg

theorem firstMomentum_eventually (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    (fun q : ℂ × ℂ => firstMomentum h q.1 q.2) =ᶠ[𝓝 p]
      (fun q => d1 h q.1 q.2) := by
  filter_upwards [gap_eventually p hg] with q hq
  exact firstMomentum_eq h q.1 q.2 hh hq

theorem secondMomentum_eventually (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    (fun q : ℂ × ℂ => secondMomentum h q.1 q.2) =ᶠ[𝓝 p]
      (fun q => d2 h q.1 q.2) := by
  filter_upwards [gap_eventually p hg] with q hq
  exact secondMomentum_eq h q.1 q.2 hh hq

theorem firstMomentum_diagonal (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (fun p : ℂ × ℂ => firstMomentum h p.1 p.2)
      (-diagonalScale h x • deltaLinear) (x,x) :=
  (d1_joint_diagonal h x hh hg).congr_of_eventuallyEq
    (firstMomentum_eventually h (x,x) hh (by simpa using hg))

theorem action_mixed_second (h : ℝ) (x u v : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    SecondOrder.second (fun p : ℂ × ℂ => discrete h p.1 p.2) (x,x) (0,u) (v,0) =
      -diagonalScale h x * covector u v := by
  have he : (fun p : ℂ × ℂ =>
      fderiv ℝ (fun q : ℂ × ℂ => discrete h q.1 q.2) p (v,0)) =ᶠ[𝓝 (x,x)]
      (fun p => covector v (d1 h p.1 p.2)) := by
    filter_upwards [gap_eventually (x,x) (by simpa using hg)] with p hp
    rw [directional_first h p v hh hp]
    simp only [covector_apply]
    ring
  have hd := (covector v).hasFDerivAt.comp (x,x) (d1_joint_diagonal h x hh hg)
  have hs := SecondOrderAt.second_of_directional
    (fun p : ℂ × ℂ => discrete h p.1 p.2) (fun p => covector v (d1 h p.1 p.2))
    (x,x) (v,0) (0,u) _ (action_smooth h (x,x) hh (by simpa using hg)) he hd
  rw [hs]
  simp [deltaLinear, covector, add_mul, mul_comm, mul_assoc]

theorem action_twice_mixed (h : ℝ) (x u v : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    (SecondOrderAt.twice (fun p : ℂ × ℂ => discrete h p.1 p.2)
      (((x,x),(v,0)),((0,u),0))).2.2 =
      -diagonalScale h x * covector u v := by
  rw [SecondOrderAt.twice_formula _ _ _ _ _
    (action_smooth h (x,x) hh (by simpa using hg))]
  simpa using action_mixed_second h x u v hh hg

def legendreMinusAD (h : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, -firstMomentum h p.1 p.2)

def legendrePlusAD (h : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.2, secondMomentum h p.1 p.2)

theorem legendreMinusAD_eq (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hp : p ∈ endpointDomain) : legendreMinusAD h p = legendreMinus h p := by
  rw [legendreMinusAD, firstMomentum_eq h p.1 p.2 hh
    (ne_of_gt (sub_pos.mpr (midpoint_inside hp.1 hp.2)))]
  rfl

theorem legendrePlusAD_eq (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hp : p ∈ endpointDomain) : legendrePlusAD h p = legendrePlus h p := by
  rw [legendrePlusAD, secondMomentum_eq h p.1 p.2 hh
    (ne_of_gt (sub_pos.mpr (midpoint_inside hp.1 hp.2)))]
  rfl

theorem minusBranch_domain (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p : ℂ × ℂ}
    (hp : p ∈ (minusBranch h x hh hx).source) : p ∈ endpointDomain := by
  rw [minusBranch, OpenPartialHomeomorph.restr_source' _ _ endpointDomain_open] at hp
  exact hp.2

theorem plusBranch_domain (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p : ℂ × ℂ}
    (hp : p ∈ (plusBranch h x hh hx).source) : p ∈ endpointDomain := by
  rw [plusBranch, OpenPartialHomeomorph.restr_source' _ _ endpointDomain_open] at hp
  exact hp.2

theorem minusBranch_ad_inverse (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p : ℂ × ℂ}
    (hp : p ∈ (minusBranch h x hh hx).source) :
    (minusBranch h x hh hx).symm (legendreMinusAD h p) = p := by
  rw [legendreMinusAD_eq h p (ne_of_gt hh) (minusBranch_domain h x hh hx hp)]
  exact minusBranch_inverse h x hh hx hp

theorem plusBranch_ad_inverse (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p : ℂ × ℂ}
    (hp : p ∈ (plusBranch h x hh hx).source) :
    (plusBranch h x hh hx).symm (legendrePlusAD h p) = p := by
  rw [legendrePlusAD_eq h p (ne_of_gt hh) (plusBranch_domain h x hh hx hp)]
  exact plusBranch_inverse h x hh hx hp

theorem minusBranch_ad_unique (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p q : ℂ × ℂ}
    (hp : p ∈ (minusBranch h x hh hx).source)
    (hq : q ∈ (minusBranch h x hh hx).source)
    (he : legendreMinusAD h p = legendreMinusAD h q) : p = q := by
  rw [legendreMinusAD_eq h p (ne_of_gt hh) (minusBranch_domain h x hh hx hp),
    legendreMinusAD_eq h q (ne_of_gt hh) (minusBranch_domain h x hh hx hq)] at he
  exact minusBranch_unique h x hh hx hp hq he

theorem plusBranch_ad_unique (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) {p q : ℂ × ℂ}
    (hp : p ∈ (plusBranch h x hh hx).source)
    (hq : q ∈ (plusBranch h x hh hx).source)
    (he : legendrePlusAD h p = legendrePlusAD h q) : p = q := by
  rw [legendrePlusAD_eq h p (ne_of_gt hh) (plusBranch_domain h x hh hx hp),
    legendrePlusAD_eq h q (ne_of_gt hh) (plusBranch_domain h x hh hx hq)] at he
  exact plusBranch_unique h x hh hx hp hq he

theorem minusBranch_ad_smooth_inverse (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) :
    ContDiffAt ℝ ∞ (minusBranch h x hh hx).symm (legendreMinusAD h (x,x)) := by
  rw [legendreMinusAD_eq h (x,x) (ne_of_gt hh) ⟨hx,hx⟩]
  exact minus_inverse_smooth h x hh hx

theorem plusBranch_ad_smooth_inverse (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) :
    ContDiffAt ℝ ∞ (plusBranch h x hh hx).symm (legendrePlusAD h (x,x)) := by
  rw [legendrePlusAD_eq h (x,x) (ne_of_gt hh) ⟨hx,hx⟩]
  exact plus_inverse_smooth h x hh hx

def quarticJoint (p : ℝ × ℝ) : ℝ := quartic p.1 p.2

theorem quarticJoint_smooth : ContDiff ℝ ∞ quarticJoint :=
  (contDiff_snd.sub contDiff_fst).pow 4

theorem quartic_twice_compositional :
    SecondOrder.twice quarticJoint quarticJoint_smooth =
      SecondOrder.twice (fun z : ℝ => z^4) (contDiff_id.pow 4) ∘
        SecondOrder.twice (fun p : ℝ × ℝ => p.2-p.1) (contDiff_snd.sub contDiff_fst) :=
  SecondOrder.twice_comp _ _ (contDiff_snd.sub contDiff_fst) (contDiff_id.pow 4)

theorem quartic_directional_first (p : ℝ × ℝ) :
    fderiv ℝ quarticJoint p (1,0) = -4*(p.2-p.1)^3 := by
  have hd := (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)).sub
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).pow 4
  rw [show fderiv ℝ quarticJoint p = _ from hd.fderiv]
  simp

theorem quartic_ad_momenta (p : ℝ × ℝ) :
    (SecondOrder.lift quarticJoint quarticJoint_smooth (p,(1,0))).2 =
        -4*(p.2-p.1)^3 ∧
    (SecondOrder.lift quarticJoint quarticJoint_smooth (p,(0,1))).2 =
        4*(p.2-p.1)^3 := by
  constructor
  · exact quartic_directional_first p
  · change fderiv ℝ quarticJoint p (0,1) = _
    have hd := (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)).sub
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).pow 4
    rw [show fderiv ℝ quarticJoint p = _ from hd.fderiv]
    simp

theorem quartic_second_mixed (x y : ℝ) :
    SecondOrder.second quarticJoint (x,y) (0,1) (1,0) = -12*(y-x)^2 := by
  have he : (fun p : ℝ × ℝ => fderiv ℝ quarticJoint p (1,0)) =ᶠ[𝓝 (x,y)]
      (fun p => -4*(p.2-p.1)^3) :=
    Filter.Eventually.of_forall quartic_directional_first
  have hd := ((((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (x,y))).sub
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).pow 3).const_mul (-4)
  have hs := SecondOrderAt.second_of_directional quarticJoint
    (fun p : ℝ × ℝ => -4*(p.2-p.1)^3) (x,y) (1,0) (0,1) _
    quarticJoint_smooth.contDiffAt he hd
  rw [hs]
  simp
  ring

theorem quartic_twice_mixed (x y : ℝ) :
    (SecondOrder.twice quarticJoint quarticJoint_smooth
      (((x,y),(1,0)),((0,1),0))).2.2 = -12*(y-x)^2 := by
  rw [SecondOrder.twice_formula]
  simpa using quartic_second_mixed x y

/-- The exact AD observation vanishes where the existing regularity test fails. -/
theorem quartic_diagonal_control (x : ℝ) :
    (SecondOrder.twice quarticJoint quarticJoint_smooth
      (((x,x),(1,0)),((0,1),0))).2.2 = 0 ∧
    (¬ ∃ e : ℝ ≃L[ℝ] ℝ,
      HasFDerivAt (fun y => -4*(y-x)^3) (e : ℝ →L[ℝ] ℝ) x) := by
  constructor
  · simp [quartic_twice_mixed]
  · exact quartic_mixed_not_invertible x

theorem quartic_recurrence_control (x y z : ℝ) :
    4*(y-x)^3 - 4*(z-y)^3 = 0 ↔ z = 2*y-x := quartic_unique_recurrence x y z

theorem legendreMinusAD_regular (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (legendreMinusAD h)
      (minusBlock (diagonalScale h x) (diagonalScale_nonzero hh hg) :
        (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) (x,x) := by
  apply (minus_derivative h x hh hg).congr_of_eventuallyEq
  filter_upwards [firstMomentum_eventually h (x,x) hh (by simpa using hg)] with p hp
  simp only [legendreMinusAD, legendreMinus, hp]

theorem legendrePlusAD_regular (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (legendrePlusAD h)
      (plusBlock (diagonalScale h x) (diagonalScale_nonzero hh hg) :
        (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) (x,x) := by
  apply (plus_derivative h x hh hg).congr_of_eventuallyEq
  filter_upwards [secondMomentum_eventually h (x,x) hh (by simpa using hg)] with p hp
  simp only [legendrePlusAD, legendrePlus, hp]

/-- At the origin the mixed coefficient is -4 for unit timestep and directions. -/
example : (SecondOrderAt.twice (fun p : ℂ × ℂ => discrete 1 p.1 p.2)
    (((0,0),(1,0)),((0,1),0))).2.2 = -4 := by
  rw [action_twice_mixed 1 0 1 1 (by norm_num) (by norm_num [gap])]
  norm_num [diagonalScale, gap, covector]

example : (SecondOrder.twice quarticJoint quarticJoint_smooth
    (((0,1),(1,0)),((0,1),0))).2.2 = -12 := by
  norm_num [quartic_twice_mixed]

/-- The selected branch is inhabited and recovers its AD-derived observation. -/
example : (minusBranch 1 0 (by norm_num) (by norm_num)).symm
    (legendreMinusAD 1 (0,0)) = (0,0) :=
  minusBranch_ad_inverse 1 0 (by norm_num) (by norm_num)
    (minusBranch_contains 1 0 (by norm_num) (by norm_num))

end Examples.KineticAD

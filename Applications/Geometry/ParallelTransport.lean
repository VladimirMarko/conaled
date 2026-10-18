import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Squares

/-! Experimental parallel equations in a fixed vector-space chart.
Scalar fundamental solutions construct transport; no transport laws are input
fields. The comparison theorem applies to arbitrary real normed vector spaces. -/
noncomputable section
open Set
namespace ParallelTransport

/-- Transport from a nonvanishing scalar fundamental solution. -/
def scalar (q : ℝ → ℂ) (a b : ℝ) (ha : q a ≠ 0) (hb : q b ≠ 0) : ℂ ≃ₗ[ℝ] ℂ where
  toFun v := q b / q a * v
  invFun v := q a / q b * v
  left_inv v := by field_simp <;> ring
  right_inv v := by field_simp <;> ring
  map_add' v w := by ring
  map_smul' r v := by simp [Complex.real_smul]; ring

@[simp] theorem scalar_apply (q : ℝ → ℂ) (a b : ℝ) (ha hb) (v : ℂ) :
    scalar q a b ha hb v = q b / q a * v := rfl

@[simp] theorem scalar_self (q : ℝ → ℂ) (a : ℝ) (ha) :
    scalar q a a ha ha = LinearEquiv.refl ℝ ℂ := by
  ext v; simp [scalar, ha]

theorem scalar_comp (q : ℝ → ℂ) (a b c : ℝ) (ha hb hc) :
    (scalar q a b ha hb).trans (scalar q b c hb hc) = scalar q a c ha hc := by
  ext v; simp only [LinearEquiv.trans_apply, scalar_apply]
  field_simp

theorem scalar_reverse (q : ℝ → ℂ) (a b : ℝ) (ha hb) :
    scalar q b a hb ha = (scalar q a b ha hb).symm := rfl

/-- The coefficient is the connection contracted against path velocity. -/
theorem scalar_solves {q k : ℝ → ℂ} {a t : ℝ}
    (hq : HasDerivAt q (-k t * q t) t) (v : ℂ) :
    HasDerivAt (fun s => q s / q a * v) (-k t * (q t / q a * v)) t := by
  convert (hq.div_const (q a)).mul_const v using 1 <;> ring

/-- An integrating factor proves uniqueness on the entire closed interval,
including its endpoint values. No global existence theorem is assumed. -/
theorem scalar_unique {q k w : ℝ → ℂ} {a b : ℝ}
    (hn : ∀ t ∈ Icc a b, q t ≠ 0)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (-k t * q t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (-k t * w t) t)
    {t : ℝ} (ht : t ∈ Icc a b) : w t = q t / q a * w a := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (fun r => w r / q r) 0 s := by
    intro s hs
    convert (hw s hs).div (hq s hs) (hn s hs) using 1 <;> ring
  have he := constant_of_has_deriv_right_zero
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (mem_Icc_of_Ico hs)).hasDerivWithinAt) t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  apply (div_eq_iff (hn t ht)).mp at he
  rw [he]; ring

section Comparison
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Concrete coordinate preservation along a path: the derivative of the
coordinate tangent map plus the target coefficient equals the pushed source
coefficient. This is a connection equation, not a transport square. -/
def PreservesAlong (A : ℝ → E →L[ℝ] E) (B : ℝ → F →L[ℝ] F)
    (J J' : ℝ → E →L[ℝ] F) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ v, J' t v + B t (J t v) = J t (A t v)

/-- The product rule sends parallel fields to parallel fields. For a coordinate
map `phi`, use `J(t)=D phi(c(t))` and its derivative along `c`. -/
theorem map_parallel {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F}
    {J J' : ℝ → E →L[ℝ] F} {s : Set ℝ}
    (hp : PreservesAlong A B J J' s) {v : ℝ → E} {t : ℝ} (ht : t ∈ s)
    (hJ : HasDerivAt J (J' t) t) (hv : HasDerivAt v (-A t (v t)) t) :
    HasDerivAt (fun r => J r (v r)) (-B t (J t (v t))) t := by
  convert hJ.clm_apply hv using 1
  have h := hp t ht (v t)
  simp only [Function.comp_apply, map_neg]
  rw [eq_sub_of_add_eq h]
  abel

/-- Uniqueness turns concrete connection preservation into the transport square.
The target uniqueness hypothesis can be supplied by `scalar_unique` in a chart
or by an ODE uniqueness theorem in another vector space. -/
theorem comparison {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F}
    {J J' : ℝ → E →L[ℝ] F} {s : Set ℝ} {a b : ℝ}
    {v : ℝ → E} {w : ℝ → F}
    (hp : PreservesAlong A B J J' s)
    (hJ : ∀ t ∈ s, HasDerivAt J (J' t) t)
    (hv : ∀ t ∈ s, HasDerivAt v (-A t (v t)) t)
    (hw : ∀ t ∈ s, HasDerivAt w (-B t (w t)) t)
    (hi : J a (v a) = w a)
    (unique : ∀ f g : ℝ → F,
      (∀ t ∈ s, HasDerivAt f (-B t (f t)) t) →
      (∀ t ∈ s, HasDerivAt g (-B t (g t)) t) → f a = g a → f b = g b) :
    J b (v b) = w b :=
  unique _ _ (fun t ht => map_parallel hp ht (hJ t ht) (hv t ht)) hw hi

/-- Coordinate preservation expressed by the Christoffel transformation formula.
`dphi` and `ddphi` are separately required to be actual derivatives below. -/
def PreservesConnection (G : E → E → E →L[ℝ] E) (H : F → F → F →L[ℝ] F)
    (phi : E → F) (dphi : E → E →L[ℝ] F)
    (ddphi : E → E →L[ℝ] (E →L[ℝ] F)) (U : Set E) : Prop :=
  ∀ z ∈ U, ∀ u v, ddphi z u v + H (phi z) (dphi z u) (dphi z v) = dphi z (G z u v)

/-- Chain rule and the Christoffel transformation formula give the pathwise
connection identity for actual coordinate derivatives. -/
theorem coordinate_parallel
    {G : E → E → E →L[ℝ] E} {H : F → F → F →L[ℝ] F}
    {phi : E → F} {dphi : E → E →L[ℝ] F}
    {ddphi : E → E →L[ℝ] (E →L[ℝ] F)} {U : Set E}
    (hp : PreservesConnection G H phi dphi ddphi U)
    {c v : ℝ → E} {u : E} {t : ℝ} (hcU : c t ∈ U)
    (hc : HasDerivAt c u t)
    (hphi : HasFDerivAt phi (dphi (c t)) (c t))
    (hdphi : HasFDerivAt dphi (ddphi (c t)) (c t))
    (hv : HasDerivAt v (-G (c t) u (v t)) t) :
    HasDerivAt (phi ∘ c) (dphi (c t) u) t ∧
    HasDerivAt (fun r => dphi (c r) (v r))
      (-H (phi (c t)) (dphi (c t) u) (dphi (c t) (v t))) t := by
  refine ⟨hphi.comp_hasDerivAt t hc, ?_⟩
  have hh := (hdphi.comp_hasDerivAt t hc).clm_apply hv
  convert hh using 1
  · rfl
  · have he := hp (c t) hcU u (v t)
    simp only [Function.comp_apply, map_neg]
    rw [eq_sub_of_add_eq he]
    abel

/-- Transport commutes with a connection-preserving coordinate map wherever
both solution families are constructed and the target equation is unique.
No inverse for `phi` is needed, so coordinate diffeomorphisms are a specialization. -/
theorem coordinate_transport
    {G : E → E → E →L[ℝ] E} {H : F → F → F →L[ℝ] F}
    {phi : E → F} {dphi : E → E →L[ℝ] F}
    {ddphi : E → E →L[ℝ] (E →L[ℝ] F)} {U : Set E}
    (hp : PreservesConnection G H phi dphi ddphi U)
    {c velocity : ℝ → E} {s : Set ℝ} {a b : ℝ}
    (hcU : ∀ t ∈ s, c t ∈ U) (hc : ∀ t ∈ s, HasDerivAt c (velocity t) t)
    (hphi : ∀ z ∈ U, HasFDerivAt phi (dphi z) z)
    (hdphi : ∀ z ∈ U, HasFDerivAt dphi (ddphi z) z)
    (P : E → ℝ → E) (Q : F → ℝ → F)
    (hP : ∀ v t, t ∈ s → HasDerivAt (P v) (-G (c t) (velocity t) (P v t)) t)
    (hQ : ∀ w t, t ∈ s → HasDerivAt (Q w)
      (-H (phi (c t)) (dphi (c t) (velocity t)) (Q w t)) t)
    (iP : ∀ v, P v a = v) (iQ : ∀ w, Q w a = w)
    (unique : ∀ f g : ℝ → F,
      (∀ t ∈ s, HasDerivAt f (-H (phi (c t)) (dphi (c t) (velocity t)) (f t)) t) →
      (∀ t ∈ s, HasDerivAt g (-H (phi (c t)) (dphi (c t) (velocity t)) (g t)) t) →
      f a = g a → f b = g b) (v : E) :
    dphi (c b) (P v b) = Q (dphi (c a) v) b := by
  apply unique (fun t => dphi (c t) (P v t)) (Q (dphi (c a) v))
  · intro t ht
    exact (coordinate_parallel hp (hcU t ht) (hc t ht)
      (hphi _ (hcU t ht)) (hdphi _ (hcU t ht)) (hP v t ht)).2
  · exact hQ _
  · rw [iP, iQ]

end Comparison
/-- The coefficient in new linear coordinates. -/
def conjugateCoefficient (L : ℂ ≃L[ℝ] ℂ) (k : ℂ) : ℂ →L[ℝ] ℂ :=
  L.toContinuousLinearMap.comp ((ContinuousLinearMap.mul ℝ ℂ k).comp L.symm.toContinuousLinearMap)

/-- Uniqueness survives a real-linear coordinate change, including anisotropic
stretching. It is proved by pulling the equation back, not assumed as a law. -/
theorem conjugate_unique (L : ℂ ≃L[ℝ] ℂ) {q k w : ℝ → ℂ} {a b : ℝ}
    (hn : ∀ t ∈ Icc a b, q t ≠ 0)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (-k t * q t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (-conjugateCoefficient L (k t) (w t)) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    w t = L (q t / q a * L.symm (w a)) := by
  have hh : ∀ s ∈ Icc a b,
      HasDerivAt (fun s => L.symm (w s)) (-k s * L.symm (w s)) s := by
    intro s hs
    convert L.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hw s hs) using 1
    · rfl
    · simp [conjugateCoefficient, neg_mul]
  have he := scalar_unique hn hq hh ht
  exact L.symm.injective (by simpa using he)

/-- Endpoint comparison obtained from the generic connection comparison and
proved uniqueness, for any independently supplied solution in new coordinates. -/
theorem linear_comparison (L : ℂ ≃L[ℝ] ℂ) {q k w : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hn : ∀ t ∈ Icc a b, q t ≠ 0)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (-k t * q t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (-conjugateCoefficient L (k t) (w t)) t)
    (v : ℂ) (hi : w a = L v) :
    L (q b / q a * v) = w b := by
  apply comparison (A := fun t => ContinuousLinearMap.mul ℝ ℂ (k t))
    (B := fun t => conjugateCoefficient L (k t))
    (J := fun _ => L.toContinuousLinearMap) (J' := fun _ => 0)
    (s := Icc a b) (a := a) (v := fun t => q t / q a * v)
  · intro t ht u; simp [conjugateCoefficient]
  · intro t ht; exact hasDerivAt_const t _
  · intro t ht; simpa only [ContinuousLinearMap.mul_apply', neg_mul] using scalar_solves (a := a) (hq t ht) v
  · exact hw
  · simpa [hn a ⟨le_rfl, hab⟩] using hi.symm
  · intro f g hf hg h0
    rw [conjugate_unique L hn hq hf ⟨hab, le_rfl⟩,
      conjugate_unique L hn hq hg ⟨hab, le_rfl⟩, h0]

end ParallelTransport

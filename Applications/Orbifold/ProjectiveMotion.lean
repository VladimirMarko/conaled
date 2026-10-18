import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Experimental projective motions of a complex sesquilinear space.
The algebra needs neither a dimension nor a signature assumption. Disk geometry
will specialize the form to signature (1,1). All constructions are exact and
noncomputable. Multiplication applies the right operand first. -/

noncomputable section
open scoped ComplexConjugate
namespace Orbifold
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev Form (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ

/-- Positive similitudes, forgetting the redundant choice of scale witness. -/
def similitudes (H : Form V) : Subgroup (V ≃ₗ[ℂ] V) where
  carrier := {L | ∃ c : ℝ, 0 < c ∧ ∀ v w, H (L v) (L w) = (c : ℂ) * H v w}
  one_mem' := ⟨1, zero_lt_one, by simp⟩
  mul_mem' := by
    rintro L K ⟨c, hc, hL⟩ ⟨d, hd, hK⟩
    exact ⟨c * d, mul_pos hc hd, fun v w => by simp [hL, hK, mul_assoc]⟩
  inv_mem' := by
    rintro L ⟨c, hc, hL⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, fun v w => ?_⟩
    have h := hL (L.symm v) (L.symm w)
    simp only [LinearEquiv.apply_symm_apply] at h
    change H (L.symm v) (L.symm w) = _
    rw [h, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast ne_of_gt hc

abbrev Similitude (H : Form V) := ↥(similitudes H)

namespace Similitude
variable {H : Form V}

theorem preserves (L : Similitude H) :
    ∃ c : ℝ, 0 < c ∧ ∀ v w, H (L.val v) (L.val w) = (c : ℂ) * H v w := L.property

/-- Scalar multiplication scales the form by the positive squared modulus. -/
theorem form_smul (H : Form V) (a : ℂ) (v w : V) :
    H (a • v) (a • w) = (Complex.normSq a : ℂ) * H v w := by
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply,
    smul_eq_mul]
  rw [← mul_assoc, mul_comm (star a) a]
  change a * conj a * H v w = _
  rw [Complex.mul_conj]

def scalar (H : Form V) (a : ℂˣ) : Similitude H :=
  ⟨LinearEquiv.smulOfUnit a, ⟨Complex.normSq a, Complex.normSq_pos.mpr a.ne_zero,
    fun v w => form_smul H a v w⟩⟩

@[simp] theorem scalar_apply (a : ℂˣ) (v : V) : (scalar H a).val v = (a : ℂ) • v := rfl

/-- The central subgroup of nonzero scalar representatives. -/
def scalars (H : Form V) : Subgroup (Similitude H) where
  carrier := Set.range (scalar H)
  one_mem' := ⟨1, by apply Subtype.ext; ext v; simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    apply Subtype.ext; ext v
    simp [← mul_smul, mul_comm]
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    symm
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext; ext v
    simp [← mul_smul]

instance : (scalars H).Normal := Subgroup.normal_of_le_center (by
  rintro L ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro K
  apply Subtype.ext; ext v
  simp)

end Similitude

/-- Motions identify precisely the central scalar redundancy of similitudes. -/
abbrev Motion (H : Form V) := Similitude H ⧸ Similitude.scalars H

def Similitude.motion {H : Form V} : Similitude H →* Motion H :=
  QuotientGroup.mk' _

@[simp] theorem Similitude.motion_scalar {H : Form V} (a : ℂˣ) :
    (scalar H a).motion = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨a, rfl⟩

theorem Similitude.motion_eq_iff {H : Form V} (L K : Similitude H) :
    L.motion = K.motion ↔ ∃ a : ℂˣ, L = Similitude.scalar H a * K := by
  change ((L : Motion H) = (K : Motion H)) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using congrArg (fun x => x * K) ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

/-- Negativity is stated on a representative but is invariant under rescaling. -/
def Negative (H : Form V) (p : Projectivization ℂ V) : Prop :=
  ∃ (v : V) (hv : v ≠ 0), Projectivization.mk ℂ v hv = p ∧ (H v v).re < 0

abbrev NegativeLine (H : Form V) := {p : Projectivization ℂ V // Negative H p}

theorem negative_mk_iff (H : Form V) (v : V) (hv : v ≠ 0) :
    Negative H (Projectivization.mk ℂ v hv) ↔ (H v v).re < 0 := by
  constructor
  · rintro ⟨w, hw, heq, hneg⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ w v hw hv).mp heq
    rw [← ha] at hneg
    change (H ((a : ℂ) • v) ((a : ℂ) • v)).re < 0 at hneg
    rw [Similitude.form_smul] at hneg
    have hp := Complex.normSq_pos.mpr a.ne_zero
    have hn : Complex.normSq (a : ℂ) * (H v v).re < 0 := by simpa using hneg
    nlinarith
  · intro h; exact ⟨v, hv, rfl, h⟩

/-- Restrict Mathlib's linear action to negative lines. -/
def Similitude.act {H : Form V} (L : Similitude H) (p : NegativeLine H) :
    NegativeLine H := by
  refine ⟨L.val • p.val, ?_⟩
  obtain ⟨v, hv, heq, hneg⟩ := p.property
  rw [← heq]
  refine ⟨L.val v, (fun h => hv (L.val.injective (h.trans (map_zero L.val).symm))), rfl, ?_⟩
  obtain ⟨c, hc, hL⟩ := L.preserves
  rw [hL]
  simpa using mul_neg_of_pos_of_neg hc hneg

instance {H : Form V} : MulAction (Similitude H) (NegativeLine H) where
  smul := Similitude.act
  one_smul p := Subtype.ext (one_smul (V ≃ₗ[ℂ] V) p.val)
  mul_smul L K p := Subtype.ext (mul_smul L.val K.val p.val)

/-- Scalars fix every projective point, hence the action descends to motions. -/
theorem scalar_act {H : Form V} (a : ℂˣ) (p : NegativeLine H) :
    Similitude.scalar H a • p = p := by
  apply Subtype.ext
  change (Similitude.scalar H a).val • p.val = p.val
  induction p.val using Projectivization.ind with
  | _ v hv =>
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    exact ⟨a, rfl⟩

def motionAction (H : Form V) : Motion H →* Equiv.Perm (NegativeLine H) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (by
    rintro _ ⟨a, rfl⟩
    apply Equiv.ext
    exact scalar_act a)

instance {H : Form V} : MulAction (Motion H) (NegativeLine H) :=
  MulAction.compHom _ (motionAction H)

@[simp] theorem motion_act {H : Form V} (L : Similitude H) (p : NegativeLine H) :
    L.motion • p = L • p := rfl

/-- The invariant is real; Hermitian symmetry makes the diagonal values real.
Using real parts also defines this algebraic ratio for general sesquilinear forms. -/
def vectorRatio (H : Form V) (v w : V) : ℝ :=
  Complex.normSq (H v w) / ((H v v).re * (H w w).re)

theorem vectorRatio_smul (H : Form V) (a b : ℂˣ) (v w : V) :
    vectorRatio H ((a : ℂ) • v) ((b : ℂ) • w) = vectorRatio H v w := by
  unfold vectorRatio
  rw [Similitude.form_smul, Similitude.form_smul]
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply,
    smul_eq_mul, map_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hs : Complex.normSq (star (a : ℂ)) = Complex.normSq (a : ℂ) := Complex.normSq_conj _
  rw [hs]
  have ha := Complex.normSq_pos.mpr a.ne_zero
  have hb := Complex.normSq_pos.mpr b.ne_zero
  field_simp

theorem vectorRatio_preserved {H : Form V} (L : Similitude H) (v w : V) :
    vectorRatio H (L.val v) (L.val w) = vectorRatio H v w := by
  obtain ⟨c, hc, hL⟩ := L.preserves
  unfold vectorRatio
  simp only [hL, map_mul, Complex.normSq_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have : c ≠ 0 := ne_of_gt hc
  field_simp

/-- A representative-independent ratio on negative projective lines. -/
def ratio (H : Form V) (p q : NegativeLine H) : ℝ :=
  vectorRatio H p.val.rep q.val.rep

theorem ratio_eq (H : Form V) (p q : NegativeLine H) (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hp : Projectivization.mk ℂ v hv = p.val)
    (hq : Projectivization.mk ℂ w hw = q.val) :
    ratio H p q = vectorRatio H v w := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ p.val.rep_nonzero hv).mp
    ((Projectivization.mk_rep p.val).trans hp.symm)
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ q.val.rep_nonzero hw).mp
    ((Projectivization.mk_rep q.val).trans hq.symm)
  unfold ratio
  rw [← ha, ← hb]
  exact vectorRatio_smul H a b v w

theorem ratio_preserved (H : Form V) (g : Motion H) (p q : NegativeLine H) :
    ratio H (g • p) (g • q) = ratio H p q := by
  obtain ⟨L, rfl⟩ := QuotientGroup.mk'_surjective (Similitude.scalars H) g
  change ratio H (L • p) (L • q) = ratio H p q
  rw [ratio_eq H (L • p) (L • q) (L.val p.val.rep) (L.val q.val.rep)
    (by simpa using L.val.injective.ne p.val.rep_nonzero)
    (by simpa using L.val.injective.ne q.val.rep_nonzero)]
  · exact vectorRatio_preserved L _ _
  · change Projectivization.mk ℂ (L.val p.val.rep) _ = L.val • p.val
    simpa only [Projectivization.smul_mk, LinearEquiv.smul_def] using congrArg (fun x : Projectivization ℂ V => L.val • x)
      (Projectivization.mk_rep _)
  · change Projectivization.mk ℂ (L.val q.val.rep) _ = L.val • q.val
    simpa only [Projectivization.smul_mk, LinearEquiv.smul_def] using congrArg (fun x : Projectivization ℂ V => L.val • x)
      (Projectivization.mk_rep _)

end Orbifold

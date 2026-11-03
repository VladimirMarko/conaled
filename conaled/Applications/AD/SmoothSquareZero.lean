import Applications.AD.SmoothDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Experimental smooth square-zero stages. The nilpotent vector space needs no norm
or topology: only the finite real input space is differentiated. The construction
works for any real vector space, in particular every finite-dimensional one.
Right scalar actions used by Mathlib's extension ring are required to agree with
the real action through `IsCentralScalar`; no basis of the nilpotent space is chosen.
-/

noncomputable section
namespace Applications.AD.SmoothSquareZero
open SmoothDual
open scoped BigOperators

variable {V W U : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

/-- Extend the analytic derivative's finite input coefficients to vector nilpotents. -/
def act {n : ℕ} (f : Operation n) (z : Fin n → TrivSqZeroExt ℝ V) : TrivSqZeroExt ℝ V :=
  ⟨f.val (fun i => (z i).fst),
    ∑ i, (fderiv ℝ f.val (fun j => (z j).fst) (Pi.single i 1)) • (z i).snd⟩

/-- A finite linear functional is determined by its coordinate values. -/
theorem coefficient_sum {n : ℕ} (d : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    (∑ i, d (Pi.single i 1) * v i) = d v := by
  calc
    _ = ∑ i, d (Pi.single i (v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm, ← smul_eq_mul, ← map_smul]
      congr 1
      ext j
      simp [Pi.single_apply]
    _ = d (∑ i, Pi.single i (v i)) := (map_sum d _ _).symm
    _ = d v := by rw [Finset.univ_sum_single]

/-- Exact recovery for every smooth operation, not just ring operations. -/
theorem act_real {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) :
    act f z = SmoothDual.act f z := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact coefficient_sum _ _

section Maps
variable [Module ℝᵐᵒᵖ V] [IsCentralScalar ℝ V]
  [Module ℝᵐᵒᵖ W] [IsCentralScalar ℝ W]
  [Module ℝᵐᵒᵖ U] [IsCentralScalar ℝ U]

/-- The actual real algebra map supplied by Mathlib. -/
abbrev map (L : V →ₗ[ℝ] W) : TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W :=
  TrivSqZeroExt.map L

theorem map_ident : map (LinearMap.id : V →ₗ[ℝ] V) = AlgHom.id ℝ _ :=
  TrivSqZeroExt.map_id

theorem map_comp (L : V →ₗ[ℝ] W) (M : W →ₗ[ℝ] U) :
    map (M.comp L) = (map M).comp (map L) := TrivSqZeroExt.map_comp_map L M

theorem map_act {n : ℕ} (L : V →ₗ[ℝ] W) (f : Operation n)
    (z : Fin n → TrivSqZeroExt ℝ V) :
    map L (act f z) = act f (fun i => map L (z i)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_map]
    simp [act]
  · rw [TrivSqZeroExt.snd_map]
    simp [act]

/-- Scalar observations separate the stages; this does not choose a basis in `act`. -/
theorem observations_ext {a b : TrivSqZeroExt ℝ V}
    (h : ∀ L : V →ₗ[ℝ] ℝ, map L a = map L b) : a = b := by
  apply TrivSqZeroExt.ext
  · simpa using congrArg TrivSqZeroExt.fst (h 0)
  · apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℝ (a.snd - b.snd)).mp
    intro L
    have hh := congrArg TrivSqZeroExt.snd (h L)
    simpa using (sub_eq_zero.mpr (by simpa using hh) : L a.snd - L b.snd = 0)

/-- All real algebra maps preserve the square-zero ideal because ℝ is reduced. -/
theorem hom_inr_fst (h : TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W) (v : V) :
    (h (TrivSqZeroExt.inr v)).fst = 0 := by
  have hz : h (TrivSqZeroExt.inr v) * h (TrivSqZeroExt.inr v) = 0 := by
    rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  have hh := congrArg TrivSqZeroExt.fst hz
  exact mul_self_eq_zero.mp (by simpa using hh)

def linearPart (h : TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W) : V →ₗ[ℝ] W :=
  (TrivSqZeroExt.sndHom ℝ W).comp (h.toLinearMap.comp (TrivSqZeroExt.inrHom ℝ V))

theorem map_linearPart (h : TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W) :
    map (linearPart h) = h := by
  apply TrivSqZeroExt.algHom_ext
  intro v
  apply TrivSqZeroExt.ext
  · simpa using (hom_inr_fst h v).symm
  · simp [linearPart]

theorem linearPart_map (L : V →ₗ[ℝ] W) : linearPart (map L) = L := by
  ext v
  simp [linearPart]

/-- Exactly the compatible stage morphisms, in both directions. -/
def homEquiv : (V →ₗ[ℝ] W) ≃ (TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W) where
  toFun := map
  invFun := linearPart
  left_inv := linearPart_map
  right_inv := map_linearPart

theorem hom_act {n : ℕ} (h : TrivSqZeroExt ℝ V →ₐ[ℝ] TrivSqZeroExt ℝ W)
    (f : Operation n) (z : Fin n → TrivSqZeroExt ℝ V) :
    h (act f z) = act f (fun i => h (z i)) := by
  rw [← map_linearPart h]
  exact map_act _ _ _

/-- The scalar chain rule already proved for dual numbers determines the vector law. -/
theorem act_substitute {m n : ℕ} (f : Operation n) (g : Fin n → Operation m)
    (z : Fin m → TrivSqZeroExt ℝ V) :
    act (substitute f g) z = act f (fun i => act (g i) z) := by
  apply observations_ext
  intro L
  simp only [map_act, act_real, SmoothDual.act_substitute]

theorem act_projection {n : ℕ} (i : Fin n) (z : Fin n → TrivSqZeroExt ℝ V) :
    act (projection i) z = z i := by
  apply observations_ext
  intro L
  rw [map_act, act_real, SmoothDual.act_projection]

theorem act_constant (n : ℕ) (a : ℝ) (z : Fin n → TrivSqZeroExt ℝ V) :
    act (constant n a) z = algebraMap ℝ (TrivSqZeroExt ℝ V) a := by
  apply observations_ext
  intro L
  rw [map_act, act_real, SmoothDual.act_constant, AlgHom.commutes]

theorem act_addition (z : Fin 2 → TrivSqZeroExt ℝ V) :
    act addition z = z 0 + z 1 := by
  apply observations_ext
  intro L
  rw [map_act, act_real, SmoothDual.act_addition, map_add]

theorem act_multiplication (z : Fin 2 → TrivSqZeroExt ℝ V) :
    act multiplication z = z 0 * z 1 := by
  apply observations_ext
  intro L
  rw [map_act, act_real, SmoothDual.act_multiplication, map_mul]

end Maps
end Applications.AD.SmoothSquareZero

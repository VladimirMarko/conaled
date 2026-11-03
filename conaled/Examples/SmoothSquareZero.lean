import Applications.AD.SmoothSquareZero
import Examples.SmoothDual

/-! Experimental multi-direction clients. All nilpotent products vanish, including
mixed directions; the stage cannot record a mixed second derivative. -/

noncomputable section
namespace Examples.SmoothSquareZero
open Applications.AD.SmoothDual (Operation substitute addition multiplication constant)
open Applications.AD.SmoothSquareZero

abbrev Directions := Fin 2 → ℝ
abbrev Stage := TrivSqZeroExt ℝ Directions

def direction (i : Fin 2) : Stage := TrivSqZeroExt.inr (Pi.single i 1)

theorem direction_nonzero (i : Fin 2) : direction i ≠ 0 := by
  intro h
  have hh := congrArg (fun z : Stage => z.snd i) h
  simp [direction] at hh

/-- The two infinitesimal directions are linearly independent. -/
theorem directions_independent (a b : ℝ)
    (h : a • direction 0 + b • direction 1 = 0) : a = 0 ∧ b = 0 := by
  constructor
  · have hh := congrArg (fun z : Stage => z.snd 0) h
    simpa [direction, Pi.single_apply] using hh
  · have hh := congrArg (fun z : Stage => z.snd 1) h
    simpa [direction, Pi.single_apply] using hh

theorem directions_mul (i j : Fin 2) : direction i * direction j = 0 :=
  TrivSqZeroExt.inr_mul_inr _ _ _

/-- Nonidentity change of tangent coordinates. -/
def double : Directions →ₗ[ℝ] Directions := (2 : ℝ) • LinearMap.id

theorem double_not_identity : map double ≠ AlgHom.id ℝ Stage := by
  intro h
  have hh := congrArg (fun k : Stage →ₐ[ℝ] Stage => (k (direction 0)).snd 0) h
  norm_num [double, direction] at hh

theorem double_exponential (z : Fin 1 → Stage) :
    map double (act SmoothDual.exponential z) =
      act SmoothDual.exponential (fun i => map double (z i)) := map_act _ _ _

theorem exponential_formula (x : ℝ) (v : Directions) :
    act SmoothDual.exponential (fun _ => (⟨x, v⟩ : Stage)) =
      (⟨Real.exp x, Real.exp x • v⟩ : Stage) := by
  apply observations_ext
  intro L
  erw [map_act, act_real, SmoothDual.exponential_formula]
  apply TrivSqZeroExt.ext
  · erw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map]
    rfl
  · erw [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map]
    exact (L.map_smul (Real.exp x) v).symm

/-- The old nonzero-direction exponential client is recovered by the general comparison. -/
theorem dual_exponential :
    act SmoothDual.exponential (fun _ => (⟨0, 2⟩ : DualNumber ℝ)) =
      (⟨1, 2⟩ : DualNumber ℝ) := by
  erw [act_real]
  exact SmoothDual.exponential_nonzero_direction

theorem nullary (f : Operation 0) (z : Fin 0 → Stage) :
    act f z = algebraMap ℝ Stage (f.val Fin.elim0) := by
  apply observations_ext
  intro L
  rw [map_act, act_real, SmoothDual.nullary, AlgHom.commutes]

theorem nullary_substitution (a : ℝ) (z : Fin 0 → Stage) :
    act (substitute addition (fun _ => constant 0 a)) z =
      algebraMap ℝ Stage a + algebraMap ℝ Stage a := by
  rw [act_substitute, act_addition, act_constant]

/-- Multiplication evaluated in two independent directions still loses the mixed term. -/
theorem mixed_term_lost :
    act multiplication (fun i => direction i) = 0 := by
  rw [act_multiplication, directions_mul]

/-- The corresponding ordinary mixed derivative is nonzero: this stage has lost information. -/
theorem ordinary_mixed_derivative :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => x * y) 0) 1 0 := by
  have h : (fun y : ℝ => deriv (fun x : ℝ => x * y) 0) = id := by
    funext y
    exact ((hasDerivAt_id (0 : ℝ)).mul_const y).deriv.trans (one_mul y)
  rw [h]
  exact hasDerivAt_id 0

end Examples.SmoothSquareZero

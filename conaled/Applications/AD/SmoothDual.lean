import Applications.AD.Smooth
import SquareKit.SmoothOperations
import Mathlib.Algebra.DualNumber

/-!
Experimental smooth operations on the real dual-number ring. These are finite-arity
operations with projection and substitution laws, not a smooth sheaf model.
-/

noncomputable section
open scoped ContDiff
namespace Applications.AD.SmoothDual

/-- Ordinary smooth functions identify operations extensionally. -/
abbrev Operation := SquareKit.SmoothAlgebra.Operation

def coordinates {n : ℕ} : (Fin n → DualNumber ℝ) ≃ ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun z := (fun i => (z i).fst, fun i => (z i).snd)
  invFun p i := ⟨p.1 i, p.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def scalarCoordinates : DualNumber ℝ ≃ ℝ × ℝ where
  toFun z := (z.fst, z.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The existing tangent construction, expressed in dual-number coordinates. -/
def act {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) : DualNumber ℝ :=
  scalarCoordinates.symm (tangent (DMap.ofSmooth f.val f.property) (coordinates z))

theorem act_coordinates {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) :
    scalarCoordinates (act f z) = tangent (DMap.ofSmooth f.val f.property) (coordinates z) := rfl

theorem act_formula {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) :
    act f z = ⟨f.val (fun i => (z i).fst),
      fderiv ℝ f.val (fun i => (z i).fst) (fun i => (z i).snd)⟩ := rfl

/-- The coordinate formula is an equality in the existing dual-number algebra. -/
theorem act_affine {n : ℕ} (f : Operation n) (z : Fin n → DualNumber ℝ) :
    act f z = algebraMap ℝ (DualNumber ℝ) (f.val (fun i => (z i).fst)) +
      algebraMap ℝ (DualNumber ℝ)
        (fderiv ℝ f.val (fun i => (z i).fst) (fun i => (z i).snd)) * DualNumber.eps := by
  apply TrivSqZeroExt.ext <;> simp [act_formula, TrivSqZeroExt.algebraMap_eq_inl]

/-- Any analytically certified implementation gives the same operation. -/
theorem act_of_dmap {n : ℕ} (f : Operation n) (d : DMap (Fin n → ℝ) ℝ)
    (h : ∀ x, d.primal x = f.val x) (z : Fin n → DualNumber ℝ) :
    act f z = scalarCoordinates.symm (tangent d (coordinates z)) := by
  have hd : DMap.ofSmooth f.val f.property = d := DMap.ext (fun x => (h x).symm)
  unfold act
  rw [hd]

abbrev projection := @SquareKit.SmoothAlgebra.projection
abbrev constant := SquareKit.SmoothAlgebra.constant
abbrev substitute := @SquareKit.SmoothAlgebra.substitute

theorem act_projection {n : ℕ} (i : Fin n) (z : Fin n → DualNumber ℝ) :
    act (projection i) z = z i := by
  rw [act_of_dmap (projection i) (DMap.linear (ContinuousLinearMap.proj i)) (fun _ => rfl)]
  rfl

theorem act_constant (n : ℕ) (a : ℝ) (z : Fin n → DualNumber ℝ) :
    act (constant n a) z = algebraMap ℝ (DualNumber ℝ) a := by
  rw [act_of_dmap (constant n a) (DMap.constant a) (fun _ => rfl)]
  rfl

/-- Arbitrary simultaneous substitution, with no positivity assumptions on either arity. -/
theorem act_substitute {m n : ℕ} (f : Operation n) (g : Fin n → Operation m)
    (z : Fin m → DualNumber ℝ) :
    act (substitute f g) z = act f (fun i => act (g i) z) := by
  rw [act_of_dmap (substitute f g)
    (DMap.comp (DMap.ofSmooth f.val f.property)
      (DMap.tuple (fun i => DMap.ofSmooth (g i).val (g i).property))) (fun _ => rfl)]
  rw [tangent_comp]
  rfl

abbrev addition := SquareKit.SmoothAlgebra.addition
abbrev multiplication := SquareKit.SmoothAlgebra.multiplication

theorem act_addition (z : Fin 2 → DualNumber ℝ) : act addition z = z 0 + z 1 := by
  rw [act_of_dmap addition (DMap.add (DMap.linear (ContinuousLinearMap.proj 0))
    (DMap.linear (ContinuousLinearMap.proj 1))) (fun _ => rfl)]
  rfl

theorem act_multiplication (z : Fin 2 → DualNumber ℝ) :
    act multiplication z = z 0 * z 1 := by
  rw [act_of_dmap multiplication (DMap.mul (DMap.linear (ContinuousLinearMap.proj 0))
    (DMap.linear (ContinuousLinearMap.proj 1))) (fun _ => rfl)]
  apply TrivSqZeroExt.ext
  · rfl
  · change (z 0).fst * (z 1).snd + (z 1).fst * (z 0).snd = _
    simp [mul_comm]

end Applications.AD.SmoothDual

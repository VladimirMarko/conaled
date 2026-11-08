import SquareKit.Numerical.Error
import Applications.Intervals.Arithmetic
import Examples.NumericalMotion

/-! Affine interval analysis and the existing rational disk-motion execution
share error propagation while retaining distinct selected observations. -/
namespace Examples.NumericalError
open _root_.NumericalError
open scoped NNReal

noncomputable def affine (a b : ℝ) (x : ℝ) : ℝ := a*x+b

theorem affine_lipschitz (a : ℝ≥0) (b : ℝ) :
    LipschitzOnWith a (affine a b) Set.univ := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y _
  simp only [Real.dist_eq, affine]
  rw [show (a : ℝ)*x+b-((a : ℝ)*y+b) = a*(x-y) by ring,
    abs_mul, abs_of_nonneg a.coe_nonneg]

/-- Arbitrary implementations and input uncertainty recover the report bound. -/
theorem affine_pipeline (fhat ghat : ℝ → ℝ) (df dg : ℝ≥0)
    (hf : UniformOn Set.univ fhat (affine 2 1) df)
    (hg : UniformOn Set.univ ghat (affine 3 (-2)) dg)
    (xhat x e : ℝ) (he : dist xhat x ≤ e) :
    dist (ghat (fhat xhat)) (6*x+1) ≤ 6*e+3*df+dg := by
  have h := compose (a := ⟨2,df⟩) (b := ⟨3,dg⟩)
    (affine_lipschitz 2 1) hf (affine_lipschitz 3 (-2)) hg
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (Set.mem_univ xhat) (Set.mem_univ x) he
  convert h using 1 <;> simp [affine, Bound.apply, Bound.comp] <;> ring

/-- The concrete chosen implementations satisfy the uniform obligations and
use the reusable composition theorem, including nonzero input uncertainty. -/
theorem selected_affine_bound (x : ℝ) :
    dist (3 * (2 * (x + 1/100) + 1 + 1/10) - 2 + 1/5) (6*x+1) ≤ 14/25 := by
  have h := affine_pipeline (fun z => 2*z+1+1/10) (fun z => 3*z-2+1/5)
    (1/10) (1/5)
    (by intro z _; simp [affine])
    (by intro z _; simp only [affine, Real.dist_eq]; ring_nf; norm_num)
    (x+1/100) x (1/100) (by simp [Real.dist_eq])
  norm_num at h
  exact h

/-- Chosen perturbations attain the amplified bound, refuting bare addition. -/
theorem amplification :
    |(3*((2*(0:ℝ)+1)+1/10)-2+1/5)-(6*0+1)| = 1/2 ∧
    ¬ |(3*((2*(0:ℝ)+1)+1/10)-2+1/5)-(6*0+1)| ≤ 1/10+1/5 := by norm_num

theorem nonexpansive_fails : ¬ dist (affine 2 1 1) (affine 2 1 0) ≤ dist (1:ℝ) 0 := by
  norm_num [affine, Real.dist_eq]
theorem interchange_fails : affine 3 (-2) (affine 2 1 0) ≠ affine 2 1 (affine 3 (-2) 0) := by
  norm_num [affine]

/-- Restricting the domain can certify a smaller sensitivity; applying that
certificate to an input outside the domain is unsound. -/
theorem domain_membership_needed :
    LipschitzOnWith 0 (fun x : ℝ => x) {0} ∧
    ¬ dist (1:ℝ) 0 ≤ (0:ℝ) * dist (1:ℝ) 0 := by
  constructor
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x; subst y
    simp
  · norm_num

open IntervalAnalysis

def intervalAffine (a b : ℚ) (i : Interval) : Interval := add (mul (singleton a) i) (singleton b)

theorem intervalAffine_contains {i : Interval} {x : ℚ} (hx : Contains i x) (a b : ℚ) :
    Contains (intervalAffine a b i) (a*x+b) :=
  add_contains (mul_contains (singleton_contains a) hx) (singleton_contains b)

/-- The bridge preserves rational membership in a real closed interval. -/
theorem contains_cast {i : Interval} {x : ℚ} (hx : Contains i x) :
    (x : ℝ) ∈ Set.Icc (i.lo : ℝ) (i.hi : ℝ) := by
  exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩

/-- Native interval operations retain the report's exact range. -/
theorem affine_range {x : ℚ} (hx : Contains unitBox x) :
    Contains (intervalAffine 3 (-2) (intervalAffine 2 1 unitBox)) (6*x+1) ∧
    intervalAffine 3 (-2) (intervalAffine 2 1 unitBox) = ⟨-5,7⟩ := by
  constructor
  · convert intervalAffine_contains (intervalAffine_contains hx 2 1) 3 (-2) using 1; ring
  · norm_num [intervalAffine, add, mul, IntervalAnalysis.singleton, unitBox]

/-- Symmetric perturbation boxes bound every selected rational implementation. -/
theorem approximate_range (fhat ghat : ℚ → ℚ)
    (hf : ∀ x, |fhat x-(2*x+1)| ≤ 1/10)
    (hg : ∀ x, |ghat x-(3*x-2)| ≤ 1/5)
    {x : ℚ} (hx : Contains unitBox x) : Contains ⟨-11/2,15/2⟩ (ghat (fhat x)) := by
  have h1 : Contains (add (intervalAffine 2 1 unitBox) ⟨-1/10,1/10⟩) (fhat x) := by
    have h := add_contains (intervalAffine_contains hx 2 1) (show Contains ⟨-1/10,1/10⟩ (fhat x-(2*x+1)) from (by simpa [Contains, neg_div] using abs_le.mp (hf x)))
    convert h using 1; ring
  have h2 := add_contains (intervalAffine_contains h1 3 (-2)) (show Contains ⟨-1/5,1/5⟩ (ghat (fhat x)-(3*fhat x-2)) from (by simpa [Contains, neg_div] using abs_le.mp (hg (fhat x))))
  convert h2 using 1
  · norm_num [intervalAffine, add, mul, IntervalAnalysis.singleton, unitBox]
  · ring

/-- The rational enclosure is also a real observation of the chosen execution. -/
theorem approximate_real_range (fhat ghat : ℚ → ℚ)
    (hf : ∀ x, |fhat x-(2*x+1)| ≤ 1/10)
    (hg : ∀ x, |ghat x-(3*x-2)| ≤ 1/5)
    {x : ℚ} (hx : Contains unitBox x) :
    (ghat (fhat x) : ℝ) ∈ Set.Icc (-11/2) (15/2) := by
  have h := contains_cast (approximate_range fhat ghat hf hg hx)
  norm_num at h
  simpa only [Set.mem_Icc, neg_div] using h

theorem enclosure_not_symmetric : Contains unitBox 0 ∧ ¬ Contains (singleton 0) 1 := by
  norm_num [Contains, unitBox, IntervalAnalysis.singleton]

/-- Two actual moving half-steps keep their selected endpoint. Their budget
is the shared affine transformer composed twice, and endpoint adequacy still
comes from the native run theorem (whose step proof uses `propagate`). -/
theorem motion_two_steps :
    Orbifold.DiskTransport.Numerical.Approx NumericalMotion.refinedResult.final
      (NumericalMotion.moveTick.control.decode.trajectory NumericalMotion.initialPose (1/1024)) ∧
    (NumericalMotion.refinedResult.final.error : ℝ) =
      (Bound.comp ⟨1+13/2048,39/2048^2⟩ ⟨1+13/2048,39/2048^2⟩).apply 0 := by
  refine ⟨NumericalMotion.refined_error, ?_⟩
  rw [Orbifold.DiskTransport.Numerical.run_error NumericalMotion.refined_run]
  norm_num [Orbifold.DiskTransport.Numerical.errorAfter,
    Orbifold.DiskTransport.Numerical.budget, NumericalMotion.halfTick,
    NumericalMotion.initial, Bound.comp, Bound.apply]

/-- Equal certificates do not erase distinct selected approximations. -/
theorem same_error_distinct_outputs :
    dist (1/10 : ℝ) 0 = dist (-1/10 : ℝ) 0 ∧ (1/10 : ℝ) ≠ -1/10 := by
  norm_num [Real.dist_eq]

end Examples.NumericalError

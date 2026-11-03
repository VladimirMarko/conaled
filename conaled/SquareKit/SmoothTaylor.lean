import SquareKit.SmoothQuotient
import Mathlib.RingTheory.Ideal.Operations

/-! Experimental Taylor remainder and nilsquare Taylor laws in arbitrary smooth algebras. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra

def derivative {n : ℕ} (f : Operation n) (i : Fin n) : Operation n :=
  ⟨fun x => fderiv ℝ f.val x (Pi.single i 1),
    (f.property.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩

theorem coefficient_diagonal {n : ℕ} (f : Operation n) (i : Fin n) (x : Fin n → ℝ) :
    SmoothHadamard.coefficient f.val i (x,x) = (derivative f i).val x := by
  simp [SmoothHadamard.coefficient, derivative]

variable {A : Type*} [CommRing A] [Algebra ℝ A] [Structure A]

theorem evaluate_coefficient_diagonal {n : ℕ} (f : Operation n) (i : Fin n) (x : Fin n → A) :
    evaluate (Fin.append x x) (differenceCoefficient f i) = act (derivative f i) x := by
  have h : pullback (Fin.append (fun j : Fin n => projection j) (fun j : Fin n => projection j))
      (differenceCoefficient f i) = (show Free n from derivative f i) := by
    apply Subtype.ext
    funext z
    rw [pullback_apply]
    simp only [differenceCoefficient, Fin.append_left, Fin.append_right, projection]
    exact coefficient_diagonal f i z
  have he := congrArg (evaluate x) h
  change act (substitute (differenceCoefficient f i)
    (Fin.append (fun j : Fin n => projection j) (fun j : Fin n => projection j))) x = _ at he
  erw [Structure.substitute] at he
  have ht : (Fin.append x x) = (fun j => act (Fin.append (fun k : Fin n => projection k) (fun k : Fin n => projection k) j) x) := by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right, Structure.projection]
  change act (show Operation (n+n) from differenceCoefficient f i) (Fin.append x x) = _
  rw [ht]
  exact he

/-- The first-order error is in the square of the ordinary difference ideal.
The coefficient differences are themselves factored by the smooth Hadamard theorem. -/
theorem taylor_remainder (I : Ideal A) {n : ℕ} (f : Operation n) (x y : Fin n → A)
    (h : ∀ i, x i - y i ∈ I) :
    act f x - act f y - ∑ i, (x i - y i) * act (derivative f i) y ∈ I * I := by
  rw [act_difference, ← Finset.sum_sub_distrib]
  apply (I * I).sum_mem
  intro i _
  rw [← mul_sub]
  apply Ideal.mul_mem_mul (h i)
  rw [← evaluate_coefficient_diagonal f i y]
  apply ideal_stable I (differenceCoefficient f i)
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa only [Fin.append_left] using h k
  · simp only [Fin.append_right, sub_self, Ideal.zero_mem]

/-- First-order Taylor is exact along any square-zero scalar, in any smooth algebra. -/
theorem nilsquare_taylor {n : ℕ} (f : Operation n) (x v : Fin n → A) (d : A)
    (hd : d * d = 0) :
    act f (fun i => x i + d * v i) = act f x + d * ∑ i, act (derivative f i) x * v i := by
  have h := taylor_remainder (Ideal.span ({d} : Set A)) f (fun i => x i + d * v i) x
    (fun i => by simpa only [add_sub_cancel_left] using
      Ideal.mul_mem_right (v i) (Ideal.span ({d} : Set A)) (Ideal.subset_span (Set.mem_singleton d)))
  rw [Ideal.span_singleton_mul_span_singleton, hd, Ideal.span_singleton_zero, Ideal.mem_bot] at h
  have hs : (∑ i, (x i + d * v i - x i) * act (derivative f i) x) =
      d * ∑ i, act (derivative f i) x * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at h
  linear_combination h


/-- Coordinate expansion of an ordinary continuous linear functional. -/
theorem linear_coordinates {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  calc
    L v = L (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, L (Pi.single i (v i)) := map_sum L _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm, ← smul_eq_mul, ← map_smul]
      congr 1
      ext j
      simp [Pi.single_apply]

theorem derivative_chain {m n : ℕ} (f : Operation n) (g : Fin n → Operation m) (j : Fin m) :
    (show Free m from derivative (substitute f g) j) =
      ∑ i, (show Free m from substitute (derivative f i) g) * (show Free m from derivative (g i) j) := by
  apply Subtype.ext
  funext x
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  change fderiv ℝ (f.val ∘ fun x i => (g i).val x) x (Pi.single j 1) = _
  rw [fderiv_comp x (f.property.differentiable (by simp) _)
    ((contDiff_pi.mpr fun i => (g i).property).differentiable (by simp) x),
    fderiv_pi (fun i => (g i).property.differentiable (by simp) x)]
  exact linear_coordinates (fderiv ℝ f.val (fun i => (g i).val x))
    (fun i => fderiv ℝ (g i).val x (Pi.single j 1))

def differential {n : ℕ} (f : Operation n) (x v : Fin n → A) : A :=
  ∑ i, act (derivative f i) x * v i

theorem differential_chain {m n : ℕ} (f : Operation n) (g : Fin n → Operation m)
    (x v : Fin m → A) :
    differential (substitute f g) x v =
      differential f (fun i => act (g i) x) (fun i => differential (g i) x v) := by
  have hc (j : Fin m) : act (derivative (substitute f g) j) x =
      ∑ i, act (derivative f i) (fun k => act (g k) x) * act (derivative (g i) j) x := by
    have he := congrArg (evaluate x).toAlgHom (derivative_chain f g j)
    simp only [map_sum] at he
    calc
      _ = _ := he
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hm := (evaluate x).toAlgHom.map_mul
          (show Free m from substitute (derivative f i) g) (show Free m from derivative (g i) j)
        change evaluate x _ = act (substitute (derivative f i) g) x * act (derivative (g i) j) x at hm
        rw [Structure.substitute] at hm
        exact hm
  simp only [differential, hc, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem derivative_projection {n : ℕ} (i j : Fin n) :
    derivative (projection i) j = constant n (if j = i then 1 else 0) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x (Pi.single j 1) = _
  simp [constant, Pi.single_apply, eq_comm]

theorem differential_projection {n : ℕ} (i : Fin n) (x v : Fin n → A) :
    differential (projection i) x v = v i := by
  simp only [differential, derivative_projection, Structure.constant]
  simp [apply_ite]

theorem derivative_constant (n : ℕ) (r : ℝ) (i : Fin n) :
    derivative (constant n r) i = constant n 0 := by
  apply Subtype.ext
  funext x
  simp [derivative, constant]

theorem differential_constant (n : ℕ) (r : ℝ) (x v : Fin n → A) :
    differential (constant n r) x v = 0 := by
  simp [differential, derivative_constant, Structure.constant]


theorem derivative_addition (i : Fin 2) : derivative addition i = constant 2 1 := by
  apply Subtype.ext
  funext x
  have h := ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x) |>.add
    (ContinuousLinearMap.proj (1 : Fin 2)).hasFDerivAt).fderiv
  change fderiv ℝ (fun x : Fin 2 → ℝ => x 0 + x 1) x (Pi.single i 1) = 1
  erw [h]
  fin_cases i <;> norm_num [Pi.single_apply]

theorem derivative_multiplication (i : Fin 2) : derivative multiplication i = projection (1-i) := by
  apply Subtype.ext
  funext x
  have h := ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x) |>.mul
    (ContinuousLinearMap.proj (1 : Fin 2)).hasFDerivAt).fderiv
  change fderiv ℝ (fun x : Fin 2 → ℝ => x 0 * x 1) x (Pi.single i 1) = x (1-i)
  erw [h]
  fin_cases i <;> norm_num [Pi.single_apply]

theorem differential_addition (x v : Fin 2 → A) : differential addition x v = v 0 + v 1 := by
  simp [differential, derivative_addition, Structure.constant, Fin.sum_univ_two]

theorem differential_multiplication (x v : Fin 2 → A) :
    differential multiplication x v = x 0 * v 1 + x 1 * v 0 := by
  simp [differential, derivative_multiplication, Structure.projection, Fin.sum_univ_two, add_comm]

end SquareKit.SmoothAlgebra

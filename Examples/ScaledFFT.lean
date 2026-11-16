import Applications.Parallel.ScaledFFT

/-! Complete observations and retained arithmetic costs for scaled size-four FFTs. -/
namespace Examples.ScaledFFT
open Applications.Parallel
open Applications.Parallel.ScaledFFT

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Counts come from the generated graph, including all boundary multiplications. -/
theorem route_costs :
    ((circuit ordinary).work, (circuit ordinary).multiplications, (circuit ordinary).depth) =
      (32, 0, 4) ∧
    ((circuit eager).work, (circuit eager).multiplications, (circuit eager).depth) =
      (64, 32, 8) ∧
    ((circuit retained).work, (circuit retained).multiplications, (circuit retained).depth) =
      (48, 16, 6) ∧
    ((circuit reordered).work, (circuit reordered).multiplications, (circuit reordered).depth) =
      (48, 16, 6) := by decide +kernel

/-- Exposing the intermediate ordinary value changes the shared-context comparison. -/
theorem shared_costs :
    (ordinaryObservedCircuit.work, ordinaryObservedCircuit.multiplications) = (32, 0) ∧
    ((observedCircuit eager).work, (observedCircuit eager).multiplications) = (64, 32) ∧
    ((observedCircuit retained).work, (observedCircuit retained).multiplications) = (56, 24) := by
  decide +kernel

/-- Every real and imaginary input is arbitrary; no projection of the DFT is discarded. -/
theorem full_observations (v : Nat → ℝ) :
    evaluate v (retained inputs) = fourier (fourier (evaluate v inputs)) ∧
    (evaluate v (observed retained inputs).1, evaluate v (observed retained inputs).2) =
      (fourier (evaluate v inputs), fourier (fourier (evaluate v inputs))) :=
  ⟨retained_correct v inputs, observed_correct v inputs retained (retained_correct v inputs)⟩

private theorem root_four : shape.fourierRoot = -Complex.I := by
  rw [← FFTScalar.phase_fourierRoot]
  exact FFTScalar.phase_quarter

/-- Unequal real/imaginary components detect output-order mistakes. This case
uses the public correctness theorem and evaluates the independent DFT. -/
theorem asymmetric_observation :
    evaluate (fun n => (n : ℝ) + 1) (retained inputs) =
      ![4 + 8 * Complex.I, 28 + 32 * Complex.I,
        20 + 24 * Complex.I, 12 + 16 * Complex.I] := by
  rw [retained_correct]
  funext i
  fin_cases i <;>
    norm_num [fourier, Factor.directDFT, root_four, Fin.sum_univ_succ,
      evaluate, inputs, FFTScalar.value, FFTScalar.Wire.eval, Complex.ext_iff, pow_succ]

/-- A zero scale loses a nonzero coordinate, so it cannot be admitted as a boundary. -/
theorem zero_scale_loses_coordinate :
    (fun i : Fin 4 => (0 : ℂ) * (if i = 0 then 1 else 0)) = (fun _ => 0) ∧
      (fun i : Fin 4 => if i = 0 then (1 : ℂ) else 0) ≠ (fun _ => 0) := by
  constructor
  · funext i; simp
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

/-- Reconstruction at the incompatible boundary includes its compensation gates. -/
theorem compensation_costs :
    ((circuit compensated).work, (circuit compensated).multiplications,
      (circuit compensated).depth) = (48, 16, 6) ∧
    ((circuit uncompensated).work, (circuit uncompensated).multiplications,
      (circuit uncompensated).depth) = (44, 12, 6) := by decide +kernel

/-- The impulse's first DFT is all ones. The uncompensated alternating scale
changes the second DC coefficient from four to three. -/
theorem missing_compensation_changes_value :
    evaluate (fun n => if n = 0 then 1 else 0) (uncompensated inputs) 0 = 3 ∧
    evaluate (fun n => if n = 0 then 1 else 0) (compensated inputs) 0 = 4 := by
  simp only [uncompensated, evaluate_transform, toAlternating_correct, producer_correct,
    Boundary.decode_encode, compensated_correct]
  norm_num [fourier, Factor.directDFT, root_four, Fin.sum_univ_succ, evaluate, inputs,
    FFTScalar.value, FFTScalar.Wire.eval, alternatingBoundary, Boundary.encode,
    Complex.ext_iff, pow_succ]

/-- The inventory is expanded from the same two factor trees, including their
nonidentity twiddle occurrences even though quarter-turn arithmetic is free. -/
theorem structural_counts : transformSites.length = 8 ∧ twiddleSites.length = 2 := by
  decide +kernel

/-- The result applies to unequal arrival times as well as the zero-arrival depth. -/
theorem skewed_arrivals (i : Fin 4) :
    ((eager inputs i).1.arrival (fun n => if n = 3 then 7 else n),
      (eager inputs i).2.arrival (fun n => if n = 3 then 7 else n)) =
    ((retained inputs i).1.arrival (fun n => if n = 3 then 7 else n) + 2,
      (retained inputs i).2.arrival (fun n => if n = 3 then 7 else n) + 2) :=
  eager_arrivals _ _ _

end Examples.ScaledFFT

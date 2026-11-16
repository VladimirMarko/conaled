import Applications.Parallel.FFTScalar
import Applications.Parallel.FFTNormalization

/-! Two forward size-four transforms with explicit scaled boundaries.
The ordinary observation is the full vector, including an optional intermediate
observation. Arithmetic costs use the existing labeled scalar graph. -/
namespace Applications.Parallel.ScaledFFT

open FFTScalar
open scoped BigOperators Matrix

abbrev shape : Factor := .comp .two .two
abbrev Vector (α : Type) := Fin 4 → α

/-- The independent ordinary, forward DFT specification. -/
noncomputable def fourier (x : Vector ℂ) : Vector ℂ :=
  Factor.directDFT shape.fourierRoot x

theorem fourier_scale (c : ℂ) (x : Vector ℂ) :
    fourier (fun i => c * x i) = fun i => c * fourier x i := by
  funext i
  simp [fourier, Factor.directDFT, Finset.mul_sum, mul_assoc]

/-- A bounded representation helper used by the uniform and nonuniform clients.
The permutation maps stored coordinates to ordinary coordinates. -/
structure Boundary where
  scale : Vector ℂ
  permutation : Equiv.Perm (Fin 4)
  nonzero : ∀ i, scale i ≠ 0

noncomputable def Boundary.encode (b : Boundary) (x : Vector ℂ) : Vector ℂ :=
  fun i => b.scale i * x (b.permutation i)

noncomputable def Boundary.decode (b : Boundary) (x : Vector ℂ) : Vector ℂ :=
  fun i => (b.scale (b.permutation.symm i))⁻¹ * x (b.permutation.symm i)

@[simp] theorem Boundary.decode_encode (b : Boundary) (x : Vector ℂ) :
    b.decode (b.encode x) = x := by
  funext i
  simp [Boundary.encode, Boundary.decode, b.nonzero]

@[simp] theorem Boundary.encode_decode (b : Boundary) (x : Vector ℂ) :
    b.encode (b.decode x) = x := by
  funext i
  simp [Boundary.encode, Boundary.decode, b.nonzero]

noncomputable def halfBoundary : Boundary :=
  ⟨fun _ => 1 / 2, Equiv.refl _, by intro i; norm_num⟩

noncomputable def reversedBoundary : Boundary :=
  ⟨fun _ => 1 / 2, ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩,
    by intro i; norm_num⟩

noncomputable def alternatingBoundary : Boundary :=
  ⟨fun i => if i.val % 2 = 0 then 1 / 2 else 1, Equiv.refl _,
    by intro i; split <;> norm_num⟩

def multiply (q : ℚ) (p : List Nat) (z : ComplexWire) : ComplexWire :=
  (.mul (0 :: p) (.rational q) z.1, .mul (1 :: p) (.rational q) z.2)

@[simp] theorem value_multiply (v : Nat → ℝ) (q : ℚ) (p : List Nat)
    (z : ComplexWire) : value v (multiply q p z) = (q : ℂ) * value v z := by
  apply Complex.ext <;> simp [value, multiply, Wire.eval, Constant.eval,
    Complex.mul_re, Complex.mul_im]

def scale (q : ℚ) (p : List Nat) (x : Vector ComplexWire) : Vector ComplexWire :=
  fun i => multiply q (i.val :: p) (x i)

noncomputable def evaluate (v : Nat → ℝ) (x : Vector ComplexWire) : Vector ℂ := fun i => value v (x i)

@[simp] theorem evaluate_scale (v : Nat → ℝ) (q : ℚ) (p : List Nat)
    (x : Vector ComplexWire) :
    evaluate v (scale q p x) = fun i => (q : ℂ) * evaluate v x i := by
  funext i
  exact value_multiply v q _ _

/-- The existing factor-tree lowering; this wrapper fixes only coordinates. -/
def transform (p : List Nat) (x : Vector ComplexWire) : Vector ComplexWire :=
  shape.reverse.decode (lower true shape p (shape.tabulate fun i => x (shape.indexEquiv i)))

@[simp] theorem evaluate_transform (v : Nat → ℝ) (p : List Nat)
    (x : Vector ComplexWire) : evaluate v (transform p x) = fourier (evaluate v x) := by
  have hd (s : Factor) (y : s.Data ComplexWire) :
      s.decode (s.map (value v) y) = fun i => value v (s.decode y i) := by
    funext i
    exact s.get_map (value v) y _
  have ht : shape.decode (shape.map (value v)
      (shape.tabulate fun i => x (shape.indexEquiv i))) = evaluate v x := by
    rw [hd]
    funext i
    change value v (shape.get (shape.tabulate fun j => x (shape.indexEquiv j))
      (shape.indexEquiv.symm i)) = value v (x i)
    rw [Factor.get_tabulate, Equiv.apply_symm_apply]
  have h := lower_fourier v true shape p (shape.tabulate fun i => x (shape.indexEquiv i))
  rw [hd, ht] at h
  exact h

/-- Size four's unitary normalization is exactly one half. -/
theorem normalization_four : FFTUnitary.normalization 4 = (1 / 2 : ℂ) := by
  have h : Real.sqrt 4 = 2 := by norm_num [Real.sqrt_eq_iff_eq_sq]
  simp [FFTUnitary.normalization, h]

/-- The scaled producer is the established normalized Fourier boundary. -/
theorem normalized_observation (v : Nat → ℝ) (p : List Nat)
    (x : Vector ComplexWire) (i : Fin 4) :
    evaluate v (scale (1/2) [0] (transform p x)) i =
      (FFTUnitary.fourierMatrix 4 *ᵥ evaluate v x) i := by
  have hx : shape.decode
      (shape.tabulate fun j => evaluate v x (shape.indexEquiv j)) = evaluate v x := by
    funext j
    change shape.get (shape.tabulate fun k => evaluate v x (shape.indexEquiv k))
      (shape.indexEquiv.symm j) = evaluate v x j
    rw [Factor.get_tabulate, Equiv.apply_symm_apply]
  have h := FFTUnitary.normalized_fft_decode shape
    (shape.tabulate fun j => evaluate v x (shape.indexEquiv j)) i
  rw [Factor.fourier_correct, hx] at h
  change FFTUnitary.normalization 4 * fourier (evaluate v x) i = _ at h
  rw [normalization_four] at h
  have hi : Fin.cast shape.size_reverse i = i := Fin.ext rfl
  rw [hi] at h
  rw [evaluate_scale, evaluate_transform]
  convert h using 1 <;> norm_num
  rfl

def ordinary (x : Vector ComplexWire) : Vector ComplexWire :=
  transform [2] (transform [1] x)

def producer (x : Vector ComplexWire) : Vector ComplexWire :=
  scale (1/2) [3] (transform [1] x)

/-- An ordinary-input normalized stage needs decoding and final reconstruction. -/
def eager (x : Vector ComplexWire) : Vector ComplexWire :=
  scale 2 [6] (scale (1/2) [5] (transform [2] (scale 2 [4] (producer x))))

/-- A scale-aware consumer keeps the producer's scale through the second FFT. -/
def retained (x : Vector ComplexWire) : Vector ComplexWire :=
  scale 2 [6] (transform [2] (producer x))

def reverseStorage (x : Vector ComplexWire) : Vector ComplexWire := fun i => x i.rev

def reordered (x : Vector ComplexWire) : Vector ComplexWire :=
  scale 2 [6] (transform [2] (reverseStorage (reverseStorage (producer x))))

@[simp] theorem reverseStorage_twice (x : Vector ComplexWire) :
    reverseStorage (reverseStorage x) = x := by funext i; simp [reverseStorage]

@[simp] theorem ordinary_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (ordinary x) = fourier (fourier (evaluate v x)) := by
  simp [ordinary]

@[simp] theorem producer_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (producer x) = halfBoundary.encode (fourier (evaluate v x)) := by
  change evaluate v (producer x) = fun i => (1 / 2 : ℂ) * fourier (evaluate v x) i
  simp [producer]

@[simp] theorem retained_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (retained x) = fourier (fourier (evaluate v x)) := by
  simp only [retained, producer, evaluate_scale, evaluate_transform, fourier_scale]
  funext i
  norm_num
  ring

@[simp] theorem eager_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (eager x) = fourier (fourier (evaluate v x)) := by
  simp only [eager, producer, evaluate_scale, evaluate_transform, fourier_scale]
  funext i
  norm_num
  ring

@[simp] theorem reordered_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (reordered x) = fourier (fourier (evaluate v x)) := by
  simpa [reordered, retained] using retained_correct v x

/-- Both complete observations, not just the final transform. -/
def observed (route : Vector ComplexWire → Vector ComplexWire)
    (x : Vector ComplexWire) : Vector ComplexWire × Vector ComplexWire :=
  (scale 2 [4] (producer x), route x)

theorem observed_correct (v : Nat → ℝ) (x : Vector ComplexWire)
    (route : Vector ComplexWire → Vector ComplexWire)
    (h : evaluate v (route x) = fourier (fourier (evaluate v x))) :
    (evaluate v (observed route x).1, evaluate v (observed route x).2) =
      (fourier (evaluate v x), fourier (fourier (evaluate v x))) := by
  refine Prod.ext ?_ h
  simp only [observed, producer, evaluate_scale, evaluate_transform]
  funext i
  norm_num
  ring

def inputs : Vector ComplexWire := fun i => (.input (2*i.val), .input (2*i.val+1))

def outputs (x : Vector ComplexWire) : List Wire :=
  (List.ofFn x).flatMap fun z => [z.1, z.2]

def circuit (route : Vector ComplexWire → Vector ComplexWire) : Circuit :=
  ⟨outputs (route inputs)⟩

def observedCircuit (route : Vector ComplexWire → Vector ComplexWire) : Circuit :=
  ⟨outputs (observed route inputs).1 ++ outputs (observed route inputs).2⟩

/-- The ordinary route exposes its existing intermediate outputs without adapters. -/
def ordinaryObservedCircuit : Circuit :=
  ⟨outputs (transform [1] inputs) ++ outputs (ordinary inputs)⟩

/-- Conversion from the producer's uniform half-scale to an alternating scale.
Only the odd coordinates require multiplication. -/
def toAlternating (x : Vector ComplexWire) : Vector ComplexWire :=
  fun i => if i.val % 2 = 0 then x i else multiply 2 [7, i.val] (x i)

/-- An ordinary-input consumer must compensate the even coordinates. -/
def fromAlternating (x : Vector ComplexWire) : Vector ComplexWire :=
  fun i => if i.val % 2 = 0 then multiply 2 [8, i.val] (x i) else x i

/-- The shared boundary helper describes the actual generated conversion. -/
theorem toAlternating_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (toAlternating x) =
      alternatingBoundary.encode (halfBoundary.decode (evaluate v x)) := by
  funext i
  change value v (if i.val % 2 = 0 then x i else multiply 2 [7, i.val] (x i)) =
    (if i.val % 2 = 0 then (1/2 : ℂ) else 1) * ((1/2 : ℂ)⁻¹ * value v (x i))
  split <;> simp [value_multiply]

theorem fromAlternating_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (fromAlternating x) = alternatingBoundary.decode (evaluate v x) := by
  funext i
  change value v (if i.val % 2 = 0 then multiply 2 [8, i.val] (x i) else x i) =
    (if i.val % 2 = 0 then (1/2 : ℂ) else 1)⁻¹ * value v (x i)
  split <;> simp

def compensated (x : Vector ComplexWire) : Vector ComplexWire :=
  transform [2] (fromAlternating (toAlternating (producer x)))

/-- This tempting omitted compensation is retained only as a negative case. -/
def uncompensated (x : Vector ComplexWire) : Vector ComplexWire :=
  transform [2] (toAlternating (producer x))

theorem compensated_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (compensated x) = fourier (fourier (evaluate v x)) := by
  simp only [compensated, evaluate_transform, fromAlternating_correct,
    toAlternating_correct, producer_correct, Boundary.decode_encode]

/-- Permutation metadata agrees with the stored producer vector. -/
theorem reversed_producer_correct (v : Nat → ℝ) (x : Vector ComplexWire) :
    evaluate v (reverseStorage (producer x)) =
      reversedBoundary.encode (fourier (evaluate v x)) := by
  funext i
  change evaluate v (producer x) i.rev = (1/2 : ℂ) * fourier (evaluate v x) i.rev
  rw [producer_correct]
  rfl

/-- The structural sites belong to the same two factor-tree invocations used by
all routes. Boundary products are separately counted by their generated gates. -/
def transformSites : List (Nat × Factor.Site shape) :=
  shape.butterflySites.map (1, ·) ++ shape.butterflySites.map (2, ·)

def twiddleSites : List (Nat × Factor.Site shape) :=
  shape.twiddleSites.map (1, ·) ++ shape.twiddleSites.map (2, ·)

/-- Scalar arrival propagation through the fixed two-pass butterfly network. -/
def arrivalMap (x : Vector (Nat × Nat)) (i : Fin 4) : Nat × Nat :=
  if i.val % 2 = 0 then
    (max (max (x 0).1 (x 2).1) (max (x 1).1 (x 3).1) + 2,
     max (max (x 0).2 (x 2).2) (max (x 1).2 (x 3).2) + 2)
  else
    (max (max (x 0).1 (x 2).1) (max (x 1).2 (x 3).2) + 2,
     max (max (x 0).2 (x 2).2) (max (x 1).1 (x 3).1) + 2)

def arrivals (t : Nat → Nat) (x : Vector ComplexWire) : Vector (Nat × Nat) :=
  fun i => ((x i).1.arrival t, (x i).2.arrival t)

theorem arrivals_transform (t : Nat → Nat) (p : List Nat) (x : Vector ComplexWire) :
    arrivals t (transform p x) = arrivalMap (arrivals t x) := by
  funext i
  fin_cases i <;>
    change (max (_ + 1) (_ + 1) + 1, max (_ + 1) (_ + 1) + 1) = _
  all_goals simp only [max_add_add_right, Nat.add_assoc, arrivalMap, arrivals]
  all_goals rfl

@[simp] theorem arrivals_scale (t : Nat → Nat) (q : ℚ) (p : List Nat)
    (x : Vector ComplexWire) : arrivals t (scale q p x) =
      fun i => ((arrivals t x i).1 + 1, (arrivals t x i).2 + 1) := rfl

/-- Exact pointwise arrival comparison for arbitrary input gates and times. -/
theorem eager_arrivals (t : Nat → Nat) (x : Vector ComplexWire) (i : Fin 4) :
    ((eager x i).1.arrival t, (eager x i).2.arrival t) =
      ((retained x i).1.arrival t + 2, (retained x i).2.arrival t + 2) := by
  change arrivals t (eager x) i =
    ((arrivals t (retained x) i).1 + 2, (arrivals t (retained x) i).2 + 2)
  simp only [eager, retained, producer, arrivals_scale, arrivals_transform]
  fin_cases i <;> norm_num [arrivalMap, Nat.add_assoc, max_add_add_right]

end Applications.Parallel.ScaledFFT

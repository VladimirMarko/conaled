import Applications.Parallel.FFT
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The conventional complex Fourier transform

The algebraic factorization is instantiated with the primitive root
`exp (-(2 π i / N))`.  This is exact complex mathematics, rather than a
floating-point implementation or a Walsh--Hadamard transform.
-/

namespace Applications.Parallel.Factor

open Complex
open scoped Real

noncomputable def fourierRoot (s : Factor) : ℂ :=
  (Complex.exp (2 * π * I / s.size))⁻¹

theorem fourierRoot_eq_exp (s : Factor) :
    s.fourierRoot = Complex.exp (-(2 * π * I / s.size)) := by
  rw [Complex.exp_neg]
  rfl

theorem fourierRoot_primitive (s : Factor) :
    IsPrimitiveRoot s.fourierRoot s.size :=
  (Complex.isPrimitiveRoot_exp s.size (Nat.ne_of_gt s.size_pos)).inv

theorem fourierRoot_pow (s : Factor) : s.fourierRoot ^ s.size = 1 :=
  s.fourierRoot_primitive.pow_eq_one

noncomputable def fourierSquare (s : Factor) :
    Squares.Square (s.rep ℂ) (s.reverse.rep ℂ) :=
  s.fftSquare s.fourierRoot s.fourierRoot_pow

theorem fourier_correct (s : Factor) (x : s.Data ℂ) :
    s.reverse.decode (s.fft s.fourierRoot x) =
      directDFT s.fourierRoot (s.decode x) :=
  s.fft_decode s.fourierRoot s.fourierRoot_pow x

theorem radixTwo_correct (depth : Nat) (x : (rightPow depth).Data ℂ) :
    (rightPow depth).reverse.decode
      ((rightPow depth).fft (rightPow depth).fourierRoot x) =
      directDFT (rightPow depth).fourierRoot ((rightPow depth).decode x) :=
  (rightPow depth).fourier_correct x

end Applications.Parallel.Factor

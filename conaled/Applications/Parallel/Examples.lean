import Applications.Parallel.Polynomial
import Applications.Parallel.ComplexFFT
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Executable checks and representative proof audits

The universal results are in the application modules.  These examples also
exercise a noncommutative monoid, two different scan recipes, a polynomial,
and exact non-real Fourier twiddle behavior in a finite field.
-/

namespace Applications.Parallel.Examples

def rightScan : ScanPlan := ScanPlan.pair.rightPow 3
def leftScan : ScanPlan := ScanPlan.pair.leftPow 3

theorem different_recipes : rightScan ≠ leftScan := by decide

def scanWords (p : ScanPlan) (xs : p.shape.Data Nat) : List (List Nat) × List Nat :=
  let r := p.scanner.run (p.shape.map FreeMonoid.of xs)
  ((p.shape.flatten r.1).map FreeMonoid.toList, FreeMonoid.toList r.2)

def eightNaturals : ((Nat × Nat) × (Nat × Nat)) × ((Nat × Nat) × (Nat × Nat)) :=
  (((1, 2), (3, 4)), ((5, 6), (7, 8)))

def rightWords : List (List Nat) × List Nat :=
  scanWords rightScan eightNaturals

def leftWords : List (List Nat) × List Nat :=
  scanWords leftScan eightNaturals

theorem rightWords_value : rightWords =
    ([[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [1, 2, 3, 4, 5],
      [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7]], [1, 2, 3, 4, 5, 6, 7, 8]) := rfl

theorem two_scans_agree : rightWords = leftWords := rfl

def polynomialExample : Nat :=
  evaluatePolynomial (ScanPlan.pair.rightPow 2) (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)) 2

theorem polynomialExample_value : polynomialExample = 49 := rfl

def fourPoint : Factor := .comp .two .two

/-- The root required by the four-point factorization. -/
theorem fourth_root : (4 : ZMod 17) ^ fourPoint.size = 1 := by decide

theorem fourth_root_half : (4 : ZMod 17) ^ 2 = -1 := by decide

def fourInput : fourPoint.Data (ZMod 17) := ((1, 2), (3, 4))

def fourOutput : List Nat :=
  (List.ofFn (fourPoint.reverse.decode (fourPoint.fft (4 : ZMod 17) fourInput))).map ZMod.val

theorem fourOutput_value : fourOutput = [10, 7, 15, 6] := by decide

theorem fourOutput_matches_DFT :
    fourPoint.reverse.decode (fourPoint.fft (4 : ZMod 17) fourInput) =
      Factor.directDFT 4 (fourPoint.decode fourInput) :=
  fourPoint.fft_decode 4 fourth_root fourInput

def eightPoint : Factor := Factor.rightPow 3

theorem eighth_root : (2 : ZMod 17) ^ eightPoint.size = 1 := by decide

def eightInput : eightPoint.Data (ZMod 17) :=
  (show ((ZMod 17 × ZMod 17) × (ZMod 17 × ZMod 17)) ×
    ((ZMod 17 × ZMod 17) × (ZMod 17 × ZMod 17)) from
      (((1, 2), (3, 4)), ((5, 6), (7, 8))))

def eightOutput : List Nat :=
  (List.ofFn (eightPoint.reverse.decode (eightPoint.fft (2 : ZMod 17) eightInput))).map ZMod.val

theorem eightOutput_matches_DFT :
    eightPoint.reverse.decode (eightPoint.fft (2 : ZMod 17) eightInput) =
      Factor.directDFT 2 (eightPoint.decode eightInput) :=
  eightPoint.fft_decode 2 eighth_root eightInput

#eval rightWords
#eval leftWords
#eval polynomialExample
#eval fourOutput
#eval eightOutput

#print axioms Shape.scan_correct
#print axioms Shape.scanNestedWith_correct
#print axioms ScanPlan.correct
#print axioms Scanner.powers_correct
#print axioms evaluatePolynomial_correct
#print axioms Factor.twiddle_factorization
#print axioms Factor.fft_correct
#print axioms Factor.dft_eq_direct
#print axioms Factor.fft_decode
#print axioms Factor.fourierRoot_primitive
#print axioms Factor.fourier_correct
#print axioms fourOutput_value

end Applications.Parallel.Examples

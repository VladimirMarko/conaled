import Applications.Convolution.Sparse
import Applications.Convolution.Proper
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Independent and combined clients for finite convolution, sparse monoid
semantics and proper closure. Exact values separate counting from existence. -/
namespace Examples.GeneralizedConvolution
open Convolution
open scoped BigOperators Computability

/-- Four additive decompositions of three give Cauchy coefficient four. -/
example : Finite.convolution (M := Multiplicative ℕ) (fun _ => (1 : ℕ))
    (fun _ => 1) (Multiplicative.ofAdd 3) = 4 := by decide

local instance : Finset.HasMulAntidiagonal (Multiplicative (ZMod 2)) :=
  Finite.finiteAntidiagonal _

/-- A finite group admits convolution even though repeated factorization is unbounded. -/
example : Finite.convolution (M := Multiplicative (ZMod 2)) (fun _ => (1 : ℕ))
    (fun _ => 1) 1 = 2 := by decide

def groupDelta : Finite.Series (Multiplicative (ZMod 2)) ℕ :=
  ⟨fun x => if x = Multiplicative.ofAdd 1 then 1 else 0⟩

example : groupDelta 1 = 0 := by decide
example : (groupDelta * groupDelta) 1 = 1 := by decide

/-- These sparse inputs live on an infinite group, which has infinite full fibers. -/
def integerP : Sparse.Terms (Multiplicative ℤ) ℕ := [(Multiplicative.ofAdd 2,3)]
def integerQ : Sparse.Terms (Multiplicative ℤ) ℕ := [(Multiplicative.ofAdd (-2),4)]

example : Sparse.denote (Sparse.mul integerP integerQ) = MonoidAlgebra.single 1 12 := by
  rw [Sparse.denote_mul]
  simp [integerP, integerQ, Sparse.denote, MonoidAlgebra.single_mul_single]

/-- A homomorphism may identify keys; the semantic map adds their coefficients. -/
def forgetIndex : Multiplicative ℤ →* Multiplicative ℤ := 1

example : Sparse.denote (Sparse.push forgetIndex
    [(Multiplicative.ofAdd 2, (3 : ℕ)), (Multiplicative.ofAdd 5, 4)]) =
    MonoidAlgebra.single 1 7 := by
  rw [Sparse.denote_push]
  simp [Sparse.denote, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapDomain_add,
    MonoidAlgebra.mapDomain_single, forgetIndex, ← MonoidAlgebra.single_add]

/-- Existing word polynomial multiplication is recovered through the new decoder. -/
example : (Sparse.denote (Sparse.mul (M := FreeMonoid Char)
    Polynomial.sampleP Polynomial.sampleQ)).coeff (FreeMonoid.ofList "abc".toList) = 10 := by
  rw [Sparse.word_mul]
  decide

abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

def upper : Mat := !![0,1;0,0]
def lower : Mat := !![0,0;1,0]

/-- Coefficient multiplication order remains visible under the generalized word convolution. -/
example : (Finite.convolution
    (fun u : FreeMonoid Unit => (monomial [()] upper : Series Unit Mat) u.toList)
    (fun u : FreeMonoid Unit => (monomial [()] lower : Series Unit Mat) u.toList)
    (FreeMonoid.ofList [(),()])) 0 0 = 1 := by
  rw [word_convolution, monomial_mul]
  decide
example : (Finite.convolution
    (fun u : FreeMonoid Unit => (monomial [()] lower : Series Unit Mat) u.toList)
    (fun u : FreeMonoid Unit => (monomial [()] upper : Series Unit Mat) u.toList)
    (FreeMonoid.ofList [(),()])) 0 0 = 0 := by
  rw [word_convolution, monomial_mul]
  decide

/-- On two letters, one length-two piece contributes three and two singleton
pieces contribute four. The independent expected count is seven. -/
def ambiguous : Series Unit ℕ := Polynomial.denote [([()],2),([(),()],3)]
theorem ambiguous_proper : Proper ambiguous := rfl

theorem ambiguous_count : properStar ambiguous [(),()] = 7 := by
  rw [← evalProperStar_correct]
  decide

example : [(),()] ∈ (support ambiguous)∗ := by
  rw [← support_properStar ambiguous ambiguous_proper]
  change properStar ambiguous [(),()] ≠ 0
  rw [ambiguous_count]; decide

example : SquareKit.WordCoalgebra.run
    (LanguageCoalgebra.Weighted.coalgebra ClosureMachine.leaves)
    (ClosureMachine.nextTerm ambiguous ()) [()] = 7 := by
  rw [ClosureMachine.run_nextTerm ambiguous ambiguous_proper, ambiguous_count]

/-- The generalized multiplication and proper closure compose through a semiring equivalence. -/
theorem combined_unfold {α R : Type*} [DecidableEq α] [Semiring R]
    (f : Series α R) (hf : Proper f) :
    wordEquiv (properStar f) = 1 + wordEquiv f * wordEquiv (properStar f) := by
  simpa only [map_add, map_one, map_mul] using
    congrArg (wordEquiv (α := α) (R := R)) (properStar_unfold_left f hf)

/-- The same coefficient interpretation preserves the old and generalized multiplication. -/
example {α R S : Type*} [DecidableEq α] [Semiring R] [Semiring S]
    (φ : R →+* S) (f : Series α R) :
    Finite.mapCoefficients φ (wordEquiv (properStar f)) =
      wordEquiv (properStar (mapCoefficients φ f)) := by
  have h := congrArg (wordEquiv (α := α) (R := S)) (map_properStar φ f)
  exact h

example : properStar (0 : Series Unit ℕ) [] = 1 := properStar_nil _
example : properStar (0 : Series Unit ℕ) = 1 := properStar_zero
example (s : Series Unit ℕ) : s ≠ 1 + (1 : Series Unit ℕ)*s :=
  no_nat_nullable_star 1 s rfl

end Examples.GeneralizedConvolution

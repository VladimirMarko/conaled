import Applications.Convolution.Polynomial
import Applications.Convolution.Finite
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! Redundant sparse monoid polynomials. Finite support makes multiplication
possible on arbitrary monoids; no finite-factorization or star assumption is used. -/
namespace Convolution
namespace Sparse
universe u v
variable {M N R : Type*} [Monoid M] [Monoid N] [Semiring R]

abbrev Terms (M R : Type*) := List (M × R)

noncomputable def denote : Terms M R → MonoidAlgebra R M
  | [] => 0
  | (m,r) :: p => MonoidAlgebra.single m r + denote p

def mul (p q : Terms M R) : Terms M R :=
  p.flatMap fun mr => q.map fun ns => (mr.1 * ns.1, mr.2 * ns.2)
def one : Terms M R := [(1,1)]

@[simp] theorem denote_nil : denote ([] : Terms M R) = 0 := rfl
@[simp] theorem denote_cons (m : M) (r : R) (p : Terms M R) :
    denote ((m,r)::p) = MonoidAlgebra.single m r + denote p := rfl
@[simp] theorem denote_append (p q : Terms M R) : denote (p++q) = denote p + denote q := by
  induction p with
  | nil => simp
  | cons mr p ih => cases mr; simp [ih, add_assoc]
@[simp] theorem denote_one : denote (one : Terms M R) = 1 := by simp [one, MonoidAlgebra.one_def]

theorem denote_map_left (m : M) (r : R) (q : Terms M R) :
    denote (q.map fun ns => (m * ns.1, r * ns.2)) = MonoidAlgebra.single m r * denote q := by
  induction q with
  | nil => simp
  | cons ns q ih => cases ns; simp [ih, mul_add, MonoidAlgebra.single_mul_single]

theorem denote_mul (p q : Terms M R) : denote (mul p q) = denote p * denote q := by
  induction p with
  | nil => simp [mul]
  | cons mr p ih =>
    cases mr
    simp [mul, denote_map_left, ← ih, add_mul]

section Normalize
variable [DecidableEq M]
def insert (m : M) (r : R) : Terms M R → Terms M R
  | [] => [(m,r)]
  | (n,s)::p => if m=n then (n,r+s)::p else (n,s)::insert m r p

theorem denote_insert (m : M) (r : R) (p : Terms M R) :
    denote (insert m r p) = MonoidAlgebra.single m r + denote p := by
  induction p with
  | nil => simp [insert]
  | cons ns p ih =>
    rcases ns with ⟨n,s⟩
    by_cases h : m=n
    · subst n; simp [insert, MonoidAlgebra.single_add, add_assoc]
    · simp only [insert, ite_eq_right h, denote_cons, ih]; ac_rfl

def normalize : Terms M R → Terms M R
  | [] => []
  | (m,r)::p => insert m r (normalize p)

theorem denote_normalize (p : Terms M R) : denote (normalize p) = denote p := by
  induction p with
  | nil => rfl
  | cons mr p ih => cases mr; simp [normalize, denote_insert, ih]
end Normalize

/-- Pushforward combines collisions through the finite-support semantic map. -/
def push (h : M →* N) (p : Terms M R) : Terms N R := p.map fun mr => (h mr.1, mr.2)

theorem denote_push (h : M →* N) (p : Terms M R) :
    denote (push h p) = MonoidAlgebra.mapDomainRingHom R h (denote p) := by
  induction p with
  | nil => simp [push]
  | cons mr p ih =>
    rcases mr with ⟨m,r⟩
    change MonoidAlgebra.single (h m) r + denote (push h p) =
      (MonoidAlgebra.mapDomainRingHom R h) (MonoidAlgebra.single m r + denote p)
    rw [map_add, ih]
    congr 1
    exact (MonoidAlgebra.mapDomain_single).symm

theorem push_mul (h : M →* N) (p q : Terms M R) :
    denote (push h (mul p q)) = denote (push h p) * denote (push h q) := by
  rw [denote_push, denote_mul, map_mul, denote_push, denote_push]

@[reducible] noncomputable def rep (M : Type u) (R : Type v) [Monoid M] [Semiring R] :
    Squares.Rep.{max u v} where
  R := Terms M R
  S := MonoidAlgebra R M
  decode := denote

noncomputable def mulSquare : Squares.Square
    (Squares.product (rep M R) (rep M R)) (rep M R) where
  impl p := mul p.1 p.2
  spec p := p.1 * p.2
  commutes p := denote_mul p.1 p.2

noncomputable def normalizeSquare [DecidableEq M] : Squares.Square (rep M R) (rep M R) where
  impl := normalize
  spec := id
  commutes := denote_normalize

noncomputable def normalizedMulSquare [DecidableEq M] : Squares.Square
    (Squares.product (rep M R) (rep M R)) (rep M R) :=
  Squares.compose normalizeSquare mulSquare

/-- No representation conversion is needed for existing word terms. -/
theorem word_normalize_eq {α : Type*} [DecidableEq α] (p : Polynomial α R) :
    normalize (M := FreeMonoid α) p = Polynomial.normalize p := by
  induction p with
  | nil => rfl
  | cons ur p ih =>
    rcases ur with ⟨u,r⟩
    simp only [normalize, Polynomial.normalize, ih]
    generalize Polynomial.normalize p = q
    induction q with
    | nil => rfl
    | cons vs q ih =>
      rcases vs with ⟨v,s⟩
      change (if u=v then (v,r+s)::q else (v,s)::insert (M := FreeMonoid α) u r q) = _
      by_cases h : u=v <;> simp [Polynomial.insert, h, ih]

/-- The original word decoder is recovered coefficient by coefficient. -/
theorem word_denote {α : Type*} [DecidableEq α] (p : Polynomial α R) (w : List α) :
    (denote (M := FreeMonoid α) p).coeff (FreeMonoid.ofList w) = Polynomial.denote p w := by
  induction p with
  | nil => simp [denote, Polynomial.denote]
  | cons ur p ih =>
    rcases ur with ⟨u,r⟩
    change (MonoidAlgebra.single (FreeMonoid.ofList u) r + denote (M := FreeMonoid α) p).coeff
      (FreeMonoid.ofList w) = (monomial u r + Polynomial.denote p) w
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_apply, ih]
    congr 1
    classical
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, monomial_apply, eq_comm]

/-- Recover the existing multiplication square through the monoid-algebra decoder. -/
theorem word_mul {α : Type*} [DecidableEq α] (p q : Polynomial α R) (w : List α) :
    (denote (mul (M := FreeMonoid α) p q)).coeff (FreeMonoid.ofList w) =
      (Polynomial.denote p * Polynomial.denote q) w := by
  change (denote (M := FreeMonoid α) (Polynomial.mul p q)).coeff (FreeMonoid.ofList w) = _
  rw [word_denote, Polynomial.denote_mul]

/-- The existing normalization square has the same finite-support meaning. -/
theorem word_normalize {α : Type*} [DecidableEq α] (p : Polynomial α R) (w : List α) :
    (denote (M := FreeMonoid α) (Polynomial.normalize p)).coeff (FreeMonoid.ofList w) =
      Polynomial.denote p w := by
  rw [word_denote, Polynomial.denote_normalize]

end Sparse
end Convolution

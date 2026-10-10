import Squares
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A shape-compositional Cooley--Tukey FFT

The runtime is a nested product of scalar values.  Functor composition is
kept explicit in `Factor.comp`; its FFT reverses the two output factors.
The only scalar kernels have size one or two.  Larger transforms use two
families of recursive transforms, transposes, and twiddle factors.

The correctness theorem is against the direct finite Fourier sum.  It is
proved for every factor tree and every root satisfying `ω ^ size = 1` in a
commutative semiring.  Primitivity is not needed for the factorization itself;
the companion complex specialization supplies a primitive root for the
usual Fourier transform.  No floating-point error or backend speed theorem
is claimed here.
-/

universe u v

namespace Applications.Parallel

inductive Factor where
  | one
  | two
  | comp (outer inner : Factor)
  deriving Repr, DecidableEq

namespace Factor

def size : Factor → Nat
  | .one => 1
  | .two => 2
  | .comp s t => s.size * t.size

theorem size_pos (s : Factor) : 0 < s.size := by
  induction s with
  | one => decide
  | two => decide
  | comp s t ihs iht => exact Nat.mul_pos ihs iht

@[reducible] def Index : Factor → Type
  | .one => Fin 1
  | .two => Fin 2
  | .comp s t => s.Index × t.Index

instance indexFintype : (s : Factor) → Fintype s.Index
  | .one => inferInstanceAs (Fintype (Fin 1))
  | .two => inferInstanceAs (Fintype (Fin 2))
  | .comp s t => @instFintypeProd s.Index t.Index (indexFintype s) (indexFintype t)

instance indexDecidableEq : (s : Factor) → DecidableEq s.Index
  | .one => inferInstanceAs (DecidableEq (Fin 1))
  | .two => inferInstanceAs (DecidableEq (Fin 2))
  | .comp s t => @instDecidableEqProd s.Index t.Index (indexDecidableEq s) (indexDecidableEq t)

def rank : (s : Factor) → s.Index → Nat
  | .one, i => i.val
  | .two, i => i.val
  | .comp s t, i => t.rank i.2 + t.size * s.rank i.1

/-- Exact row-major indexing, proving there are no missing or duplicate bins. -/
def indexEquiv : (s : Factor) → s.Index ≃ Fin s.size
  | .one => Equiv.refl _
  | .two => Equiv.refl _
  | .comp s t => (Equiv.prodCongr s.indexEquiv t.indexEquiv).trans finProdFinEquiv

@[simp] theorem indexEquiv_val (s : Factor) (i : s.Index) :
    (s.indexEquiv i).val = s.rank i := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht =>
    change (t.indexEquiv i.2).val + t.size * (s.indexEquiv i.1).val = _
    rw [iht, ihs]
    rfl

theorem rank_lt (s : Factor) (i : s.Index) : s.rank i < s.size := by
  rw [← indexEquiv_val]
  exact (s.indexEquiv i).isLt

@[reducible] def Data : Factor → Type u → Type u
  | .one, A => A
  | .two, A => A × A
  | .comp s t, A => s.Data (t.Data A)

def get : (s : Factor) → s.Data A → s.Index → A
  | .one, x, _ => x
  | .two, x, i => if i = 0 then x.1 else x.2
  | .comp s t, x, i => t.get (s.get x i.1) i.2

def tabulate : (s : Factor) → (s.Index → A) → s.Data A
  | .one, f => f 0
  | .two, f => (f 0, f 1)
  | .comp s t, f => s.tabulate (fun i => t.tabulate (fun j => f (i, j)))

@[simp] theorem get_tabulate (s : Factor) (f : s.Index → A) (i : s.Index) :
    s.get (s.tabulate f) i = f i := by
  induction s generalizing A with
  | one => have : i = 0 := Subsingleton.elim _ _; subst i; rfl
  | two => fin_cases i <;> simp [get, tabulate]
  | comp s t ihs iht => simp [get, tabulate, ihs, iht]

theorem tabulate_get (s : Factor) (x : s.Data A) : s.tabulate (s.get x) = x := by
  induction s generalizing A with
  | one => rfl
  | two => simp [tabulate, get]
  | comp s t ihs iht =>
    simp only [tabulate, get, iht]
    exact ihs x

theorem data_ext (s : Factor) {x y : s.Data A} (h : ∀ i, s.get x i = s.get y i) : x = y := by
  rw [← tabulate_get s x, ← tabulate_get s y, funext h]

/-- `tabulate` materializes the finite product; it is not a lazy lookup table. -/
def map (s : Factor) (f : A → B) (x : s.Data A) : s.Data B :=
  s.tabulate (fun i => f (s.get x i))

@[simp] theorem get_map (s : Factor) (f : A → B) (x : s.Data A) (i : s.Index) :
    s.get (s.map f x) i = f (s.get x i) := by simp [map]

def transpose (s t : Factor) (x : s.Data (t.Data A)) : t.Data (s.Data A) :=
  t.tabulate (fun j => s.tabulate (fun i => t.get (s.get x i) j))

@[simp] theorem get_transpose (s t : Factor) (x : s.Data (t.Data A))
    (j : t.Index) (i : s.Index) :
    s.get (t.get (s.transpose t x) j) i = t.get (s.get x i) j := by
  simp [transpose]

theorem transpose_transpose (s t : Factor) (x : s.Data (t.Data A)) :
    t.transpose s (s.transpose t x) = x := by
  apply s.data_ext
  intro i
  apply t.data_ext
  intro j
  simp

def reverse : Factor → Factor
  | .one => .one
  | .two => .two
  | .comp s t => .comp t.reverse s.reverse

@[simp] theorem size_reverse (s : Factor) : s.reverse.size = s.size := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht => simp [reverse, size, ihs, iht, Nat.mul_comm]

theorem reverse_reverse (s : Factor) : s.reverse.reverse = s := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht => simp [reverse, ihs, iht]

section Semiring

variable {R : Type u} [CommSemiring R]

/-- The direct DFT coefficient, a sum over every input exactly once. -/
def dft (s : Factor) (ω : R) (x : s.Data R) (k : Nat) : R :=
  ∑ i : s.Index, s.get x i * ω ^ (s.rank i * k)

def twiddle (s t : Factor) (ω : R) (x : s.Data (t.Data R)) : s.Data (t.Data R) :=
  s.tabulate (fun i => t.tabulate
    (fun j => t.get (s.get x i) j * ω ^ (s.rank i * t.rank j)))

@[simp] theorem get_twiddle (s t : Factor) (ω : R) (x : s.Data (t.Data R))
    (i : s.Index) (j : t.Index) :
    t.get (s.get (s.twiddle t ω x) i) j =
      t.get (s.get x i) j * ω ^ (s.rank i * t.rank j) := by
  simp [twiddle]

/--
The two-point kernel uses its supplied root.  At the primitive root `-1`
this is precisely the usual addition/subtraction butterfly.
-/
def fft : (s : Factor) → R → s.Data R → s.reverse.Data R
  | .one, _, x => x
  | .two, ω, x => (x.1 + x.2, x.1 + ω * x.2)
  | .comp s t, ω, x =>
      let columns := t.map (s.fft (ω ^ t.size)) (s.transpose t x)
      let weighted := t.twiddle s.reverse ω columns
      let rows := s.reverse.map (t.fft (ω ^ s.size)) (t.transpose s.reverse weighted)
      s.reverse.transpose t.reverse rows

/-- The algebraic calculation underlying every composition node. -/
theorem twiddle_factorization (ω : R) (m n a b c d : Nat)
    (hω : ω ^ (m * n) = 1) :
    ω ^ ((b + n * a) * (d + m * c)) =
      (ω ^ n) ^ (a * d) * ω ^ (b * d) * (ω ^ m) ^ (b * c) := by
  have he : (b + n * a) * (d + m * c) =
      n * (a * d) + b * d + m * (b * c) + (m * n) * (a * c) := by ring
  rw [he]
  simp only [pow_add, pow_mul, hω, one_pow, mul_one]

/-- Correctness for every factor tree, including arbitrary radix-two depth. -/
theorem fft_correct (s : Factor) (ω : R) (hω : ω ^ s.size = 1)
    (x : s.Data R) (k : s.reverse.Index) :
    s.reverse.get (s.fft ω x) k = s.dft ω x (s.reverse.rank k) := by
  induction s generalizing ω with
  | one => simp [fft, reverse, get, dft, rank, Index]
  | two =>
    fin_cases k <;> simp [fft, reverse, get, dft, rank, Index, Fin.sum_univ_two, mul_comm]
  | comp s t ihs iht =>
    rcases k with ⟨kt, ks⟩
    have hs : (ω ^ t.size) ^ s.size = 1 := by
      rw [← pow_mul, Nat.mul_comm]
      exact hω
    have ht : (ω ^ s.size) ^ t.size = 1 := by
      rw [← pow_mul]
      exact hω
    simp only [fft, reverse, get, get_transpose, get_map]
    rw [iht _ ht]
    simp only [dft, get_transpose, get_twiddle, get_map]
    simp_rw [ihs _ hs]
    simp only [dft, get_transpose, get, rank, size_reverse]
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [twiddle_factorization ω s.size t.size (s.rank i) (t.rank j)
      (t.reverse.rank kt) (s.reverse.rank ks) hω]
    ring

/-- The conventional array DFT.  The kernel above does not invoke it. -/
def directDFT {n m : Nat} (ω : R) (x : Fin n → R) (k : Fin m) : R :=
  ∑ i : Fin n, x i * ω ^ (i.val * k.val)

def decode (s : Factor) (x : s.Data R) : Fin s.size → R :=
  fun i => s.get x (s.indexEquiv.symm i)

theorem dft_eq_direct (s : Factor) (ω : R) (x : s.Data R) (k : Nat) :
    s.dft ω x k = ∑ i : Fin s.size, s.decode x i * ω ^ (i.val * k) := by
  simpa [dft, decode] using
    (s.indexEquiv.sum_comp (fun i : Fin s.size => s.decode x i * ω ^ (i.val * k)))

def rep (s : Factor) (R : Type u) : Squares.Rep where
  R := s.Data R
  S := Fin s.size → R
  decode := s.decode

theorem fft_decode (s : Factor) (ω : R) (hω : ω ^ s.size = 1) (x : s.Data R) :
    s.reverse.decode (s.fft ω x) = directDFT ω (s.decode x) := by
  funext k
  unfold decode
  rw [fft_correct s ω hω, dft_eq_direct]
  have hk : s.reverse.rank (s.reverse.indexEquiv.symm k) = k.val := by simp [← indexEquiv_val]
  simp only [hk, directDFT, decode]

/-- The full, shape-changing computation and its denotation as one square. -/
def fftSquare (s : Factor) (ω : R) (hω : ω ^ s.size = 1) :
    Squares.Square (s.rep R) (s.reverse.rep R) where
  impl := s.fft ω
  spec := directDFT ω
  commutes := s.fft_decode ω hω

end Semiring

theorem two_butterfly {R : Type u} [CommRing R] (a b : R) :
    Factor.two.fft (-1) (a, b) = (a + b, a - b) := by
  simp [fft, sub_eq_add_neg]

def rightPow : Nat → Factor
  | 0 => .one
  | n + 1 => .comp .two (rightPow n)

def leftPow : Nat → Factor
  | 0 => .one
  | n + 1 => .comp (leftPow n) .two

def bush : Nat → Factor
  | 0 => .two
  | n + 1 => .comp (bush n) (bush n)

theorem size_rightPow (n : Nat) : (rightPow n).size = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightPow, size, ih, Nat.pow_succ, Nat.mul_comm]

theorem size_leftPow (n : Nat) : (leftPow n).size = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftPow, size, ih, Nat.pow_succ]

theorem reverse_rightPow (n : Nat) : (rightPow n).reverse = leftPow n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightPow, leftPow, reverse, ih]

end Factor
end Applications.Parallel

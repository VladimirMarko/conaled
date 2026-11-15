import Applications.Parallel.ComplexFFT
import Mathlib.Tactic.Linarith

/-!
# Explicit Fourier expressions and structural operation sites

The expression interpretation preserves the existing semiring algorithm, including
its supplied root. Structural sites count expanded butterfly invocations and
nonzero-exponent twiddle occurrences. These are not retained real arithmetic gates.
-/
namespace Applications.Parallel
namespace Factor

/-- Interpret a recipe using supplied addition and constant multiplication. -/
def runWith {R A : Type*} [CommSemiring R] (add : A → A → A) (scale : R → A → A) :
    (s : Factor) → R → s.Data A → s.reverse.Data A
  | .one, _, x => x
  | .two, ω, x => (add x.1 x.2, add x.1 (scale ω x.2))
  | .comp s t, ω, x =>
      let columns := t.map (s.runWith add scale (ω ^ t.size)) (s.transpose t x)
      let weighted := t.tabulate (fun i => s.reverse.tabulate
        (fun j => scale (ω ^ (t.rank i * s.reverse.rank j))
          (s.reverse.get (t.get columns i) j)))
      let rows := s.reverse.map (t.runWith add scale (ω ^ s.size))
        (t.transpose s.reverse weighted)
      s.reverse.transpose t.reverse rows

/-- Evaluation of operations commutes with the entire shape-changing recipe. -/
theorem runWith_erases {R A : Type*} [CommSemiring R]
    (add : A → A → A) (scale : R → A → A) (eval : A → R)
    (ha : ∀ a b, eval (add a b) = eval a + eval b)
    (hs : ∀ c a, eval (scale c a) = c * eval a)
    (s : Factor) (ω : R) (x : s.Data A) :
    s.reverse.map eval (s.runWith add scale ω x) = s.fft ω (s.map eval x) := by
  induction s generalizing ω with
  | one => rfl
  | two => simp [runWith, fft, reverse, map, tabulate, get, ha, hs]
  | comp s t ihs iht =>
    apply (Factor.comp t.reverse s.reverse).data_ext
    rintro ⟨i, j⟩
    simp only [runWith, fft, reverse]
    rw [get_map]
    simp only [get, get_transpose, get_map]
    have ht := congrArg (fun z => t.reverse.get z i) (iht (ω ^ s.size)
      (s.reverse.get ((t.transpose s.reverse
        (t.tabulate fun a => s.reverse.tabulate fun b =>
          scale (ω ^ (t.rank a * s.reverse.rank b))
            (s.reverse.get (t.get
              (t.map (s.runWith add scale (ω ^ t.size)) (s.transpose t x)) a) b)))) j))
    simp only [get_map] at ht
    rw [ht]
    congr 1
    apply congrArg (t.fft (ω ^ s.size))
    apply t.data_ext
    intro a
    simp only [get_map, get_transpose, get_tabulate, hs, get_twiddle]
    have hleft := congrArg (fun z => s.reverse.get z j)
      (ihs (ω ^ t.size) (t.get (s.transpose t x) a))
    simp only [get_map] at hleft
    rw [hleft, mul_comm]
    congr 2
    apply congrArg (s.fft (ω ^ t.size))
    apply s.data_ext
    intro b
    simp only [get_map, get_transpose]
    exact (get_map (Factor.comp s t) eval x (b, a)).symm

/-- Circuit expressions are exact, with precomputed scalar constants. -/
inductive Expr (R : Type*) where
  | input (index : Nat)
  | add (left right : Expr R)
  | scale (constant : R) (value : Expr R)

namespace Expr

def eval {R : Type*} [CommSemiring R] (v : Nat → R) : Expr R → R
  | .input i => v i
  | .add a b => eval v a + eval v b
  | .scale c a => c * eval v a

end Expr

def expressions {R : Type*} [CommSemiring R] (s : Factor) (ω : R)
    (inputs : s.Data (Expr R)) : s.reverse.Data (Expr R) :=
  s.runWith Expr.add Expr.scale ω inputs

theorem expressions_eval {R : Type*} [CommSemiring R] (s : Factor) (ω : R)
    (v : Nat → R) (inputs : s.Data (Expr R)) :
    s.reverse.map (Expr.eval v) (s.expressions ω inputs) =
      s.fft ω (s.map (Expr.eval v) inputs) :=
  runWith_erases _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) s ω inputs

theorem expressions_decode {R : Type*} [CommSemiring R] (s : Factor) (ω : R)
    (hω : ω ^ s.size = 1) (v : Nat → R) (inputs : s.Data (Expr R)) :
    s.reverse.decode (s.reverse.map (Expr.eval v) (s.expressions ω inputs)) =
      directDFT ω (s.decode (s.map (Expr.eval v) inputs)) := by
  rw [expressions_eval]
  exact s.fft_decode ω hω _

/-- Expanded structural sites. The two families at a composition node have
separate occurrence identities even when their scalar expressions agree. -/
inductive Site : Factor → Type where
  | butterfly : Site .two
  | column {s t : Factor} (index : t.Index) (site : Site s) : Site (.comp s t)
  | row {s t : Factor} (index : s.reverse.Index) (site : Site t) : Site (.comp s t)
  | twiddle {s t : Factor} (i : t.Index) (j : s.reverse.Index) : Site (.comp s t)

/-- Enumerate every recursive butterfly invocation with its column/row address. -/
def butterflySites : (s : Factor) → List (Site s)
  | .one => []
  | .two => [.butterfly]
  | .comp s t =>
      (List.ofFn fun i : Fin t.size =>
        s.butterflySites.map (Site.column (t.indexEquiv.symm i))).flatten ++
      (List.ofFn fun j : Fin s.reverse.size =>
        t.butterflySites.map (Site.row (s.reverse.indexEquiv.symm j))).flatten

/-- Nonzero row/column indices in a twiddle rectangle. -/
def positiveIndex (s : Factor) (i : Fin (s.size - 1)) : s.Index :=
  s.indexEquiv.symm ⟨i.val + 1, by have := i.isLt; have := s.size_pos; omega⟩

@[simp] theorem rank_positiveIndex (s : Factor) (i : Fin (s.size - 1)) :
    s.rank (s.positiveIndex i) = i.val + 1 := by
  simp [positiveIndex, ← indexEquiv_val]

def twiddleSites : (s : Factor) → List (Site s)
  | .one => []
  | .two => []
  | .comp s t =>
      (List.ofFn fun i : Fin t.size =>
        s.twiddleSites.map (Site.column (t.indexEquiv.symm i))).flatten ++
      (List.ofFn fun j : Fin s.reverse.size =>
        t.twiddleSites.map (Site.row (s.reverse.indexEquiv.symm j))).flatten ++
      (List.ofFn fun i : Fin (t.size - 1) => List.ofFn fun j : Fin (s.reverse.size - 1) =>
        Site.twiddle (t.positiveIndex i) (s.reverse.positiveIndex j)).flatten

def butterflies : Factor → Nat
  | .one => 0
  | .two => 1
  | .comp s t => t.size * s.butterflies + s.size * t.butterflies

def twiddles : Factor → Nat
  | .one => 0
  | .two => 0
  | .comp s t => t.size * s.twiddles + s.size * t.twiddles + (s.size - 1) * (t.size - 1)

theorem butterflySites_length (s : Factor) : s.butterflySites.length = s.butterflies := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht =>
    simp [butterflySites, butterflies, List.length_flatten, List.map_ofFn, Function.comp_def,
      ihs, iht, List.ofFn_const, List.sum_replicate]

theorem twiddleSites_length (s : Factor) : s.twiddleSites.length = s.twiddles := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht =>
    simp [twiddleSites, twiddles, List.length_flatten, List.map_ofFn, Function.comp_def,
      ihs, iht, List.ofFn_const, List.sum_replicate, Nat.mul_comm, Nat.add_assoc]

/-- A circuit retains outputs and its expanded operation-site inventory.
Each stage is the corresponding stage of runWith, including the reversed shape. -/
structure Circuit (s : Factor) (R : Type*) where
  outputs : s.reverse.Data (Expr R)
  butterflies : List (Site s)
  twiddles : List (Site s)

def compile {R : Type*} [CommSemiring R] (s : Factor) (ω : R)
    (inputs : s.Data (Expr R)) : Circuit s R :=
  ⟨s.expressions ω inputs, s.butterflySites, s.twiddleSites⟩

theorem compile_counts {R : Type*} [CommSemiring R] (s : Factor) (ω : R)
    (inputs : s.Data (Expr R)) :
    (s.compile ω inputs).butterflies.length = s.butterflies ∧
      (s.compile ω inputs).twiddles.length = s.twiddles :=
  ⟨s.butterflySites_length, s.twiddleSites_length⟩

theorem nonidentity_twiddle {R : Type*} [CommMonoid R] (s t : Factor) (ω : R)
    (hω : IsPrimitiveRoot ω (s.size * t.size))
    (i : Fin (t.size - 1)) (j : Fin (s.reverse.size - 1)) :
    ω ^ (t.rank (t.positiveIndex i) * s.reverse.rank (s.reverse.positiveIndex j)) ≠ 1 := by
  apply hω.pow_ne_one_of_pos_of_lt
  · simp
  · rw [rank_positiveIndex, rank_positiveIndex]
    have hi := (t.positiveIndex i |> t.rank_lt)
    have hj := (s.reverse.positiveIndex j |> s.reverse.rank_lt)
    simp only [rank_positiveIndex, size_reverse] at hi hj
    have := Nat.mul_lt_mul_of_pos_left hi (by omega : 0 < j.val + 1)
    nlinarith [s.size_pos, t.size_pos]

/-- Exactly the omitted zero-index rows and columns are identity twiddles
when the root is primitive. -/
theorem twiddle_eq_one_iff {R : Type*} [CommMonoid R] (s t : Factor) (ω : R)
    (hω : IsPrimitiveRoot ω (s.size * t.size)) (i : t.Index) (j : s.reverse.Index) :
    ω ^ (t.rank i * s.reverse.rank j) = 1 ↔ t.rank i = 0 ∨ s.reverse.rank j = 0 := by
  constructor
  · intro h
    by_contra hz
    have hi : t.rank i ≠ 0 := fun h0 => hz (Or.inl h0)
    have hj : s.reverse.rank j ≠ 0 := fun h0 => hz (Or.inr h0)
    apply hω.pow_ne_one_of_pos_of_lt (Nat.mul_ne_zero hi hj) _ h
    have hit := t.rank_lt i
    have hjs := s.reverse.rank_lt j
    rw [size_reverse] at hjs
    have hb := Nat.mul_lt_mul_of_pos_left hit (by omega : 0 < s.reverse.rank j)
    nlinarith [s.size_pos, t.size_pos]
  · rintro (h | h) <;> simp [h]

def logSize : Factor → Nat
  | .one => 0
  | .two => 1
  | .comp s t => s.logSize + t.logSize

theorem size_eq_pow (s : Factor) : s.size = 2 ^ s.logSize := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht => simp [size, logSize, pow_add, ihs, iht]

theorem twice_butterflies (s : Factor) : 2 * s.butterflies = s.logSize * s.size := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht =>
    simp only [butterflies, logSize, size]
    nlinarith

/-- This formulation avoids truncated-subtraction errors at sizes one and two. -/
theorem twiddles_add_size (s : Factor) : s.twiddles + s.size = s.butterflies + 1 := by
  induction s with
  | one => rfl
  | two => rfl
  | comp s t ihs iht =>
    have hs := s.size_pos
    have ht := t.size_pos
    have hsm : s.size - 1 + 1 = s.size := by omega
    have htm : t.size - 1 + 1 = t.size := by omega
    simp only [twiddles, butterflies, size]
    nlinarith

theorem butterflies_closed (s : Factor) : s.butterflies = s.logSize * s.size / 2 := by
  rw [← twice_butterflies]
  omega

theorem twiddles_closed (s : Factor) :
    s.twiddles = (s.logSize * s.size / 2 + 1) - s.size := by
  rw [← butterflies_closed]
  have := s.twiddles_add_size
  omega

theorem butterflies_assoc (r s t : Factor) :
    (Factor.comp (Factor.comp r s) t).butterflies = (Factor.comp r (Factor.comp s t)).butterflies := by
  simp only [butterflies, size]
  ring

theorem twiddles_assoc (r s t : Factor) :
    (Factor.comp (Factor.comp r s) t).twiddles = (Factor.comp r (Factor.comp s t)).twiddles := by
  have h₁ := (Factor.comp (Factor.comp r s) t).twiddles_add_size
  have h₂ := (Factor.comp r (Factor.comp s t)).twiddles_add_size
  have hb := butterflies_assoc r s t
  simp only [size, Nat.mul_assoc] at h₁ h₂
  omega

theorem counts_of_same_size (s t : Factor) (h : s.size = t.size) :
    s.butterflies = t.butterflies ∧ s.twiddles = t.twiddles := by
  have he : s.logSize = t.logSize :=
    Nat.pow_right_injective (by decide : 2 ≤ 2)
      (s.size_eq_pow.symm.trans (h.trans t.size_eq_pow))
  constructor
  · rw [s.butterflies_closed, t.butterflies_closed, h, he]
  · rw [s.twiddles_closed, t.twiddles_closed, h, he]

theorem logSize_rightPow (k : Nat) : (rightPow k).logSize = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rightPow, logSize, ih, Nat.add_comm]

theorem radix_two_counts (k : Nat) :
    (rightPow k).butterflies = k * 2 ^ k / 2 ∧
    (rightPow k).twiddles = (k * 2 ^ k / 2 + 1) - 2 ^ k := by
  simp [butterflies_closed, twiddles_closed, logSize_rightPow, size_rightPow]

end Factor
end Applications.Parallel

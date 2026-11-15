import Applications.Parallel.MeasuredFFT
import Applications.Parallel.FFTRoots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact scalar Fourier rewrites

Arithmetic gates have explicit local labels. Equal referenced nodes are shared;
there is no algebraic common-subexpression elimination. Signs and wiring are
free. Constants are precomputed. Each real add/subtract or constant multiply
has unit work and latency. This is an exact mathematical circuit model.
-/
namespace Applications.Parallel.FFTScalar

/-- Named exact coefficients; these remain executable syntax. -/
inductive Constant where
  | cosine (denominator exponent : Nat)
  | sine (denominator exponent : Nat)
  | diagonal
  deriving BEq, ReflBEq, LawfulBEq, Repr

instance : DecidableEq Constant := instDecidableEqOfLawfulBEq

noncomputable def Constant.eval : Constant → ℝ
  | .cosine n k => Real.cos (-(2 * Real.pi * k / n))
  | .sine n k => Real.sin (-(2 * Real.pi * k / n))
  | .diagonal => Real.sqrt 2 / 2

/-- Gate labels distinguish deliberately distinct multiplication sites. -/
inductive Wire where
  | input (index : Nat)
  | neg (value : Wire)
  | add (label : List Nat) (left right : Wire)
  | sub (label : List Nat) (left right : Wire)
  | mul (label : List Nat) (constant : Constant) (value : Wire)
  deriving BEq, ReflBEq, LawfulBEq, Repr

instance : DecidableEq Wire := instDecidableEqOfLawfulBEq

namespace Wire

noncomputable def eval (inputs : Nat → ℝ) : Wire → ℝ
  | .input i => inputs i
  | .neg a => -eval inputs a
  | .add _ a b => eval inputs a + eval inputs b
  | .sub _ a b => eval inputs a - eval inputs b
  | .mul _ c a => c.eval * eval inputs a

def arrival (inputs : Nat → Nat) : Wire → Nat
  | .input i => inputs i
  | .neg a => arrival inputs a
  | .add _ a b | .sub _ a b => max (arrival inputs a) (arrival inputs b) + 1
  | .mul _ _ a => arrival inputs a + 1

def gates : Wire → Finset Wire
  | .input _ => ∅
  | .neg a => a.gates
  | w@(.add _ a b) | w@(.sub _ a b) => insert w (a.gates ∪ b.gates)
  | w@(.mul _ _ a) => insert w a.gates

def isMul : Wire → Bool
  | .mul .. => true
  | _ => false

end Wire

abbrev ComplexWire := Wire × Wire

noncomputable def value (v : Nat → ℝ) (z : ComplexWire) : ℂ :=
  ⟨z.1.eval v, z.2.eval v⟩

def plus (p : List Nat) (z w : ComplexWire) : ComplexWire :=
  (.add (0 :: p) z.1 w.1, .add (1 :: p) z.2 w.2)

def minus (p : List Nat) (z w : ComplexWire) : ComplexWire :=
  (.sub (0 :: p) z.1 w.1, .sub (1 :: p) z.2 w.2)

def quarter (z : ComplexWire) : ComplexWire := (z.2, .neg z.1)

/-- Four distinct product sites, followed by two add/subtract sites. -/
def general (p : List Nat) (c d : Constant) (z : ComplexWire) : ComplexWire :=
  (.sub (4 :: p) (.mul (0 :: p) c z.1) (.mul (1 :: p) d z.2),
   .add (5 :: p) (.mul (2 :: p) d z.1) (.mul (3 :: p) c z.2))

/-- Multiply by (1-i)/sqrt(2) with two products. -/
def diagonal (p : List Nat) (z : ComplexWire) : ComplexWire :=
  (.mul (2 :: p) .diagonal (.add (0 :: p) z.1 z.2),
   .mul (3 :: p) .diagonal (.sub (1 :: p) z.2 z.1))

@[simp] theorem value_plus (v : Nat → ℝ) (p : List Nat) (z w : ComplexWire) :
    value v (plus p z w) = value v z + value v w := by
  apply Complex.ext <;> rfl

@[simp] theorem value_minus (v : Nat → ℝ) (p : List Nat) (z w : ComplexWire) :
    value v (minus p z w) = value v z - value v w := by
  apply Complex.ext <;> rfl

theorem value_quarter (v : Nat → ℝ) (z : ComplexWire) :
    value v (quarter z) = value v z * (-Complex.I) := by
  apply Complex.ext <;> simp [value, quarter, Wire.eval, Complex.mul_re, Complex.mul_im]

theorem value_general (v : Nat → ℝ) (p : List Nat) (c d : Constant) (z : ComplexWire) :
    value v (general p c d z) = value v z * (⟨c.eval, d.eval⟩ : ℂ) := by
  apply Complex.ext <;> simp [value, general, Wire.eval, Complex.mul_re, Complex.mul_im] <;> ring

theorem value_diagonal (v : Nat → ℝ) (p : List Nat) (z : ComplexWire) :
    value v (diagonal p z) = value v z *
      (⟨Real.sqrt 2 / 2, -(Real.sqrt 2 / 2)⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [value, diagonal, Wire.eval, Constant.eval, Complex.mul_re, Complex.mul_im] <;> ring

theorem diagonal_arrivals (t : Nat → Nat) (p : List Nat) (z : ComplexWire) :
    (diagonal p z).1.arrival t = max (z.1.arrival t) (z.2.arrival t) + 2 ∧
    (diagonal p z).2.arrival t = max (z.1.arrival t) (z.2.arrival t) + 2 := by
  simp [diagonal, Wire.arrival, Nat.add_assoc, max_comm]

theorem general_arrivals (t : Nat → Nat) (p : List Nat) (c d : Constant) (z : ComplexWire) :
    (general p c d z).1.arrival t = max (z.1.arrival t) (z.2.arrival t) + 2 ∧
    (general p c d z).2.arrival t = max (z.1.arrival t) (z.2.arrival t) + 2 := by
  simp [general, Wire.arrival, Nat.add_assoc, max_add_add_right]

structure Circuit where
  outputs : List Wire

def Circuit.retained (c : Circuit) : Finset Wire :=
  (c.outputs.map Wire.gates).foldl (· ∪ ·) ∅

def Circuit.work (c : Circuit) : Nat := c.retained.card

def Circuit.multiplications (c : Circuit) : Nat := (c.retained.filter (fun w => w.isMul = true)).card

def Circuit.additions (c : Circuit) : Nat := (c.retained.filter (fun w => w.isMul = false)).card

def Circuit.depth (c : Circuit) : Nat :=
  (c.outputs.map (Wire.arrival (fun _ => 0))).foldl max 0

/-- Rewrite only recognized exact angles; other constants retain their exact
trigonometric meaning. Denominators are positive in every compiled recipe. -/
def twiddle (optimized : Bool) (p : List Nat) (n k : Nat) (z : ComplexWire) : ComplexWire :=
  if k = 0 then z
  else if 4 * k = n then quarter z
  else if optimized && 8 * k = n then diagonal p z
  else if optimized && 8 * k = 3 * n then quarter (diagonal p z)
  else if optimized && 8 * k = 5 * n then quarter (quarter (diagonal p z))
  else if optimized && 8 * k = 7 * n then quarter (quarter (quarter (diagonal p z)))
  else general p (.cosine n k) (.sine n k) z

theorem value_twiddle (v : Nat → ℝ) (optimized : Bool) (p : List Nat)
    (n k : Nat) (hn : 0 < n) (z : ComplexWire) :
    value v (twiddle optimized p n k z) = value v z * phase n k := by
  unfold twiddle
  split
  · rename_i h; subst k; rw [phase_zero, mul_one]
  · split
    · rename_i h
      rw [value_quarter, phase_ratio (j := 1) hn (by decide : 0 < 4) (by simpa using h), phase_quarter]
    · split
      · rename_i h
        have h' : 8 * k = n := by simpa using (show optimized = true ∧ _ from by simpa using h).2
        rw [value_diagonal, phase_ratio (j := 1) hn (by decide : 0 < 8) (by simpa using h'), phase_diagonal]
      · split
        · rename_i h
          have h' : 8 * k = 3 * n := by simpa using (show optimized = true ∧ _ from by simpa using h).2
          rw [value_quarter, value_diagonal, phase_ratio hn (by decide : 0 < 8) h']
          have hp := phase_eight_odd 1
          norm_num at hp
          rw [hp, phase_diagonal]
          ring
        · split
          · rename_i h
            have h' : 8 * k = 5 * n := by simpa using (show optimized = true ∧ _ from by simpa using h).2
            rw [value_quarter, value_quarter, value_diagonal,
              phase_ratio hn (by decide : 0 < 8) h']
            have hp := phase_eight_odd 2
            norm_num only at hp
            rw [hp, phase_diagonal]
            ring
          · split
            · rename_i h
              have h' : 8 * k = 7 * n := by simpa using (show optimized = true ∧ _ from by simpa using h).2
              rw [value_quarter, value_quarter, value_quarter, value_diagonal,
                phase_ratio hn (by decide : 0 < 8) h']
              have hp := phase_eight_odd 3
              norm_num only at hp
              rw [hp, phase_diagonal]
              ring
            · rw [value_general, phase_coefficients]
              rfl

/-- Each recursive invocation and scalar operation carries its construction
address. Reusing an output reuses its gate; distinct sites are not merged. -/
def lower (optimized : Bool) : (s : Factor) → List Nat →
    s.Data ComplexWire → s.reverse.Data ComplexWire
  | .one, _, x => x
  | .two, p, x => (plus (0 :: p) x.1 x.2, minus (1 :: p) x.1 x.2)
  | .comp s t, p, x =>
      let columns := t.tabulate (fun i => lower optimized s (0 :: t.rank i :: p)
        (t.get (s.transpose t x) i))
      let weighted := t.tabulate (fun i => s.reverse.tabulate
        (fun j => twiddle optimized (1 :: t.rank i :: s.reverse.rank j :: p)
          (s.size * t.size) (t.rank i * s.reverse.rank j)
          (s.reverse.get (t.get columns i) j)))
      let rows := s.reverse.tabulate (fun j => lower optimized t
        (2 :: s.reverse.rank j :: p) (s.reverse.get (t.transpose s.reverse weighted) j))
      s.reverse.transpose t.reverse rows

/-- Scalar lowering erases to the original recursively factored algorithm. -/
theorem lower_erases (v : Nat → ℝ) (optimized : Bool) (s : Factor)
    (p : List Nat) (x : s.Data ComplexWire) :
    s.reverse.map (value v) (lower optimized s p x) =
      s.fft (phase s.size 1) (s.map (value v) x) := by
  induction s generalizing p with
  | one => rfl
  | two =>
    simp [lower, Factor.fft, Factor.reverse, Factor.size, Factor.map,
      Factor.tabulate, Factor.get, phase_two, value_plus, value_minus, sub_eq_add_neg]
  | comp s t ihs iht =>
    have hsroot := phase_child s t
    have htroot := phase_child t s
    rw [Nat.mul_comm t.size s.size] at htroot
    apply (Factor.comp t.reverse s.reverse).data_ext
    rintro ⟨i, j⟩
    simp only [lower, Factor.fft, Factor.reverse, Factor.size, hsroot, htroot]
    rw [Factor.get_map]
    simp only [Factor.get, Factor.get_transpose, Factor.get_tabulate, Factor.get_map]
    have ht := congrArg (fun z => t.reverse.get z i) (iht
      (2 :: s.reverse.rank j :: p)
      (s.reverse.get (t.transpose s.reverse
        (t.tabulate fun a => s.reverse.tabulate fun b =>
          twiddle optimized (1 :: t.rank a :: s.reverse.rank b :: p)
            (s.size * t.size) (t.rank a * s.reverse.rank b)
            (s.reverse.get (lower optimized s (0 :: t.rank a :: p)
              (t.get (s.transpose t x) a)) b))) j))
    simp only [Factor.get_map] at ht
    rw [ht]
    congr 1
    apply congrArg (t.fft (phase t.size 1))
    apply t.data_ext
    intro a
    simp only [Factor.get_map, Factor.get_transpose, Factor.get_tabulate,
      value_twiddle v optimized _ _ _ (Nat.mul_pos s.size_pos t.size_pos), Factor.get_twiddle]
    have hl := congrArg (fun z => s.reverse.get z j)
      (ihs (0 :: t.rank a :: p) (t.get (s.transpose t x) a))
    simp only [Factor.get_map] at hl
    rw [hl, phase_pow, one_mul]
    congr 2
    apply congrArg (s.fft (phase s.size 1))
    apply s.data_ext
    intro b
    simp only [Factor.get_map, Factor.get_transpose]
    exact (Factor.get_map (Factor.comp s t) (value v) x (b, a)).symm

theorem lower_fourier (v : Nat → ℝ) (optimized : Bool) (s : Factor)
    (p : List Nat) (x : s.Data ComplexWire) :
    s.reverse.decode (s.reverse.map (value v) (lower optimized s p x)) =
      Factor.directDFT s.fourierRoot (s.decode (s.map (value v) x)) := by
  rw [lower_erases, phase_fourierRoot]
  exact s.fourier_correct _

def inputs (s : Factor) : s.Data ComplexWire :=
  s.tabulate fun i => (.input (2 * s.rank i), .input (2 * s.rank i + 1))

def circuit (optimized : Bool) (s : Factor) : Circuit :=
  let out := lower optimized s [] (inputs s)
  ⟨(List.ofFn (fun i : Fin s.reverse.size =>
    s.reverse.get out (s.reverse.indexEquiv.symm i))).flatMap fun z => [z.1, z.2]⟩

/-- A two-port block exposes local rewrite work separately from its context.
The six-operation baseline counts distinct sites even when coefficients coincide. -/
def block (z : ComplexWire) : Circuit := ⟨[z.1, z.2]⟩

theorem isolated_rewrite_costs :
    (block (general [] (.cosine 8 1) (.sine 8 1) (.input 0, .input 1))).work = 6 ∧
    (block (diagonal [] (.input 0, .input 1))).work = 4 ∧
    (block (quarter (.input 0, .input 1))).work = 0 := by decide

theorem diagonal_rewrite (v : Nat → ℝ) (p : List Nat) (z : ComplexWire) :
    value v (diagonal p z) = value v (general p (.cosine 8 1) (.sine 8 1) z) := by
  rw [value_general, value_diagonal]
  rw [← phase_diagonal, phase_coefficients]
  rfl

theorem diagonal_rewrite_arrivals (t : Nat → Nat) (p : List Nat) (z : ComplexWire) :
    ((diagonal p z).1.arrival t, (diagonal p z).2.arrival t) =
      ((general p (.cosine 8 1) (.sine 8 1) z).1.arrival t,
       (general p (.cosine 8 1) (.sine 8 1) z).2.arrival t) := by
  rw [(diagonal_arrivals t p z).1, (diagonal_arrivals t p z).2,
    (general_arrivals t p (.cosine 8 1) (.sine 8 1) z).1,
    (general_arrivals t p (.cosine 8 1) (.sine 8 1) z).2]

theorem quarter_rewrite (v : Nat → ℝ) (p : List Nat) (z : ComplexWire) :
    value v (quarter z) = value v (general p (.cosine 4 1) (.sine 4 1) z) := by
  rw [value_quarter, value_general, ← phase_quarter, phase_coefficients]
  rfl

theorem quarter_rewrite_arrivals (t : Nat → Nat) (p : List Nat) (z : ComplexWire) :
    (quarter z).1.arrival t ≤ (general p (.cosine 4 1) (.sine 4 1) z).1.arrival t ∧
    (quarter z).2.arrival t ≤ (general p (.cosine 4 1) (.sine 4 1) z).2.arrival t := by
  rw [(general_arrivals t p (.cosine 4 1) (.sine 4 1) z).1,
    (general_arrivals t p (.cosine 4 1) (.sine 4 1) z).2]
  simp only [quarter, Wire.arrival]
  omega

end Applications.Parallel.FFTScalar

import Applications.Convolution.Series

/-!
# Sparse noncommutative polynomials as an executable representation

A polynomial is a finite association list of words and coefficients. Duplicate
keys and zero coefficients are permitted. Addition appends, multiplication
distributes over all term pairs, and normalization combines duplicate keys.
The representation therefore has a deliberately noninjective decoder. Every
operation below is certified against `Series`; no syntactic semiring laws are
postulated for association lists.
-/

namespace Convolution

universe u v
variable {α : Type u} {R : Type v} [DecidableEq α] [Semiring R]

def prepend (a : α) (f : Series α R) : Series α R := ⟨fun w =>
  match w with
  | [] => 0
  | b :: v => if a = b then f v else 0⟩

def monomial : List α → R → Series α R
  | [], r => ⟨fun w => match w with | [] => r | _ :: _ => 0⟩
  | a :: u, r => prepend a (monomial u r)

theorem monomial_apply (u w : List α) (r : R) :
    monomial u r w = if u = w then r else 0 := by
  induction u generalizing w with
  | nil => cases w <;> simp [monomial]
  | cons a u ih =>
    cases w with
    | nil => simp [monomial, prepend]
    | cons b w =>
      by_cases h : a = b
      · subst b; simp [monomial, prepend, ih]
      · simp [monomial, prepend, h]

theorem monomial_add (u : List α) (r s : R) :
    monomial u (r + s) = monomial u r + monomial u s := by
  apply Series.ext_coeff; intro w
  simp only [monomial_apply, add_apply]
  split <;> simp

theorem monomial_zero (u : List α) : monomial u (0 : R) = 0 := by
  apply Series.ext_coeff; intro w; simp [monomial_apply]

theorem prepend_mul (a : α) (f g : Series α R) :
    prepend a f * g = prepend a (f * g) := by
  apply Series.ext_coeff; intro w
  cases w with
  | nil => simp [prepend]
  | cons b w =>
    by_cases h : a = b
    · subst b; simp [prepend, convolution]; rfl
    · simp [prepend, convolution, h]
      have hz := zero_mul g
      exact congrArg (fun k : Series α R => k w) hz

theorem scale_monomial (r : R) (u : List α) (s : R) :
    scale r (monomial u s) = monomial u (r * s) := by
  apply Series.ext_coeff; intro w
  simp only [scale, monomial_apply]
  split <;> simp

theorem prepend_scale (a : α) (r : R) (f : Series α R) :
    prepend a (scale r f) = scale r (prepend a f) := by
  apply Series.ext_coeff; intro w
  cases w with
  | nil => simp [prepend, scale]
  | cons b w => by_cases h : a = b <;> simp [prepend, scale, h]

theorem monomial_mul (u v : List α) (r s : R) :
    monomial u r * monomial v s = monomial (u ++ v) (r * s) := by
  induction u with
  | nil =>
    have he : monomial [] r = scale r (1 : Series α R) := by
      apply Series.ext_coeff; intro w; cases w <;> simp [monomial, scale]
    rw [he]
    calc
      scale r 1 * monomial v s = scale r (1 * monomial v s) :=
        Series.ext_coeff (conv_scale_left r _ _)
      _ = monomial v (r * s) := by rw [one_mul, scale_monomial]
      _ = monomial ([] ++ v) (r * s) := rfl
  | cons a u ih => simp only [monomial, List.cons_append, prepend_mul, ih]

/-- Sparse terms; duplicates are summed by the decoder. -/
abbrev Polynomial (α : Type u) (R : Type v) := List (List α × R)

namespace Polynomial

def denote : Polynomial α R → Series α R
  | [] => 0
  | (u, r) :: p => monomial u r + denote p

def add (p q : Polynomial α R) : Polynomial α R := p ++ q

def mul (p q : Polynomial α R) : Polynomial α R :=
  p.flatMap (fun ur => q.map (fun vs => (ur.1 ++ vs.1, ur.2 * vs.2)))

def one : Polynomial α R := [([], 1)]

theorem denote_append (p q : Polynomial α R) : denote (p ++ q) = denote p + denote q := by
  induction p with
  | nil => simp [denote]
  | cons ur p ih => cases ur; simp [denote, ih, add_assoc]

theorem denote_map_left (u : List α) (r : R) (q : Polynomial α R) :
    denote (q.map (fun vs => (u ++ vs.1, r * vs.2))) = monomial u r * denote q := by
  induction q with
  | nil => simp [denote]
  | cons vs q ih => cases vs; simp [denote, ih, mul_add, monomial_mul]

theorem denote_mul (p q : Polynomial α R) : denote (mul p q) = denote p * denote q := by
  induction p with
  | nil => simp [mul, denote]
  | cons ur p ih =>
    rcases ur with ⟨u, r⟩
    change denote (q.map (fun vs => (u ++ vs.1, r * vs.2)) ++ mul p q) = _
    rw [denote_append, denote_map_left, ih]
    simp only [denote, add_mul]

theorem denote_one : denote (one : Polynomial α R) = 1 := by
  apply Series.ext_coeff; intro w; cases w <;> simp [one, denote, monomial]

/-- Add a coefficient at a key; equality here is only equality of finite words. -/
def insert (u : List α) (r : R) : Polynomial α R → Polynomial α R
  | [] => [(u, r)]
  | (v, s) :: p =>
    if u = v then (v, r + s) :: p else (v, s) :: insert u r p

theorem denote_insert (u : List α) (r : R) (p : Polynomial α R) :
    denote (insert u r p) = monomial u r + denote p := by
  induction p with
  | nil => simp [insert, denote]
  | cons vs p ih =>
    rcases vs with ⟨v, s⟩
    by_cases h : u = v
    · subst v; simp [insert, denote, monomial_add, add_assoc]
    · simp only [insert, ite_eq_right h, denote, ih]
      ac_rfl

def normalize : Polynomial α R → Polynomial α R
  | [] => []
  | (u, r) :: p => insert u r (normalize p)

theorem denote_normalize (p : Polynomial α R) : denote (normalize p) = denote p := by
  induction p with
  | nil => rfl
  | cons ur p ih => cases ur; simp [normalize, denote_insert, denote, ih]

theorem mul_assoc_semantics (p q r : Polynomial α R) :
    denote (mul (mul p q) r) = denote (mul p (mul q r)) := by
  simp only [denote_mul, mul_assoc]

theorem normalized_mul_correct (p q : Polynomial α R) :
    denote (normalize (mul p q)) = denote p * denote q := by
  rw [denote_normalize, denote_mul]

@[reducible] def rep (α : Type u) (R : Type v) [DecidableEq α] [Semiring R] : Squares.Rep.{max u v} where
  R := Polynomial α R
  S := Series α R
  decode := denote

def addSquare : Squares.Square (Squares.product (rep α R) (rep α R)) (rep α R) where
  impl := fun pq => add pq.1 pq.2
  spec := fun fg => fg.1 + fg.2
  commutes := fun pq => denote_append pq.1 pq.2

def mulSquare : Squares.Square (Squares.product (rep α R) (rep α R)) (rep α R) where
  impl := fun pq => mul pq.1 pq.2
  spec := fun fg => fg.1 * fg.2
  commutes := fun pq => denote_mul pq.1 pq.2

def normalizeSquare : Squares.Square (rep α R) (rep α R) where
  impl := normalize
  spec := id
  commutes := denote_normalize

/-- Horizontal pasting proves an optimized multiplication implementation. -/
def normalizedMulSquare : Squares.Square
    (Squares.product (rep α R) (rep α R)) (rep α R) :=
  Squares.compose normalizeSquare mulSquare

@[reducible] def languageRep (α : Type u) [DecidableEq α] : Squares.Rep.{u} :=
  (rep α ℕ).after support

/-- Vertical pasting forgets weights while retaining the multiplication proof. -/
def languageMulSquare : Squares.Square
    (Squares.product (languageRep α) (languageRep α)) (languageRep α) :=
  Squares.vertical (A := Squares.product (rep α ℕ) (rep α ℕ)) (B := rep α ℕ)
    (AS := Language α × Language α) (BS := Language α)
    (fun fg : Series α ℕ × Series α ℕ => (support fg.1, support fg.2)) support
    (mulSquare (α := α) (R := ℕ)) (supportMulSquare α) (fun _ => rfl)

def sampleP : Polynomial Char ℕ := [("ab".toList, 2), ("a".toList, 1)]
def sampleQ : Polynomial Char ℕ := [("c".toList, 3), ("bc".toList, 4)]

/-- There are two distinct splits/term pairs contributing to the coefficient. -/
example : denote (mul sampleP sampleQ) "abc".toList = 10 := by decide

end Polynomial
end Convolution

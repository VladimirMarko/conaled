import Squares
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Computability.Language
import Mathlib.Algebra.Ring.Nat

/-!
# Weighted languages and finite convolution

The semantic objects are functions on words. Multiplication enumerates every
split of the input word, once, and needs only a semiring of coefficients. In
particular neither infinitely supported sums nor commutative multiplication
are assumed. The semiring laws below are proved from the executable recursion.

Source: Elliott, *Generalized Convolution and Efficient Language Recognition*
(2019), sections "Monoid semirings", "Splittings", and "Decomposing Functions
from Lists"; manuscript commit 4a466d2344daf78d1edb515d4d6fe23d7bba3e67.
-/

namespace Convolution

universe u v z
variable {α : Type u} {R : Type v} {T : Type z}

/-- A weighted, possibly infinitely supported, language. -/
@[ext] structure Series (α : Type u) (R : Type v) where
  coeff : List α → R

instance : CoeFun (Series α R) (fun _ => List α → R) := ⟨Series.coeff⟩

theorem Series.ext_coeff {f g : Series α R} (h : ∀ w, f w = g w) : f = g :=
  Series.ext (funext h)

/-- Every prefix/suffix split, including the two boundary splits. -/
def splits : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: w => ([], a :: w) :: (splits w).map (fun uv => (a :: uv.1, uv.2))

theorem mem_splits (u v w : List α) : (u, v) ∈ splits w ↔ u ++ v = w := by
  induction w generalizing u v with
  | nil => simp [splits, List.append_eq_nil_iff, Prod.ext_iff]
  | cons a w ih =>
    cases u with
    | nil => simp [splits]
    | cons b u => simp [splits, ih, Prod.ext_iff, and_assoc, and_left_comm, eq_comm]

theorem length_splits (w : List α) : (splits w).length = w.length + 1 := by
  induction w <;> simp [splits, *]

section Semiring
variable [Semiring R]

/-- Structural finite convolution; each recursive step consumes a character. -/
def convolution (f g : List α → R) : List α → R
  | [] => f [] * g []
  | a :: w => f [] * g (a :: w) + convolution (fun v => f (a :: v)) g w

theorem convolution_splits (f g : List α → R) (w : List α) :
    convolution f g w = ((splits w).map (fun uv => f uv.1 * g uv.2)).sum := by
  induction w generalizing f with
  | nil => simp [convolution, splits]
  | cons a w ih => simp [convolution, splits, ih, List.map_map, Function.comp_def]

private theorem conv_zero_left (g : List α → R) (w : List α) :
    convolution (fun _ => 0) g w = 0 := by
  induction w <;> simp [convolution, *]

private theorem conv_zero_right (f : List α → R) (w : List α) :
    convolution f (fun _ => 0) w = 0 := by
  induction w generalizing f <;> simp [convolution, *]

theorem conv_add_left (f g h : List α → R) (w : List α) :
    convolution (fun v => f v + g v) h w = convolution f h w + convolution g h w := by
  induction w generalizing f g with
  | nil => simp [convolution, add_mul]
  | cons a w ih => simp only [convolution, add_mul, ih]; ac_rfl

theorem conv_add_right (f g h : List α → R) (w : List α) :
    convolution f (fun v => g v + h v) w = convolution f g w + convolution f h w := by
  induction w generalizing f with
  | nil => simp [convolution, mul_add]
  | cons a w ih => simp only [convolution, mul_add, ih]; ac_rfl

theorem conv_scale_left (r : R) (f g : List α → R) (w : List α) :
    convolution (fun v => r * f v) g w = r * convolution f g w := by
  induction w generalizing f <;> simp [convolution, mul_add, mul_assoc, *]

theorem conv_assoc (f g h : List α → R) (w : List α) :
    convolution (convolution f g) h w = convolution f (convolution g h) w := by
  induction w generalizing f g h with
  | nil => simp [convolution, mul_assoc]
  | cons a w ih =>
    change (f [] * g []) * h (a :: w) +
      convolution (fun v => f [] * g (a :: v) +
        convolution (fun u => f (a :: u)) g v) h w =
      f [] * (g [] * h (a :: w) + convolution (fun v => g (a :: v)) h w) +
        convolution (fun v => f (a :: v)) (convolution g h) w
    rw [conv_add_left, conv_scale_left, ih]
    simp only [mul_add, mul_assoc, add_assoc]

def epsilonFn : List α → R
  | [] => 1
  | _ :: _ => 0

private theorem conv_one_left (g : List α → R) (w : List α) :
    convolution epsilonFn g w = g w := by
  cases w <;> simp [convolution, epsilonFn, conv_zero_left]

private theorem conv_one_right (f : List α → R) (w : List α) :
    convolution f epsilonFn w = f w := by
  induction w generalizing f <;> simp [convolution, epsilonFn, *]

instance : Zero (Series α R) := ⟨⟨fun _ => 0⟩⟩
instance : One (Series α R) := ⟨⟨epsilonFn⟩⟩
instance : Add (Series α R) := ⟨fun f g => ⟨fun w => f w + g w⟩⟩
instance : Mul (Series α R) := ⟨fun f g => ⟨convolution f.coeff g.coeff⟩⟩

@[simp] theorem zero_apply (w : List α) : (0 : Series α R) w = 0 := rfl
@[simp] theorem one_nil : (1 : Series α R) [] = 1 := rfl
@[simp] theorem one_cons (a : α) (w : List α) : (1 : Series α R) (a :: w) = 0 := rfl
@[simp] theorem add_apply (f g : Series α R) (w : List α) : (f + g) w = f w + g w := rfl
@[simp] theorem mul_nil (f g : Series α R) : (f * g) [] = f [] * g [] := rfl
@[simp] theorem mul_cons (f g : Series α R) (a : α) (w : List α) :
    (f * g) (a :: w) = f [] * g (a :: w) + convolution (fun v => f (a :: v)) g.coeff w := rfl

instance : Semiring (Series α R) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc f g h := Series.ext_coeff (fun _ => add_assoc _ _ _)
  zero_add f := Series.ext_coeff (fun _ => zero_add _)
  add_zero f := Series.ext_coeff (fun _ => add_zero _)
  add_comm f g := Series.ext_coeff (fun _ => add_comm _ _)
  mul_assoc f g h := Series.ext_coeff (conv_assoc _ _ _)
  zero_mul g := Series.ext_coeff (conv_zero_left _)
  mul_zero f := Series.ext_coeff (conv_zero_right _)
  one_mul f := Series.ext_coeff (conv_one_left _)
  mul_one f := Series.ext_coeff (conv_one_right _)
  left_distrib f g h := Series.ext_coeff (conv_add_right _ _ _)
  right_distrib f g h := Series.ext_coeff (conv_add_left _ _ _)
  natCast n := ⟨fun w => match w with | [] => n | _ :: _ => 0⟩
  natCast_zero := Series.ext_coeff (by intro w; cases w <;> simp)
  natCast_succ n := Series.ext_coeff (by intro w; cases w <;> simp [Nat.cast_add, Nat.cast_one])
  nsmul := nsmulRec

/-- The left scalar action required by the derivative product rule. -/
def scale (r : R) (f : Series α R) : Series α R := ⟨fun w => r * f w⟩

def derivative (a : α) (f : Series α R) : Series α R := ⟨fun w => f (a :: w)⟩

def derivativeWord (u : List α) (f : Series α R) : Series α R := ⟨fun v => f (u ++ v)⟩

theorem derivative_mul (a : α) (f g : Series α R) :
    derivative a (f * g) = scale (f []) (derivative a g) + derivative a f * g := rfl

theorem derivative_add (a : α) (f g : Series α R) :
    derivative a (f + g) = derivative a f + derivative a g := rfl

omit [Semiring R] in
theorem derivativeWord_append (u v : List α) (f : Series α R) :
    derivativeWord (u ++ v) f = derivativeWord v (derivativeWord u f) := by
  apply Series.ext_coeff; intro w; simp [derivativeWord, List.append_assoc]

omit [Semiring R] in
theorem nullable_derivativeWord (w : List α) (f : Series α R) :
    derivativeWord w f [] = f w := by simp [derivativeWord]

variable [Semiring T]

theorem map_convolution (h : R →+* T) (f g : List α → R) (w : List α) :
    h (convolution f g w) = convolution (fun v => h (f v)) (fun v => h (g v)) w := by
  induction w generalizing f <;> simp [convolution, *]

/-- Changing the coefficient semiring preserves convolution, not just pointwise addition. -/
def mapCoefficients (h : R →+* T) : Series α R →+* Series α T where
  toFun f := ⟨fun w => h (f w)⟩
  map_zero' := Series.ext_coeff (fun _ => h.map_zero)
  map_one' := Series.ext_coeff (by intro w; cases w <;> simp [epsilonFn])
  map_add' f g := Series.ext_coeff (fun _ => h.map_add _ _)
  map_mul' f g := Series.ext_coeff (map_convolution h _ _)

end Semiring

/-- Positivity gives the correct forgetful map from parse counts to membership. -/
def support (f : Series α ℕ) : Language α := {w | f w ≠ 0}

theorem support_mul (f g : Series α ℕ) : support (f * g) = support f * support g := by
  apply Language.ext
  intro w
  change convolution f.coeff g.coeff w ≠ 0 ↔ _
  rw [Language.mem_mul]
  induction w generalizing f with
  | nil =>
    simp only [convolution, ne_eq, mul_eq_zero, not_or]
    constructor
    · rintro ⟨hf, hg⟩; exact ⟨[], hf, [], hg, rfl⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv
      exact ⟨hu, hv⟩
  | cons a w ih =>
    simp only [convolution, ne_eq, Nat.add_eq_zero_iff, not_and_or, mul_eq_zero, not_or]
    change ((f [] ≠ 0 ∧ g (a :: w) ≠ 0) ∨
      convolution (derivative a f).coeff g.coeff w ≠ 0) ↔ _
    rw [ih (derivative a f)]
    constructor
    · rintro (⟨hf, hg⟩ | ⟨u, hu, v, hv, huv⟩)
      · exact ⟨[], hf, a :: w, hg, rfl⟩
      · exact ⟨a :: u, hu, v, hv, by simp [huv]⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      cases u with
      | nil => left; exact ⟨hu, by simpa using (huv ▸ hv)⟩
      | cons b u =>
        have hab : b = a ∧ u ++ v = w := List.cons.inj huv
        rcases hab with ⟨rfl, hrest⟩
        right; exact ⟨u, hu, v, hv, hrest⟩

def supportHom : Series α ℕ →+* Language α where
  toFun := support
  map_zero' := by
    apply Language.ext; intro w
    change (0 : ℕ) ≠ 0 ↔ False
    simp
  map_one' := by
    apply Language.ext; intro w
    change (1 : Series α ℕ) w ≠ 0 ↔ w = []
    cases w <;> simp
  map_add' f g := by
    apply Language.ext; intro w
    change f w + g w ≠ 0 ↔ f w ≠ 0 ∨ g w ≠ 0
    omega
  map_mul' := support_mul

theorem support_derivative (a : α) (f : Series α ℕ) :
    support (derivative a f) = {w | a :: w ∈ support f} := rfl

/-- Coefficient forgetting is a representation; multiplication is a square. -/
@[reducible] def countsRep (α : Type u) : Squares.Rep.{u} where
  R := Series α ℕ
  S := Language α
  decode := support

def supportMulSquare (α : Type u) :
    Squares.Square (Squares.product (countsRep α) (countsRep α)) (countsRep α) where
  impl := fun fg => fg.1 * fg.2
  spec := fun fg => fg.1 * fg.2
  commutes := fun fg => support_mul fg.1 fg.2

end Convolution

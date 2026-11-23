import Applications.Convolution.Series
import Applications.Languages.Coalgebra
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Proper weighted word closure. Each coefficient is a finite sum of powers.
Properness constrains the operand, not the closure result or coefficient algebra. -/
namespace Convolution
open scoped BigOperators Computability
variable {α R T : Type*} [Semiring R]

/-- A proper series cannot consume an empty word with nonzero weight. -/
def Proper (f : Series α R) : Prop := f [] = 0

@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Series α R) (w : List α) :
    (∑ i ∈ s, f i) w = ∑ i ∈ s, f i w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- A proper factor consumes a character, so too many factors give coefficient zero. -/
theorem pow_apply_eq_zero (f : Series α R) (hf : Proper f) (n : ℕ) (w : List α)
    (h : w.length < n) : (f^n) w = 0 := by
  induction n generalizing w with
  | zero => omega
  | succ n ih =>
    rw [pow_succ']
    change convolution f.coeff (f^n).coeff w = 0
    rw [convolution_splits]
    apply List.sum_eq_zero
    intro r hr
    obtain ⟨⟨u,v⟩, huv, rfl⟩ := List.mem_map.mp hr
    have hw := (mem_splits u v w).mp huv
    by_cases hu : u = []
    · subst u; simp [show f [] = 0 from hf]
    · have hl := congrArg List.length hw
      simp only [List.length_append] at hl
      have hp : 0 < u.length := List.length_pos_iff.mpr hu
      rw [ih v (by omega), mul_zero]

/-- This finite expression is defined for every series; its closure laws require properness. -/
def properStar (f : Series α R) : Series α R :=
  ⟨fun w => ∑ n ∈ Finset.range (w.length+1), (f^n) w⟩

/-- Uniform truncations agree on every word shorter than the truncation bound. -/
theorem properStar_eq_sum (f : Series α R) (hf : Proper f) (w : List α) (n : ℕ)
    (hn : w.length < n) : properStar f w = (∑ i ∈ Finset.range n, f^i) w := by
  rw [sum_apply]
  change (∑ i ∈ Finset.range (w.length+1), (f^i) w) = _
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hi hnot
  exact (pow_apply_eq_zero f hf i w (by simp only [Finset.mem_range] at hnot; omega))

/-- Convolution only observes subwords of its output. -/
theorem convolution_congr (f f' g g' : Series α R) (w : List α)
    (h : ∀ u v, u ++ v = w → f u * g v = f' u * g' v) : (f*g) w = (f'*g') w := by
  change convolution _ _ w = convolution _ _ w
  rw [convolution_splits, convolution_splits]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact h p.1 p.2 ((mem_splits _ _ _).mp hp)

private theorem sum_powers_left (f : Series α R) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), f^i) = 1 + f * ∑ i ∈ Finset.range n, f^i := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ', Finset.mul_sum, add_comm]
private theorem sum_powers_right (f : Series α R) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), f^i) = 1 + (∑ i ∈ Finset.range n, f^i) * f := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ, Finset.sum_mul, add_comm]

theorem properStar_unfold_left (f : Series α R) (hf : Proper f) :
    properStar f = 1 + f * properStar f := by
  apply Series.ext_coeff; intro w
  rw [properStar_eq_sum f hf w (w.length+2) (by omega), sum_powers_left]
  simp only [add_apply]
  congr 1
  apply convolution_congr
  intro u v huv
  have hl := congrArg List.length huv
  simp only [List.length_append] at hl
  rw [← properStar_eq_sum f hf v (w.length+1) (by omega)]

theorem properStar_unfold_right (f : Series α R) (hf : Proper f) :
    properStar f = 1 + properStar f * f := by
  apply Series.ext_coeff; intro w
  rw [properStar_eq_sum f hf w (w.length+2) (by omega), sum_powers_right]
  simp only [add_apply]
  congr 1
  apply convolution_congr
  intro u v huv
  have hl := congrArg List.length huv
  simp only [List.length_append] at hl
  rw [← properStar_eq_sum f hf u (w.length+1) (by omega)]

/-- For a proper left operand, the equation has at most one solution. -/
theorem proper_solution_unique (f r x y : Series α R) (hf : Proper f)
    (hx : x = f*x+r) (hy : y = f*y+r) : x = y := by
  apply Series.ext_coeff
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    have hc : (f*x) w = (f*y) w := by
      apply convolution_congr
      intro u v huv
      by_cases hu : u = []
      · subst u; simp [show f [] = 0 from hf]
      · have hl := congrArg List.length huv
        simp only [List.length_append] at hl
        have hp := List.length_pos_iff.mpr hu
        rw [ih v.length (by omega) v rfl]
    calc
      x w = (f*x) w + r w := congrArg (fun z : Series α R => z w) hx
      _ = (f*y) w + r w := by rw [hc]
      _ = y w := (congrArg (fun z : Series α R => z w) hy).symm

theorem properStar_solution (f r : Series α R) (hf : Proper f) :
    properStar f * r = f * (properStar f * r) + r := by
  conv_lhs => rw [properStar_unfold_left f hf]
  simp [add_mul, mul_assoc, add_comm]

theorem eq_properStar_mul (f r x : Series α R) (hf : Proper f) (hx : x = f*x+r) :
    x = properStar f * r :=
  proper_solution_unique f r x _ hf hx (properStar_solution f r hf)

@[simp] theorem properStar_nil (f : Series α R) : properStar f [] = 1 := by
  simp [properStar]
@[simp] theorem properStar_zero : properStar (0 : Series α R) = 1 := by
  have h := properStar_unfold_left (0 : Series α R) rfl
  simpa using h

/-- Finite coefficients make ordinary semiring homomorphisms sufficient. -/
theorem map_properStar [Semiring T] (φ : R →+* T) (f : Series α R) :
    mapCoefficients φ (properStar f) = properStar (mapCoefficients φ f) := by
  apply Series.ext_coeff; intro w
  change φ (∑ i ∈ Finset.range (w.length+1), (f^i) w) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : Series α T => z w) ((mapCoefficients φ).map_pow f i)


/-- An executable repeated-unfold evaluator, separate from the power-sum specification. -/
def closureApprox (f : Series α R) : ℕ → Series α R
  | 0 => 0
  | n+1 => 1 + f * closureApprox f n

theorem closureApprox_eq_sum (f : Series α R) (n : ℕ) :
    closureApprox f n = ∑ i ∈ Finset.range n, f^i := by
  induction n with
  | zero => simp [closureApprox]
  | succ n ih => rw [closureApprox, ih, sum_powers_left]

def evalProperStar (f : Series α R) (w : List α) : R := closureApprox f (w.length+1) w

theorem evalProperStar_correct (f : Series α R) (w : List α) :
    evalProperStar f w = properStar f w := by
  simp [evalProperStar, closureApprox_eq_sum, properStar]

theorem derivative_properStar (f : Series α R) (hf : Proper f) (a : α) :
    derivative a (properStar f) = derivative a f * properStar f := by
  apply Series.ext_coeff; intro w
  have h := congrArg (fun z : Series α R => z (a::w)) (properStar_unfold_left f hf)
  change properStar f (a::w) = convolution (fun v => f (a::v)) (properStar f).coeff w
  simpa only [add_apply, one_cons, mul_cons, show f [] = 0 from hf, zero_mul, zero_add]
    using h


/-- Empty weight one prevents even a left-unfold star over natural counts. -/
theorem no_nat_nullable_star (f s : Series α ℕ) (hf : f [] = 1) : s ≠ 1 + f*s := by
  intro h
  have he := congrArg (fun z : Series α ℕ => z []) h
  simp only [add_apply, one_nil, mul_nil, hf, one_mul] at he
  omega

/-- Forgetting finite natural-number multiplicities recovers language closure. -/
theorem support_properStar (f : Series α ℕ) (hf : Proper f) :
    support (properStar f) = (support f)∗ := by
  apply Language.ext; intro w
  rw [Language.kstar_eq_iSup_pow, Language.mem_iSup]
  change (∑ i ∈ Finset.range (w.length+1), (f^i) w) ≠ 0 ↔ ∃ n, w ∈ support f ^ n
  have hp (n : ℕ) : w ∈ support f ^ n ↔ (f^n) w ≠ 0 := by
    change w ∈ (supportHom f)^n ↔ _
    rw [← map_pow]
    rfl
  simp_rw [hp]
  simp only [ne_eq, Finset.sum_eq_zero_iff, not_forall]
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, h.2⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hl : n < w.length+1 := by
      by_contra h
      exact hn (pow_apply_eq_zero f hf n w (by omega))
    exact ⟨Finset.mem_range.mpr hl, hn⟩

namespace ClosureMachine
open SquareKit.WordCoalgebra
open LanguageCoalgebra.Weighted

/-- Series themselves supply leaf behaviors for the existing compositional machine. -/
def leaves : Coalgebra α R (Series α R) := fun f => (f [], fun a => derivative a f)

omit [Semiring R] in
theorem leaves_morphism : Morphism (leaves (α := α) (R := R)) final Series.coeff :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- After one consumed letter, closure is interpreted by the existing concatenation machine. -/
def nextTerm (f : Series α R) (a : α) : Term R (Series α R) :=
  .concat (.leaf (derivative a f)) (.leaf (properStar f))

theorem run_nextTerm (f : Series α R) (hf : Proper f) (a : α) (w : List α) :
    run (coalgebra leaves) (nextTerm f a) w = properStar f (a::w) := by
  rw [run_correct leaves_morphism]
  change (derivative a f * properStar f) w = properStar f (a::w)
  rw [← derivative_properStar f hf a]
  rfl

end ClosureMachine
end Convolution

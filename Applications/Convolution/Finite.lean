import Applications.Convolution.Series
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Fintype.Prod

/-! Finite-decomposition convolution. Enumeration belongs to the index monoid;
no closure operation or infinite summation is required. -/
namespace Convolution
namespace Finite
open scoped BigOperators
open Finset
variable {M R S : Type*} [Monoid M] [HasMulAntidiagonal M] [Semiring R]

/-- A finite carrier supplies an executable enumeration; select this explicitly
rather than competing with specialized antidiagonal instances. -/
abbrev finiteAntidiagonal (M : Type*) [Monoid M] [Fintype M] [DecidableEq M] :
    HasMulAntidiagonal M where
  mulAntidiagonal x := Finset.univ.filter fun p : M × M => p.1 * p.2 = x
  mem_mulAntidiagonal := by simp

/-- All-function convolution using the supplied finite multiplication fibers. -/
def convolution (f g : M → R) (x : M) : R :=
  ∑ p ∈ mulAntidiagonal x, f p.1 * g p.2

/-- Reassociation preserves each factorization, including its multiplicity. -/
theorem convolution_assoc (f g h : M → R) (x : M) :
    convolution (convolution f g) h x = convolution f (convolution g h) x := by
  classical
  simp only [convolution, sum_mul, mul_sum, sum_sigma']
  apply sum_bij (fun p _ => ⟨(p.2.1, p.2.2 * p.1.2), (p.2.2, p.1.2)⟩)
  · rintro ⟨⟨ab,c⟩,⟨a,b⟩⟩ hp
    simp only [mem_sigma, mem_mulAntidiagonal] at hp ⊢
    exact ⟨by rw [← mul_assoc, hp.2, hp.1], trivial⟩
  · rintro ⟨⟨ab,c⟩,⟨a,b⟩⟩ hp ⟨⟨ab',c'⟩,⟨a',b'⟩⟩ hq he
    simp only [mem_sigma, mem_mulAntidiagonal] at hp hq
    have he' : a = a' ∧ b = b' ∧ c = c' := by
      simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, and_assoc] at he
      exact ⟨he.1, he.2.2⟩
    rcases he' with ⟨rfl,rfl,rfl⟩
    have : ab = ab' := hp.2.symm.trans hq.2
    subst ab'; rfl
  · rintro ⟨⟨a,bc⟩,⟨b,c⟩⟩ hp
    simp only [mem_sigma, mem_mulAntidiagonal] at hp
    refine ⟨⟨(a*b,c),(a,b)⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_mulAntidiagonal]
      exact ⟨by rw [mul_assoc, hp.2, hp.1], trivial⟩
    · simp only [hp.2]
  · intro p hp; exact mul_assoc _ _ _

@[simp] theorem zero_left (f : M → R) (x : M) : convolution (fun _ => 0) f x = 0 := by
  simp [convolution]
@[simp] theorem zero_right (f : M → R) (x : M) : convolution f (fun _ => 0) x = 0 := by
  simp [convolution]
theorem add_left (f g h : M → R) (x : M) :
    convolution (fun y => f y + g y) h x = convolution f h x + convolution g h x := by
  simp [convolution, add_mul, sum_add_distrib]
theorem add_right (f g h : M → R) (x : M) :
    convolution f (fun y => g y + h y) x = convolution f g x + convolution f h x := by
  simp [convolution, mul_add, sum_add_distrib]

variable [DecidableEq M]
def unit : M → R := fun x => if x = 1 then 1 else 0

@[simp] theorem unit_left (f : M → R) (x : M) : convolution unit f x = f x := by
  classical
  unfold convolution
  rw [sum_eq_single (1,x)]
  · simp [unit]
  · rintro ⟨a,b⟩ hp hn
    have hab := mem_mulAntidiagonal.mp hp
    by_cases ha : a = 1
    · subst a; simp only [one_mul] at hab; subst b; exact (hn rfl).elim
    · simp [unit, ha]
  · simp
@[simp] theorem unit_right (f : M → R) (x : M) : convolution f unit x = f x := by
  classical
  unfold convolution
  rw [sum_eq_single (x,1)]
  · simp [unit]
  · rintro ⟨a,b⟩ hp hn
    have hab := mem_mulAntidiagonal.mp hp
    by_cases hb : b = 1
    · subst b; simp only [mul_one] at hab; subst a; exact (hn rfl).elim
    · simp [unit, hb]
  · simp

omit [DecidableEq M] in
theorem map_convolution [Semiring S] (φ : R →+* S) (f g : M → R) (x : M) :
    φ (convolution f g x) = convolution (fun y => φ (f y)) (fun y => φ (g y)) x := by
  simp [convolution]

omit [DecidableEq M] in
/-- Finite support embeds compatibly whenever all output fibers are finite. -/
theorem monoidAlgebra_mul (f g : MonoidAlgebra R M) (x : M) :
    (f * g).coeff x = convolution f.coeff g.coeff x :=
  MonoidAlgebra.coeff_mul_antidiag f g x _ (fun {_} => mem_mulAntidiagonal)

/-- This wrapper distinguishes convolution from pointwise multiplication. -/
@[ext] structure Series (M R : Type*) where
  coeff : M → R

instance : CoeFun (Series M R) (fun _ => M → R) := ⟨Series.coeff⟩
instance : Zero (Series M R) := ⟨⟨fun _ => 0⟩⟩
instance : One (Series M R) := ⟨⟨unit⟩⟩
instance : Add (Series M R) := ⟨fun f g => ⟨fun x => f x + g x⟩⟩
instance : Mul (Series M R) := ⟨fun f g => ⟨convolution f.coeff g.coeff⟩⟩

instance : Semiring (Series M R) where
  add_assoc f g h := Series.ext (funext fun _ => add_assoc _ _ _)
  zero_add f := Series.ext (funext fun _ => zero_add _)
  add_zero f := Series.ext (funext fun _ => add_zero _)
  add_comm f g := Series.ext (funext fun _ => add_comm _ _)
  mul_assoc f g h := Series.ext (funext (convolution_assoc _ _ _))
  zero_mul f := Series.ext (funext (zero_left _))
  mul_zero f := Series.ext (funext (zero_right _))
  one_mul f := Series.ext (funext (unit_left _))
  mul_one f := Series.ext (funext (unit_right _))
  left_distrib f g h := Series.ext (funext (add_right _ _ _))
  right_distrib f g h := Series.ext (funext (add_left _ _ _))
  natCast n := ⟨fun x => if x = 1 then n else 0⟩
  natCast_zero := Series.ext (funext (by intro x; change (if x = 1 then ((0 : ℕ) : R) else 0) = 0; simp))
  natCast_succ n := Series.ext (funext (by
    intro x
    change (if x = 1 then ((n+1 : ℕ) : R) else 0) =
      (if x = 1 then (n : R) else 0) + unit x
    by_cases hx : x = 1 <;> simp [unit, hx]))
  nsmul := nsmulRec

def mapCoefficients [Semiring S] (φ : R →+* S) : Series M R →+* Series M S where
  toFun f := ⟨fun x => φ (f x)⟩
  map_zero' := Series.ext (funext fun _ => φ.map_zero)
  map_one' := Series.ext (funext (by intro x; change φ (unit x) = unit x; simp [unit]))
  map_add' f g := Series.ext (funext fun _ => φ.map_add _ _)
  map_mul' f g := Series.ext (funext (map_convolution φ _ _))

end Finite
end Convolution

namespace Convolution

theorem splits_nodup {α : Type*} (w : List α) : (splits w).Nodup := by
  induction w with
  | nil => simp [splits]
  | cons a w ih =>
    simp only [splits, List.nodup_cons]
    constructor
    · simp
    · exact ih.map (by intro x y h; simpa only [Prod.mk.injEq, List.cons.injEq, true_and,
        Prod.ext_iff] using h)

instance freeMonoidDecidableEq {α : Type*} [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  inferInstanceAs (DecidableEq (List α))

/-- The word enumeration is executable when letters have decidable equality. -/
instance wordAntidiagonal {α : Type*} [DecidableEq α] :
    Finset.HasMulAntidiagonal (FreeMonoid α) where
  mulAntidiagonal w := (splits w.toList).toFinset
  mem_mulAntidiagonal := by
    intro w p
    change (p.1.toList, p.2.toList) ∈ (splits w.toList).toFinset ↔
      p.1.toList ++ p.2.toList = w.toList
    rw [List.mem_toFinset, mem_splits]

/-- Recover the structural implementation, rather than replacing its computation. -/
theorem word_convolution {α R : Type*} [DecidableEq α] [Semiring R]
    (f g : Series α R) (w : List α) :
    Finite.convolution (fun u : FreeMonoid α => f u.toList)
      (fun u : FreeMonoid α => g u.toList) (FreeMonoid.ofList w) = (f * g) w := by
  change (splits w).toFinset.sum (fun p => f p.1 * g p.2) = convolution f.coeff g.coeff w
  rw [List.sum_toFinset _ (splits_nodup w), convolution_splits]

/-- The old word API is a semiring specialization, with its computation retained. -/
def wordEquiv {α R : Type*} [DecidableEq α] [Semiring R] :
    Series α R ≃+* Finite.Series (FreeMonoid α) R where
  toFun f := ⟨fun w => f w.toList⟩
  invFun f := ⟨fun w => f (FreeMonoid.ofList w)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' f g := Finite.Series.ext (funext fun w => (word_convolution f g w.toList).symm)

end Convolution

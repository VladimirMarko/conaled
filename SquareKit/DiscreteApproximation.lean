import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Optional finite discrete comparison. Wiring and local gains are supplied by
applications; no feedback solver, domain existence or continuous-flow claim is implicit. -/
namespace SquareKit.DiscreteApproximation

def orbit {S : Type*} (f : S → S) (s : S) : ℕ → S
  | 0 => s
  | n+1 => f (orbit f s n)

theorem orbit_add {S : Type*} (f : S → S) (s : S) (n m : ℕ) :
    orbit f s (n+m) = orbit f (orbit f s n) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [orbit, ih]

theorem orbit_mem {S : Type*} {f : S → S} {D : Set S}
    (closed : ∀ s ∈ D, f s ∈ D) {s : S} (hs : s ∈ D) (n : ℕ) : orbit f s n ∈ D := by
  induction n with
  | zero => exact hs
  | succ n ih => exact closed _ ih

def budget (gain defect initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n+1 => gain * budget gain defect initial n + defect

theorem geometric_step (a : ℝ) (n : ℕ) :
    a * ∑ j ∈ Finset.range n, a^j + 1 = (∑ j ∈ Finset.range n, a^j) + a^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith

theorem budget_sum (a d e : ℝ) (n : ℕ) :
    budget a d e n = a^n*e + d*∑ j ∈ Finset.range n, a^j := by
  induction n with
  | zero => simp [budget]
  | succ n ih =>
    rw [budget, ih, pow_succ, Finset.sum_range_succ]
    have hs := congrArg (d * ·) (geometric_step a n)
    linear_combination hs

theorem budget_add (a d e : ℝ) (n m : ℕ) :
    budget a d e (n+m) = budget a d (budget a d e n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change a * budget a d e (n+m) + d = a * budget a d (budget a d e n) m + d
    rw [ih]

/-- The intermediate comparison is the interpreted source successor, not an
arbitrary matching state. The target gain must apply to that actual witness. -/
theorem step_bound {S T : Type*} [PseudoMetricSpace T]
    (f : S → S) (g : T → T) (interpret : S → T) {a d : ℝ} {s : S} {t : T}
    (defectBound : dist (interpret (f s)) (g (interpret s)) ≤ d)
    (gain : dist (g (interpret s)) (g t) ≤ a * dist (interpret s) t) :
    dist (interpret (f s)) (g t) ≤ a * dist (interpret s) t + d := by
  calc
    _ ≤ dist (interpret (f s)) (g (interpret s)) + dist (g (interpret s)) (g t) :=
      dist_triangle _ _ _
    _ ≤ _ := by linarith

/-- Domain obligations are indexed by each step of the finite horizon. -/
theorem finite_bound {S T : Type*} [PseudoMetricSpace T]
    (f : S → S) (g : T → T) (interpret : S → T) (s : S) (t : T)
    {a d e : ℝ} (ha : 0 ≤ a) (initial : dist (interpret s) t ≤ e) (N : ℕ)
    (defectBound : ∀ n < N, dist (interpret (f (orbit f s n)))
      (g (interpret (orbit f s n))) ≤ d)
    (gain : ∀ n < N, dist (g (interpret (orbit f s n))) (g (orbit g t n)) ≤
      a * dist (interpret (orbit f s n)) (orbit g t n)) :
    ∀ n ≤ N, dist (interpret (orbit f s n)) (orbit g t n) ≤ budget a d e n := by
  intro n hn
  induction n with
  | zero => exact initial
  | succ n ih =>
    have hn' : n < N := by omega
    exact (step_bound f g interpret (defectBound n hn') (gain n hn')).trans
      (by simpa [budget] using add_le_add_right (mul_le_mul_of_nonneg_left
        (ih (by omega)) ha) d)
end SquareKit.DiscreteApproximation

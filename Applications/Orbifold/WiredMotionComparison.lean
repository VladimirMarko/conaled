import Applications.Orbifold.WiredMotion

/-! Finite comparison of two real Euler evolutions of the wired move field.
The domain invariant is supplied separately and checked for the admitted fixture. -/
noncomputable section
namespace Orbifold.DiskTransport.Numerical.Wired
open SquareKit.DiscreteApproximation

/-- Covers the intermediate half step as well as both sampled evolutions. -/
def Safe (h : ℝ) (s t : ℂ × ℂ) (N : ℕ) : Prop :=
  (∀ n ≤ N, Domain (orbit (halfTwice h) s n)) ∧
  (∀ n ≤ N, Domain (orbit (euler h) t n)) ∧
  (∀ n < N, Domain (euler (h/2) (orbit (halfTwice h) s n)))

theorem comparison {h e : ℝ} (hh : 0 ≤ h) {s t : ℂ × ℂ} {N : ℕ}
    (safe : Safe h s t N) (he : dist s t ≤ e) :
    ∀ n ≤ N, dist (orbit (halfTwice h) s n) (orbit (euler h) t n) ≤
      SquareKit.DiscreteApproximation.budget (1+12*h) (6*h^2) e n := by
  apply finite_bound (halfTwice h) (euler h) id s t (by positivity) he N
  · intro n hn
    exact refinement_defect hh (safe.1 n (by omega)) (safe.2.2 n hn)
  · intro n hn
    exact euler_gain hh (safe.1 n (by omega)) (safe.2.1 n (by omega))

/-- Same contract proved directly, to expose exactly what the adapter reuses. -/
theorem comparison_native {h e : ℝ} (hh : 0 ≤ h) {s t : ℂ × ℂ} {N : ℕ}
    (safe : Safe h s t N) (he : dist s t ≤ e) :
    ∀ n ≤ N, dist (orbit (halfTwice h) s n) (orbit (euler h) t n) ≤
      SquareKit.DiscreteApproximation.budget (1+12*h) (6*h^2) e n := by
  intro n hn
  induction n with
  | zero => exact he
  | succ n ih =>
    have hd := refinement_defect hh (safe.1 n (by omega)) (safe.2.2 n (by omega))
    have hg := euler_gain hh (safe.1 n (by omega)) (safe.2.1 n (by omega))
    have ht := dist_triangle (halfTwice h (orbit (halfTwice h) s n))
      (euler h (orbit (halfTwice h) s n)) (euler h (orbit (euler h) t n))
    have hi := ih (by omega)
    have ha : 0 ≤ 1+12*h := by positivity
    change dist (halfTwice h (orbit (halfTwice h) s n))
      (euler h (orbit (euler h) t n)) ≤ _
    rw [SquareKit.DiscreteApproximation.budget]
    nlinarith [mul_le_mul_of_nonneg_left hi ha]

/-- Rational Euler interpretation also commutes with arbitrary finite repetition. -/
theorem orbit_step (h : ℚ) (q : State) (n : ℕ) :
    (orbit (step (.move (1,0)) h) q n).decode = orbit (euler h) q.decode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit, step_eq, ih]

theorem halfTwice_eq (h : ℚ) (q : State) :
    (step (.move (1,0)) (h/2) (step (.move (1,0)) (h/2) q)).decode =
      halfTwice h q.decode := by
  simp only [step_eq, halfTwice]
  norm_cast

end Orbifold.DiskTransport.Numerical.Wired

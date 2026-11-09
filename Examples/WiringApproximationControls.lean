import Examples.WiringApproximation

/-! Failure controls for #416: coordinate equality, stability, and behavior
recovery are distinct claims. These are discrete systems, not ODE solutions. -/
noncomputable section
namespace Examples.WiringApproximation.Controls
open Applications.OpenSystems Examples.OpenSystemWiring
open SquareKit.DiscreteApproximation

def amplifiedA (k : ℝ) : System ℝ Two One where
  field x i := -x+i 0+k*i 1
  readout x _ := x

def amplified (k : ℝ) := ((amplifiedA k).parallel BC).wire close.toRouting

def unstableStep (s : State) : State := (euler (1/4) (amplified 24)).field s (fun _ => 0)

theorem unstable_eq (s : State) : unstableStep s =
    ((3/4)*s.1+6*s.2.2, (1/2)*s.2.1+(1/4)*s.1, (1/4)*s.2.2+(1/4)*s.2.1) := by
  change (s.1+(1/4)*(-s.1+0+24*s.2.2),
    s.2.1+(1/4)*(-2*s.2.1+s.1), s.2.2+(1/4)*(-3*s.2.2+s.2.1)) = _
  ext <;> ring

/-- All three isolated components contract with zero external inputs, including
A with the amplified feedback port held at zero. -/
theorem isolated_contract (x y z : ℝ) :
    |(euler (1/4) (amplifiedA 24)).field x (fun _ => 0)| = (3/4)*|x| ∧
    |(euler (1/4) B).field y (fun _ => 0)| = (1/2)*|y| ∧
    |(euler (1/4) C).field z (fun _ => 0)| = (1/4)*|z| := by
  change |x+(1/4)*(-x+0+24*0)| = _ ∧ |y+(1/4)*(-2*y+0)| = _ ∧
    |z+(1/4)*(-3*z+0)| = _
  have hx : x+(1/4)*(-x+0+24*0) = (3/4)*x := by ring
  have hy : y+(1/4)*(-2*y+0) = (1/2)*y := by ring
  have hz : z+(1/4)*(-3*z+0) = (1/4)*z := by ring
  rw [hx,hy,hz]
  norm_num [abs_mul]

theorem expanding_direction (a : ℝ) :
    unstableStep (12*a,4*a,a) = (12*((5/4)*a),4*((5/4)*a),(5/4)*a) := by
  rw [unstable_eq]
  ext <;> ring

theorem unstable_orbit (n : ℕ) :
    orbit unstableStep (12,4,1) n = (12*(5/4)^n,4*(5/4)^n,(5/4)^n) := by
  induction n with
  | zero => norm_num [orbit]
  | succ n ih => rw [orbit, ih, expanding_direction, pow_succ]; simp only [mul_comm (5/4:ℝ)]

theorem growth_lower (n : ℕ) : (1:ℝ)+n/4 ≤ (5/4:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exposed output has no uniform bound, despite the isolated contractions. -/
theorem output_unbounded (b : ℝ) : ∃ n, b < (amplified 24).readout (orbit unstableStep (12,4,1) n) 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4*b)
  refine ⟨n, ?_⟩
  rw [unstable_orbit]
  change b < (5/4:ℝ)^n
  have := growth_lower n
  linarith

/-- Discrete incrementing component; its interface reveals the changing state. -/
def counter : System ℝ (Fin 0) One := ⟨fun x _ => x+1, fun x _ => x⟩
def sink : System Unit One (Fin 0) := ⟨fun _ _ => (), fun _ i => Fin.elim0 i⟩

/-- A certified wire consumes the counter output at the sink. No supplier is
copied or discarded by the wiring itself; the sink's dynamics ignore its input. -/
def hide : Wiring ((Fin 0) ⊕ One) (One ⊕ (Fin 0)) (Fin 0) (Fin 0) where
  input := Sum.elim Fin.elim0 (fun _ => .inl (.inl 0))
  output := Fin.elim0
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

def hidden := (counter.parallel sink).wire hide.toRouting

def hiddenTrace (n : ℕ) : ℝ × Unit := (n, ())

theorem hidden_trajectory (n : ℕ) :
    hidden.field (hiddenTrace n) (fun i => Fin.elim0 i) = hiddenTrace (n+1) := by
  ext; simp [hidden, hiddenTrace, System.wire, System.parallel, counter, sink]

/-- A fixed external chart witnesses steady-looking composite behavior. -/
theorem hidden_steady_looking : ∃ o : Fin 0 → ℝ,
    ∀ n, hidden.readout (hiddenTrace n) = o := by
  exact ⟨fun i => Fin.elim0 i, fun _ => funext (fun i => Fin.elim0 i)⟩

theorem counter_trajectory (n : ℕ) :
    counter.field (n : ℝ) (fun i => Fin.elim0 i) = ((n+1 : ℕ) : ℝ) := by
  simp [counter]

/-- The component trajectory is not steady-looking. Forward composition of
behaviors therefore cannot promise recovery of this restricted behavior class. -/
theorem counter_not_steady_looking : ¬ ∃ o : One → ℝ, ∀ n : ℕ, counter.readout n = o := by
  rintro ⟨o, h⟩
  have h0 := congrFun (h 0) 0
  have h1 := congrFun (h 1) 0
  norm_num [counter] at h0 h1
  linarith

theorem admission_controls : ¬ fanout.Admissible ∧ (¬ ∃ i : ℝ, i=i+1) ∧
    (¬ ∃ r : Unit → ℝ, ∀ s i, r s=i+1) :=
  ⟨fanout_rejected, feedthrough_feedback_unsolvable, feedthrough_not_state_only⟩

end Examples.WiringApproximation.Controls

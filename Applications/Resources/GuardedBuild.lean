import Applications.Resources.Potential
import Applications.Sequences.RunCompression

/-! Guarded list construction with explicit predicate-test and inserted-cons work.
Every tested cell costs one, including the first failed test. Nil dispatch costs
zero. The value relations are independent of the measured implementations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.GuardedBuild

universe u
variable {α : Type u}

/-- The stopping-test charge is one exactly when a suffix survives. -/
def survivorCharge : List α → Nat
  | [] => 0
  | _ :: _ => 1

/-- Drop the passing prefix, charging every predicate test actually performed. -/
def dropRun (q : α → Bool) : List α → Measured (List α) Nat
  | [] => pure []
  | x :: xs =>
      if q x then
        let r := dropRun q xs
        (r.1, r.2 + 1)
      else (x :: xs, 1)

theorem dropRun_value (q : α → Bool) (xs : List α) :
    (dropRun q xs).1 = xs.dropWhile q := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [dropRun, List.dropWhile_cons]; split <;> simp_all

/-- All removed cells pass; the remainder is empty or starts at the first failure.
No condition is imposed on the untouched tail of a nonempty remainder. -/
def DropSpec (q : α → Bool) (xs rest : List α) : Prop :=
  ∃ pre, xs = pre ++ rest ∧ (∀ x ∈ pre, q x = true) ∧
    (rest = [] ∨ ∃ x tail, rest = x :: tail ∧ q x = false)

theorem dropRun_spec (q : α → Bool) (xs : List α) :
    DropSpec q xs (dropRun q xs).1 := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp, Or.inl rfl⟩
  | cons x xs ih =>
    by_cases hq : q x = true
    · obtain ⟨pre, heq, hall, hstop⟩ := ih
      simp only [dropRun, hq, ↓reduceIte]
      refine ⟨x :: pre, ?_, ?_, hstop⟩
      · exact congrArg (x :: ·) heq
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hq
        · exact hall y hy
    · have hf : q x = false := Bool.eq_false_iff.mpr hq
      simp only [dropRun, hf, Bool.false_eq_true, ↓reduceIte]
      exact ⟨[], rfl, by simp, Or.inr ⟨x, xs, rfl, hf⟩⟩

theorem dropRun_unique (q : α → Bool) (xs rest : List α) (h : DropSpec q xs rest) :
    (dropRun q xs).1 = rest := by
  obtain ⟨pre, rfl, hall, hstop⟩ := h
  rw [dropRun_value, List.dropWhile_append_of_pos hall]
  rcases hstop with rfl | ⟨x, tail, rfl, hx⟩
  · rfl
  · simp [hx]

theorem dropRun_length (q : α → Bool) (xs : List α) :
    (dropRun q xs).1.length ≤ xs.length := by
  obtain ⟨pre, h, _, _⟩ := dropRun_spec q xs
  have hl := congrArg List.length h
  simp only [List.length_append] at hl
  omega

/-- Exact work counts the removed prefix and the first failed test, when present. -/
theorem dropRun_balance (q : α → Bool) (xs : List α) :
    (dropRun q xs).2 + (dropRun q xs).1.length =
      xs.length + survivorCharge (dropRun q xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [dropRun]
    split
    · simp only [List.length_cons]
      omega
    · simp [survivorCharge, Nat.add_comm]

theorem survivorCharge_le (xs : List α) : survivorCharge xs ≤ 1 := by
  cases xs <;> simp [survivorCharge]

/-- Insert after dropping exactly the passing prefix of the old suffix. -/
def insert (p : α → α → Bool) (x : α) (xs : List α) : List α :=
  x :: xs.dropWhile (p x)

/-- Execute the drop, then charge one for the newly inserted cons cell. -/
def insertRun (p : α → α → Bool) (x : α) (xs : List α) : Measured (List α) Nat :=
  Resources.bind (dropRun (p x) xs) (fun rest => (x :: rest, 1))

theorem insertRun_value (p : α → α → Bool) (x : α) (xs : List α) :
    (insertRun p x xs).1 = insert p x xs := by
  simp [insertRun, insert, dropRun_value]

theorem insertRun_spec (p : α → α → Bool) (x : α) (xs : List α) :
    ∃ rest, (insertRun p x xs).1 = x :: rest ∧ DropSpec (p x) xs rest :=
  ⟨_, rfl, dropRun_spec (p x) xs⟩

theorem insertRun_length (p : α → α → Bool) (x : α) (xs : List α) :
    (insertRun p x xs).1.length ≤ xs.length + 1 := by
  have h := dropRun_length (p x) xs
  simpa [insertRun, Resources.bind] using Nat.add_le_add_right h 1

/-- The local potential accounts for both the inserted cell and the stopping test. -/
theorem insertRun_potential_exact (p : α → α → Bool) (x : α) (xs : List α) :
    (insertRun p x xs).2 + (insertRun p x xs).1.length =
      xs.length + 2 + survivorCharge (dropRun (p x) xs).1 := by
  have h := dropRun_balance (p x) xs
  simp only [insertRun, Resources.bind, List.length_cons]
  omega

theorem insertRun_potential (p : α → α → Bool) (x : α) (xs : List α) :
    (insertRun p x xs).2 + (insertRun p x xs).1.length ≤ xs.length + 3 := by
  have h := insertRun_potential_exact p x xs
  have hb := survivorCharge_le (dropRun (p x) xs).1
  omega

/-- The pure guarded right fold. -/
def build (p : α → α → Bool) (xs : List α) : List α := xs.foldr (insert p) []

/-- Execute the suffix first, then insert the current element into that result. -/
def buildRun (p : α → α → Bool) : List α → Measured (List α) Nat
  | [] => Resources.pure []
  | x :: xs => Resources.bind (buildRun p xs) (insertRun p x)

theorem buildRun_value (p : α → α → Bool) (xs : List α) :
    (buildRun p xs).1 = build p xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [buildRun, insertRun_value, ih, build]

/-- Independent value relation: build the tail, then use its first-failure split. -/
inductive BuildSpec (p : α → α → Bool) : List α → List α → Prop
  | nil : BuildSpec p [] []
  | cons {x : α} {xs old rest : List α} :
      BuildSpec p xs old → DropSpec (p x) old rest → BuildSpec p (x :: xs) (x :: rest)

theorem buildRun_spec (p : α → α → Bool) (xs : List α) :
    BuildSpec p xs (buildRun p xs).1 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons ih (dropRun_spec (p x) (buildRun p xs).1)

theorem buildRun_unique (p : α → α → Bool) (xs out : List α) (h : BuildSpec p xs out) :
    (buildRun p xs).1 = out := by
  induction h with
  | nil => rfl
  | @cons x xs old rest _ hdrop ih =>
    simp only [buildRun, Resources.bind_value, insertRun, ih]
    exact congrArg (x :: ·) (dropRun_unique (p x) old rest hdrop)

theorem buildRun_length (p : α → α → Bool) (xs : List α) :
    (buildRun p xs).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [buildRun, Resources.pure]
  | cons x xs ih =>
    have h := insertRun_length p x (buildRun p xs).1
    simp only [buildRun, Resources.bind_value, List.length_cons]
    omega

/-- Reversal describes command order; this executor performs no measured reverse. -/
theorem buildRun_eq_run_reverse (p : α → α → Bool) (xs : List α) :
    buildRun p xs = Resources.run (insertRun p) xs.reverse [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, Resources.run_append, ← ih]
    simp only [buildRun, Resources.run, Resources.bind_pure]

/-- Count nonempty stopped suffixes along the same actual state trajectory.
This is accounting for the execution, not an additional uncharged computation. -/
def survivors (p : α → α → Bool) (xs : List α) : Nat :=
  Resources.budget (insertRun p)
    (fun x ys => survivorCharge (dropRun (p x) ys).1) xs.reverse []

@[simp] theorem survivors_nil (p : α → α → Bool) : survivors p [] = 0 := rfl

theorem survivors_cons (p : α → α → Bool) (x : α) (xs : List α) :
    survivors p (x :: xs) =
      survivors p xs + survivorCharge (dropRun (p x) (buildRun p xs).1).1 := by
  simp only [survivors, List.reverse_cons, Resources.budget_append,
    Resources.budget, Nat.add_zero, ← buildRun_eq_run_reverse]

theorem survivors_le (p : α → α → Bool) (xs : List α) :
    survivors p xs ≤ xs.length := by
  simpa only [survivors, List.length_reverse, Nat.one_mul] using
    Resources.budget_le_constant (insertRun p)
      (fun x ys => survivorCharge (dropRun (p x) ys).1) 1
      (fun x ys => survivorCharge_le (dropRun (p x) ys).1) xs.reverse []

private theorem budget_two_add_survivor_charges
    (p : α → α → Bool) (commands : List α) (ys : List α) :
    Resources.budget (insertRun p)
        (fun x zs => 2 + survivorCharge (dropRun (p x) zs).1) commands ys =
      2 * commands.length + Resources.budget (insertRun p)
        (fun x zs => survivorCharge (dropRun (p x) zs).1) commands ys := by
  induction commands generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    simp only [Resources.budget, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [ih]
    omega

/-- Reuse exact telescoping, specializing the initial list potential to zero. -/
theorem buildRun_potential_exact (p : α → α → Bool) (xs : List α) :
    (buildRun p xs).2 + (buildRun p xs).1.length =
      2 * xs.length + survivors p xs := by
  have h := Resources.run_potential_exact (insertRun p)
    (fun x ys => 2 + survivorCharge (dropRun (p x) ys).1) List.length
    (fun x ys => by
      simpa only [Nat.add_assoc] using insertRun_potential_exact p x ys)
    xs.reverse []
  simpa only [← buildRun_eq_run_reverse, budget_two_add_survivor_charges,
    List.length_nil, List.length_reverse, Nat.zero_add, survivors] using h

/-- The shared constant-charge theorem gives the uniform three-per-insertion bound. -/
theorem buildRun_potential (p : α → α → Bool) (xs : List α) :
    (buildRun p xs).2 + (buildRun p xs).1.length ≤ 3 * xs.length := by
  simpa only [← buildRun_eq_run_reverse, List.length_nil,
    List.length_reverse, Nat.zero_add] using
    Resources.run_constant_charge (insertRun p) List.length 3
      (insertRun_potential p) xs.reverse []

theorem buildRun_work_le (p : α → α → Bool) (xs : List α) :
    (buildRun p xs).2 ≤ 3 * xs.length := by
  have h := buildRun_potential p xs
  omega

/-- Each input element executes one new cons, independently of the returned value. -/
theorem buildRun_work_ge (p : α → α → Bool) (xs : List α) :
    xs.length ≤ (buildRun p xs).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [buildRun, Resources.bind, insertRun, List.length_cons]
    omega

/-- Boolean equality alone identifies the existing pure guarded equality fold. -/
theorem buildRun_equality_value [BEq α] (xs : List α) :
    (buildRun (· == ·) xs).1 = Applications.Sequences.RunCompression.build xs := by
  rw [buildRun_value]
  rfl

/-- A lawful Boolean equality turns an independent adjacent-run certificate into
the measured builder's value, without a DecidableEq premise. -/
theorem buildRun_equality_of_spec [BEq α] [LawfulBEq α]
    {xs out : List α} (h : Applications.Sequences.RunCompression.Spec xs out) :
    (buildRun (· == ·) xs).1 = out := by
  rw [buildRun_equality_value]
  exact (Applications.Sequences.RunCompression.build_equality_iff xs out).mpr h

theorem buildRun_equality_eq_compress [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) :
    (buildRun (· == ·) xs).1 = Applications.Sequences.RunCompression.compress xs := by
  rw [buildRun_equality_value]
  exact Applications.Sequences.RunCompression.build_equality_eq_compress xs

/-- One failed predicate test and one cons invalidate charge two under these units. -/
theorem failed_test_charge_two_counterexample :
    (insertRun (fun (_ _ : Nat) => false) 1 [2]).2 +
      (insertRun (fun (_ _ : Nat) => false) 1 [2]).1.length > [2].length + 2 := by
  calc
    (insertRun (fun (_ _ : Nat) => false) 1 [2]).2 +
        (insertRun (fun (_ _ : Nat) => false) 1 [2]).1.length =
        [2].length + 2 + survivorCharge (dropRun (fun _ : Nat => false) [2]).1 :=
      insertRun_potential_exact _ _ _
    _ > [2].length + 2 := by decide

end Resources.GuardedBuild

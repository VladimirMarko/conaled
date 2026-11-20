import Applications.Resources.Potential
import Applications.Search.Collisions.Basic

/-!
# One measured collision client

The counter carrier and additive observations are independent parameters.
The actual measured read chooses between incrementing and writing true.
Execution reuses `Resources.run`; all representations share this client.
Tariffs are declared modeled observations, not native runtime costs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollisionWork

universe u v w x y z
variable {κ : Type u} {T : Type v} {R : Type w} {C : Type x} {D : Type y} {U : Type z}

/-- Charge entry, read, then exactly one of increment or write, in that order. -/
def step [Add C] (read : κ → T → Measured Bool C)
    (write : κ → Bool → T → Measured T C) (increment : R → Measured R C)
    (tick : C) (key : κ) (state : R × T) : Measured (R × T) C :=
  bind ((), tick) fun _ =>
    bind (read key state.2) fun seen =>
      if seen then
        let next := increment state.1
        ((next.1, state.2), next.2)
      else
        let next := write key true state.2
        ((state.1, next.1), next.2)

/-- The shared executor, followed by one terminal observation, even on empty input. -/
def run [Zero C] [Add C] (read : κ → T → Measured Bool C)
    (write : κ → Bool → T → Measured T C) (increment : R → Measured R C)
    (tick terminal : C) (xs : List κ) (state : R × T) : Measured (R × T) C :=
  bind (Resources.run (step read write increment tick) xs state) fun final =>
    (final, terminal)

section Laws

variable (read : κ → T → Measured Bool C)
    (write : κ → Bool → T → Measured T C) (increment : R → Measured R C)
    (tick terminal : C)

theorem step_of_true [Add C] (key : κ) (state : R × T)
    (seen : (read key state.2).1 = true) :
    step read write increment tick key state =
      (((increment state.1).1, state.2),
        tick + ((read key state.2).2 + (increment state.1).2)) := by
  simp [step, bind, seen]

theorem step_of_false [Add C] (key : κ) (state : R × T)
    (fresh : (read key state.2).1 = false) :
    step read write increment tick key state =
      ((state.1, (write key true state.2).1),
        tick + ((read key state.2).2 + (write key true state.2).2)) := by
  simp [step, bind, fresh]

theorem step_cost_true [Add C] (key : κ) (state : R × T)
    (seen : (read key state.2).1 = true) :
    (step read write increment tick key state).2 =
      tick + ((read key state.2).2 + (increment state.1).2) := by
  rw [step_of_true read write increment tick key state seen]

theorem step_cost_false [Add C] (key : κ) (state : R × T)
    (fresh : (read key state.2).1 = false) :
    (step read write increment tick key state).2 =
      tick + ((read key state.2).2 + (write key true state.2).2) := by
  rw [step_of_false read write increment tick key state fresh]

@[simp] theorem run_nil [AddZeroClass C] (state : R × T) :
    run read write increment tick terminal [] state = (state, terminal) := by
  simp [run, Resources.run, bind, pure]

theorem run_cons [AddMonoid C] (key : κ) (xs : List κ) (state : R × T) :
    run read write increment tick terminal (key :: xs) state =
      bind (step read write increment tick key state)
        (run read write increment tick terminal xs) := by
  simp [run, Resources.run_cons, bind, add_assoc]

theorem run_invariant [Zero C] [Add C] (P : R × T → Prop)
    (closed : ∀ key state, P state → P (step read write increment tick key state).1)
    (xs : List κ) (state : R × T) (valid : P state) :
    P (run read write increment tick terminal xs state).1 := by
  exact Resources.run_invariant (step read write increment tick) P closed xs state valid

/-- Reachability may be closed only for the keys admitted by this workload. -/
theorem run_invariant_on [Zero C] [Add C] (allowed : κ → Prop) (P : R × T → Prop)
    (closed : ∀ key state, allowed key → P state → P (step read write increment tick key state).1)
    (xs : List κ) (inputs : ∀ key ∈ xs, allowed key) (state : R × T) (valid : P state) :
    P (run read write increment tick terminal xs state).1 := by
  change P (Resources.run (step read write increment tick) xs state).1
  induction xs generalizing state with
  | nil => exact valid
  | cons key xs ih =>
      exact ih (fun query inside => inputs query (List.mem_cons_of_mem key inside))
        (step read write increment tick key state).1
        (closed key state (inputs key (List.mem_cons_self)) valid)

/-- The existing decoder/invariant transport applies to the one measured client. -/
theorem run_value_fusion [Zero C] [Add C] (ops : Search.TotalTable.Ops κ Bool U)
    (decode : R × T → Nat × U) (P : R × T → Prop)
    (closed : ∀ key state, P state → P (step read write increment tick key state).1)
    (law : ∀ key state, P state →
      decode (step read write increment tick key state).1 =
        Search.Collisions.step ops (decode state) key)
    (xs : List κ) (state : R × T) (valid : P state) :
    decode (run read write increment tick terminal xs state).1 =
      Search.Collisions.run ops xs (decode state) := by
  exact Resources.run_value_fusion (step read write increment tick)
    (fun key state => Search.Collisions.step ops state key) decode P closed law xs state valid

theorem step_reweight [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (key : κ) (state : R × T) :
    reweight h (step read write increment tick key state) =
      step (fun key table => reweight h (read key table))
        (fun key value table => reweight h (write key value table))
        (fun counter => reweight h (increment counter)) (h tick) key state := by
  cases seen : (read key state.2).1 <;> simp [step, bind, reweight, seen, map_add]

theorem run_reweight [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (xs : List κ) (state : R × T) :
    reweight h (run read write increment tick terminal xs state) =
      run (fun key table => reweight h (read key table))
        (fun key value table => reweight h (write key value table))
        (fun counter => reweight h (increment counter)) (h tick) (h terminal) xs state := by
  simp only [run, reweight_bind, reweight_run, step_reweight]
  rfl

/-- A projection of each actual step is bounded in input order; the terminal
charge is included separately. -/
theorem run_cost_le_sum [AddMonoid C] (h : C →+ Nat) (tariff : κ → Nat)
    (P : R × T → Prop)
    (closed : ∀ key state, P state → P (step read write increment tick key state).1)
    (bound : ∀ key state, P state → h (step read write increment tick key state).2 ≤ tariff key)
    (xs : List κ) (state : R × T) (valid : P state) :
    h (run read write increment tick terminal xs state).2 ≤
      (xs.map tariff).sum + h terminal := by
  induction xs generalizing state with
  | nil => simp
  | cons key xs ih =>
      rw [run_cons]
      simp only [bind, map_add, List.map_cons, List.sum_cons]
      have tail := ih (step read write increment tick key state).1 (closed key state valid)
      have first := bound key state valid
      omega

/-- A fixed input-key restriction may preserve finite support, key bounds,
or a cardinality envelope that arbitrary outside writes would violate. -/
theorem run_cost_le_sum_on [AddMonoid C] (h : C →+ Nat) (tariff : κ → Nat)
    (allowed : κ → Prop) (P : R × T → Prop)
    (closed : ∀ key state, allowed key → P state → P (step read write increment tick key state).1)
    (bound : ∀ key state, allowed key → P state →
      h (step read write increment tick key state).2 ≤ tariff key)
    (xs : List κ) (inputs : ∀ key ∈ xs, allowed key) (state : R × T) (valid : P state) :
    h (run read write increment tick terminal xs state).2 ≤
      (xs.map tariff).sum + h terminal := by
  induction xs generalizing state with
  | nil => simp
  | cons key xs ih =>
      have admitted := inputs key List.mem_cons_self
      have tail := ih (fun query inside => inputs query (List.mem_cons_of_mem key inside))
        (step read write increment tick key state).1 (closed key state admitted valid)
      have first := bound key state admitted valid
      rw [run_cons]
      simp only [bind, map_add, List.map_cons, List.sum_cons]
      omega

/-- Exact state-independent projected observations retain the final tariff. -/
theorem run_observation [AddMonoid C] (h : C →+ Nat) (observe : κ → Nat)
    (law : ∀ key state, h (step read write increment tick key state).2 = observe key)
    (xs : List κ) (state : R × T) :
    h (run read write increment tick terminal xs state).2 =
      (xs.map observe).sum + h terminal := by
  have observed := Resources.run_observation
    (fun key state => reweight h (step read write increment tick key state)) observe law xs state
  rw [← Resources.reweight_run] at observed
  change h (Resources.run (step read write increment tick) xs state).2 = _ at observed
  change h ((Resources.run (step read write increment tick) xs state).2 + terminal) = _
  rw [map_add, observed]

theorem run_constant_observation [AddMonoid C] (h : C →+ Nat) (rate : Nat)
    (law : ∀ key state, h (step read write increment tick key state).2 = rate)
    (xs : List κ) (state : R × T) :
    h (run read write increment tick terminal xs state).2 = rate * xs.length + h terminal := by
  simpa [Nat.mul_comm] using
    run_observation read write increment tick terminal h (fun _ => rate) law xs state

/-- Counter potential changes only on the branch that actually increments.
Other cost coordinates may still be nonzero; only this additive projection
must vanish on reads, writes, and loop entry. -/
theorem step_counter_potential [AddMonoid C] (h : C →+ Nat) (potential : R → Nat)
    (charge : Nat) (read_zero : ∀ key table, h (read key table).2 = 0)
    (write_zero : ∀ key table, h (write key true table).2 = 0) (tick_zero : h tick = 0)
    (increment_law : ∀ counter,
      h (increment counter).2 + potential (increment counter).1 = potential counter + charge)
    (key : κ) (state : R × T) :
    h (step read write increment tick key state).2 +
        potential (step read write increment tick key state).1.1 =
      potential state.1 + if (read key state.2).1 then charge else 0 := by
  cases seen : (read key state.2).1 <;>
    simp [step, bind, seen, map_add, read_zero, write_zero, tick_zero, increment_law]

/-- Exact telescoping along the actual sequence of selected duplicate branches. -/
theorem run_counter_potential [AddMonoid C] (h : C →+ Nat) (potential : R → Nat)
    (charge : Nat) (read_zero : ∀ key table, h (read key table).2 = 0)
    (write_zero : ∀ key table, h (write key true table).2 = 0)
    (tick_zero : h tick = 0) (terminal_zero : h terminal = 0)
    (increment_law : ∀ counter,
      h (increment counter).2 + potential (increment counter).1 = potential counter + charge)
    (xs : List κ) (state : R × T) :
    h (run read write increment tick terminal xs state).2 +
        potential (run read write increment tick terminal xs state).1.1 =
      potential state.1 + Resources.budget (step read write increment tick)
        (fun key state => if (read key state.2).1 then charge else 0) xs state := by
  have accounting := Resources.run_potential_map_exact (step read write increment tick)
    (fun key state => if (read key state.2).1 then charge else 0)
    (fun state => potential state.1) h
    (step_counter_potential read write increment tick h potential charge
      read_zero write_zero tick_zero increment_law) xs state
  simpa [run, bind, map_add, terminal_zero] using accounting

theorem run_counter_cost_le [AddMonoid C] (h : C →+ Nat) (potential : R → Nat)
    (charge : Nat) (read_zero : ∀ key table, h (read key table).2 = 0)
    (write_zero : ∀ key table, h (write key true table).2 = 0)
    (tick_zero : h tick = 0) (terminal_zero : h terminal = 0)
    (increment_law : ∀ counter,
      h (increment counter).2 + potential (increment counter).1 = potential counter + charge)
    (xs : List κ) (state : R × T) :
    h (run read write increment tick terminal xs state).2 ≤ potential state.1 + charge * xs.length := by
  have accounting := run_counter_potential read write increment tick terminal h potential charge
    read_zero write_zero tick_zero terminal_zero increment_law xs state
  have bound := Resources.budget_le_constant
    (fun key state => reweight h (step read write increment tick key state))
    (fun key state => if (read key state.2).1 then charge else 0) charge
    (by intro key state; split <;> omega) xs state
  rw [← Resources.budget_congr_state (step read write increment tick)
    (fun key state => reweight h (step read write increment tick key state))
    (fun key state => if (read key state.2).1 then charge else 0) (by intros; rfl)] at bound
  omega

end Laws

/-- Nat-counter erasure needs only the three measured-value equations, not table laws. -/
theorem step_value [Add C] (ops : Search.TotalTable.Ops κ Bool T)
    (read : κ → T → Measured Bool C) (write : κ → Bool → T → Measured T C)
    (increment : Nat → Measured Nat C) (tick : C)
    (read_value : ∀ key table, (read key table).1 = ops.get key table)
    (write_value : ∀ key table, (write key true table).1 = ops.set key true table)
    (increment_value : ∀ counter, (increment counter).1 = counter + 1)
    (key : κ) (state : Nat × T) :
    (step read write increment tick key state).1 = Search.Collisions.step ops state key := by
  cases seen : ops.get key state.2 <;>
    simp [step, bind, Search.Collisions.step, read_value, write_value, increment_value, seen]

theorem run_value [Zero C] [Add C] (ops : Search.TotalTable.Ops κ Bool T)
    (read : κ → T → Measured Bool C) (write : κ → Bool → T → Measured T C)
    (increment : Nat → Measured Nat C) (tick terminal : C)
    (read_value : ∀ key table, (read key table).1 = ops.get key table)
    (write_value : ∀ key table, (write key true table).1 = ops.set key true table)
    (increment_value : ∀ counter, (increment counter).1 = counter + 1)
    (xs : List κ) (state : Nat × T) :
    (run read write increment tick terminal xs state).1 = Search.Collisions.run ops xs state := by
  exact run_value_fusion read write increment tick terminal ops id (fun _ => True)
    (by intros; trivial)
    (fun key state _ => step_value ops read write increment tick read_value write_value increment_value key state)
    xs state trivial

/-- Literal unary addition, recurring on its first operand. Every entered
branch, including the zero branch, costs one constructor-pattern call. -/
def unaryAddRun : Nat → Nat → Measured Nat Nat
  | 0, n => (n, 1)
  | m + 1, n =>
      let next := unaryAddRun m n
      (next.1 + 1, 1 + next.2)

theorem unaryAddRun_value (m n : Nat) : (unaryAddRun m n).1 = m + n := by
  induction m with
  | zero => simp [unaryAddRun]
  | succ m ih => simp [unaryAddRun, ih, Nat.succ_add]

theorem unaryAddRun_cost (m n : Nat) : (unaryAddRun m n).2 = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [unaryAddRun, ih, Nat.add_comm]

end Resources.CollisionWork

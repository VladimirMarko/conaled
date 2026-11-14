import Applications.Suspensions.Relocation
import Applications.Suspensions.Derived

/-!
# Observing force after delay

The original computation and the delayed computation have related values and
stores. Existing addresses are fixed; later allocations are consistently
shifted past the additional private cell. Its successful cache write is omitted
from the represented store. Primitive equivariance and fixed initial captures
are explicit hypotheses, not assumptions about the body's evaluation result.
The contracts concern finite normal and raised completions, with explicit
body-relative transition counts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.ForceObservation
open Machine Renaming Relocation

variable {Primitive : Type}

/-- Initial cells contain no address whose identity this relocation changes.
This constrains their finite values/captures, not the computations they run. -/
def FixedCells (rename : Nat → Nat) (memory : Memory Primitive) : Prop :=
  ∀ address entry, memory.memory address = some entry → cell rename entry = entry

theorem fixed_empty (rename : Nat → Nat) :
    FixedCells rename (Suspensions.empty : Memory Primitive) := by
  intro address entry found
  cases found

theorem delay_states_related {memory : Memory Primitive} (bounded : Suspensions.Bounded memory)
    (fixed : FixedCells (shift memory.next) memory) (body : Expr Primitive) (env : Env Primitive) :
    StatesRelated memory.next memory (Suspensions.delay memory body env).1 := by
  refine ⟨⟨?_, rfl, ?_⟩, Nat.le_refl _⟩
  · change memory.next + 1 = shift memory.next memory.next
    exact (shift_new (Nat.le_refl _)).symm
  · intro address
    by_cases old : address < memory.next
    · rw [shift_old old]
      change (Suspensions.allocate memory (.thunk body env)).1.memory address =
        (memory.memory address).map (cell (shift memory.next))
      rw [Suspensions.allocate_other _ _ (by omega)]
      cases found : memory.memory address with
      | none => rfl
      | some entry => simp [fixed address entry found]
    · have newer : memory.next ≤ address := Nat.le_of_not_gt old
      rw [shift_new newer]
      change (Suspensions.allocate memory (.thunk body env)).1.memory (address + 1) =
        (memory.memory address).map (cell (shift memory.next))
      rw [Suspensions.allocate_other _ _ (by omega), bounded _ (by omega), bounded _ newer]
      rfl

theorem delay_configs_related {memory : Memory Primitive} (bounded : Suspensions.Bounded memory)
    (fixed : FixedCells (shift memory.next) memory) (body : Expr Primitive) (env : Env Primitive)
    (captured : environment (shift memory.next) env = env) :
    ConfigsRelated memory.next (start memory env body)
      (start (Suspensions.delay memory body env).1 env body) := by
  refine ⟨delay_states_related bounded fixed body env, ?_, rfl⟩
  simp only [start, Relocation.control, captured]

/-- The body may allocate, mutate references, raise and handle exceptions or
use recursive closures. Its actual finite normal execution is transported. -/
theorem value_observed {parameters : Parameters Primitive} {memory afterBody : Memory Primitive}
    {env : Env Primitive} {body : Expr Primitive} {v : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift memory.next))
    (bounded : Suspensions.Bounded memory) (fixed : FixedCells (shift memory.next) memory)
    (captured : environment (shift memory.next) env = env)
    (execution : Progress.Evaluates (step parameters) (start memory env body)
      ⟨afterBody, .value v⟩ steps) :
    ∃ finalMemory, Progress.Evaluates (step parameters)
      (start memory env (force (.delay body)))
      ⟨finalMemory, .value (value (shift memory.next) v)⟩ (steps + 12) ∧
      StatesRelated memory.next afterBody finalMemory := by
  obtain ⟨answer, bodyRun, related⟩ := evaluates_forward equivariant execution
    (delay_configs_related bounded fixed body env captured)
  rcases answer with ⟨reached, outcome⟩
  have returned : outcome = .value (value (shift memory.next) v) := related.2
  subst outcome
  refine ⟨Suspensions.memoize reached memory.next (value (shift memory.next) v),
    Derived.force_delay_value bodyRun, ?_⟩
  exact ⟨related.1.1.private_replace (.value (value (shift memory.next) v)), related.1.2⟩

/-- An exceptional body adds no successful write at the forcing frame. The
body's effects and its packet are still related to the direct execution. -/
theorem raised_observed {parameters : Parameters Primitive} {memory afterBody : Memory Primitive}
    {env : Env Primitive} {body : Expr Primitive} {packet : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift memory.next))
    (bounded : Suspensions.Bounded memory) (fixed : FixedCells (shift memory.next) memory)
    (captured : environment (shift memory.next) env = env)
    (execution : Progress.Evaluates (step parameters) (start memory env body)
      ⟨afterBody, .raised packet⟩ steps) :
    ∃ finalMemory, Progress.Evaluates (step parameters)
      (start memory env (force (.delay body)))
      ⟨finalMemory, .raised (value (shift memory.next) packet)⟩ (steps + 10) ∧
      StatesRelated memory.next afterBody finalMemory := by
  obtain ⟨answer, bodyRun, related⟩ := evaluates_forward equivariant execution
    (delay_configs_related bounded fixed body env captured)
  rcases answer with ⟨reached, outcome⟩
  have returned : outcome = .raised (value (shift memory.next) packet) := related.2
  subst outcome
  exact ⟨reached, Derived.force_delay_raised bodyRun, related.1⟩

/-- A normal delayed result also reflects an actual direct body execution.
The relation deliberately omits the additional private cache cell. -/
theorem value_reflected {parameters : Parameters Primitive} {memory afterForce : Memory Primitive}
    {env : Env Primitive} {body : Expr Primitive} {v : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift memory.next))
    (bounded : Suspensions.Bounded memory) (fixed : FixedCells (shift memory.next) memory)
    (captured : environment (shift memory.next) env = env)
    (execution : Progress.Evaluates (step parameters) (start memory env (force (.delay body)))
      ⟨afterForce, .value v⟩ steps) :
    ∃ directMemory directValue bodySteps,
      Progress.Evaluates (step parameters) (start memory env body)
        ⟨directMemory, .value directValue⟩ bodySteps ∧
      v = value (shift memory.next) directValue ∧ steps = bodySteps + 12 ∧
      StatesRelated memory.next directMemory afterForce := by
  obtain ⟨allocatedBody, bodySteps, bodyRun, finalMemory, count⟩ :=
    Derived.force_delay_value_iff.mp execution
  obtain ⟨answer, directRun, related⟩ := evaluates_backward equivariant bodyRun
    (delay_configs_related bounded fixed body env captured)
  rcases answer with ⟨directMemory, outcome⟩
  have resultEq := related.2
  cases outcome with
  | value directValue =>
      have values : v = value (shift memory.next) directValue := Result.value.inj resultEq
      refine ⟨directMemory, directValue, bodySteps, directRun, values, count, ?_⟩
      rw [finalMemory]
      exact ⟨related.1.1.private_replace (.value v), related.1.2⟩
  | _ => simp [result] at resultEq

/-- Raised completion reflects the same kind of direct completion, with its
packet and reached effects related rather than replaced by a normal value. -/
theorem raised_reflected {parameters : Parameters Primitive} {memory afterForce : Memory Primitive}
    {env : Env Primitive} {body : Expr Primitive} {packet : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift memory.next))
    (bounded : Suspensions.Bounded memory) (fixed : FixedCells (shift memory.next) memory)
    (captured : environment (shift memory.next) env = env)
    (execution : Progress.Evaluates (step parameters) (start memory env (force (.delay body)))
      ⟨afterForce, .raised packet⟩ steps) :
    ∃ directMemory directPacket bodySteps,
      Progress.Evaluates (step parameters) (start memory env body)
        ⟨directMemory, .raised directPacket⟩ bodySteps ∧
      packet = value (shift memory.next) directPacket ∧ steps = bodySteps + 10 ∧
      StatesRelated memory.next directMemory afterForce := by
  obtain ⟨bodySteps, bodyRun, count⟩ := Derived.force_delay_raised_iff.mp execution
  obtain ⟨answer, directRun, related⟩ := evaluates_backward equivariant bodyRun
    (delay_configs_related bounded fixed body env captured)
  rcases answer with ⟨directMemory, outcome⟩
  have resultEq := related.2
  cases outcome with
  | raised directPacket =>
      exact ⟨directMemory, directPacket, bodySteps, directRun,
        Result.raised.inj resultEq, count, related.1⟩
  | _ => simp [result] at resultEq

/-- Empty memory and environment provide a uniform client for arbitrary bodies,
including those that allocate. The finite-run premise is retained. -/
theorem closed_value_observed {parameters : Parameters Primitive}
    {afterBody : Memory Primitive} {body : Expr Primitive} {v : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift 0))
    (execution : Progress.Evaluates (step parameters) (start Suspensions.empty [] body)
      ⟨afterBody, .value v⟩ steps) :
    ∃ finalMemory, Progress.Evaluates (step parameters)
      (start Suspensions.empty [] (force (.delay body)))
      ⟨finalMemory, .value (value (shift 0) v)⟩ (steps + 12) ∧
      StatesRelated 0 afterBody finalMemory :=
  value_observed equivariant Suspensions.bounded_empty (fixed_empty _) (environment_nil _) execution

end Suspensions.Core.ForceObservation

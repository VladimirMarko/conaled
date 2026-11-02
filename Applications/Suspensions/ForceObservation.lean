import Applications.Suspensions.Relocation
import Applications.Suspensions.Derived

/-!
# Observing force after delay

The original computation and the delayed computation have related values and
stores. Existing addresses are fixed; later allocations are consistently
shifted past the additional private cell. Its successful cache write is omitted
from the represented store. Primitive equivariance and fixed initial captures
are explicit hypotheses, not assumptions about the body's evaluation result.
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
  simp only [start, control, captured]

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

/-- Empty captured memory is a uniform client for arbitrary closed bodies,
not just literals or allocation-free data expressions. -/
theorem closed_value_observed {parameters : Parameters Primitive}
    {afterBody : Memory Primitive} {body : Expr Primitive} {v : Value Primitive} {steps : Nat}
    (equivariant : Equivariant parameters (shift 0))
    (execution : Progress.Evaluates (step parameters) (start Suspensions.empty [] body)
      ⟨afterBody, .value v⟩ steps) :
    ∃ finalMemory, Progress.Evaluates (step parameters)
      (start Suspensions.empty [] (force (.delay body)))
      ⟨finalMemory, .value (value (shift 0) v)⟩ (steps + 12) ∧
      StatesRelated 0 afterBody finalMemory :=
  value_observed equivariant Suspensions.bounded_empty (fixed_empty _) rfl execution

end Suspensions.Core.ForceObservation

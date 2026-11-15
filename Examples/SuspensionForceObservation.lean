import Applications.Suspensions.ForceObservation
import Examples.SuspensionRelocation

/-!
# Force/delay preserves the reference observations

The execution theorem is applied to the independently computed direct body.
It yields the differently numbered returned reference and both observable heap
effects, while retaining the extra twelve explicit forcing transitions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionForceObservation
open Suspensions Suspensions.Core Suspensions.Core.Machine
open Suspensions.Core.Renaming Suspensions.Core.Relocation Suspensions.Core.ForceObservation
open Examples.SuspensionRelocation

theorem initial_bounded : Bounded initial := allocate_bounded bounded_empty _

private theorem initial_next : initial.next = 1 := rfl

theorem initial_fixed : FixedCells (shift initial.next) initial := by
  intro address entry found
  by_cases atZero : address = 0
  · subst address
    change some (.value (integer 5)) = some entry at found
    cases found
    simp [integer]
  · simp [initial, Suspensions.allocate, Suspensions.empty, Durability.put, atZero] at found

theorem reference_effects_after_force :
    ∃ memory, Progress.Evaluates (step parameters) (start initial bindings (force (.delay body)))
      ⟨memory, .value (.address 2)⟩ 25 ∧
      memory.memory 0 = some (.value (integer 7)) ∧
      memory.memory 2 = some (.value (integer 9)) ∧ memory.next = 3 := by
  obtain ⟨memory, execution, related⟩ := value_observed
    (primitives_equivariant 1) initial_bounded initial_fixed bindings_fixed direct_execution
  refine ⟨memory, ?_, ?_, ?_, ?_⟩
  · simpa [initial_next] using execution
  · simpa [initial_next, direct_observations.1, integer] using related.1.lookup 0
  · simpa [initial_next, direct_observations.2.1, integer] using related.1.lookup 1
  · simpa [initial_next, direct_observations.2.2] using related.1.frontier

theorem every_normal_force_return {memory : Memory Unit} {returned : Value Unit} {count : Nat}
    (execution : Progress.Evaluates (step parameters) (start initial bindings (force (.delay body)))
      ⟨memory, .value returned⟩ count) :
    returned = .address 2 ∧ count = 25 ∧
      memory.memory 0 = some (.value (integer 7)) ∧
      memory.memory 2 = some (.value (integer 9)) := by
  obtain ⟨directMemory, directValue, bodySteps, directRun, values, steps, related⟩ :=
    value_reflected (primitives_equivariant 1) initial_bounded initial_fixed bindings_fixed execution
  have same := directRun.unique direct_execution
  have memoryEq : directMemory = directFinal := congrArg Answer.memory same.1
  have valueEq : directValue = .address 1 := Result.value.inj (congrArg Answer.result same.1)
  have countEq := same.2
  subst directMemory
  subst directValue
  subst bodySteps
  refine ⟨?_, steps, ?_, ?_⟩
  · simpa [initial_next] using values
  · simpa [initial_next, direct_observations.1, integer] using related.1.lookup 0
  · simpa [initial_next, direct_observations.2.1, integer] using related.1.lookup 1

def exceptionMemory : Memory Unit := { initial with exceptionNames := {0, 1, 2} }

private theorem exceptionMemory_next : exceptionMemory.next = 1 := rfl

def exceptionBindings : Env Unit := [(0, .address 0), (3, .exception 2 none)]

theorem exception_bindings_fixed : environment (shift 1) exceptionBindings = exceptionBindings := by
  simp [exceptionBindings]

def raisingBody : Expr Unit :=
  .bind .wildcard (.assign (.variable 0) (.atom (.integer 7))) (.raise (.variable 3))

theorem exception_memory_bounded : Bounded exceptionMemory := initial_bounded

theorem exception_memory_fixed : FixedCells (shift exceptionMemory.next) exceptionMemory :=
  initial_fixed

theorem direct_exception :
    Progress.Evaluates (step parameters) (start exceptionMemory exceptionBindings raisingBody)
      ⟨Suspensions.memoize exceptionMemory 0 (integer 7), .raised (.exception 2 none)⟩ 13 :=
  Progress.search_sound (fuel := 32) (by rfl)

theorem reference_effect_before_exception :
    ∃ memory, Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionBindings (force (.delay raisingBody)))
      ⟨memory, .raised (.exception 2 none)⟩ 23 ∧
      memory.memory 0 = some (.value (integer 7)) ∧ memory.next = 2 ∧
      memory.exceptionNames = {0, 1, 2} := by
  obtain ⟨memory, execution, related⟩ := raised_observed
    (primitives_equivariant 1) exception_memory_bounded exception_memory_fixed
      exception_bindings_fixed direct_exception
  refine ⟨memory, ?_, ?_, ?_, related.1.exceptionNames⟩
  · simpa using execution
  · simpa [exceptionMemory_next, integer] using related.1.lookup 0
  · simpa [exceptionMemory_next] using related.1.frontier

theorem every_raised_force_return {memory : Memory Unit} {packet : Value Unit} {count : Nat}
    (execution : Progress.Evaluates (step parameters)
      (start exceptionMemory exceptionBindings (force (.delay raisingBody)))
      ⟨memory, .raised packet⟩ count) : packet = .exception 2 none ∧ count = 23 := by
  obtain ⟨directMemory, directPacket, bodySteps, directRun, packets, steps, _⟩ :=
    raised_reflected (primitives_equivariant 1) exception_memory_bounded exception_memory_fixed
      exception_bindings_fixed execution
  have same := directRun.unique direct_exception
  have packetEq : directPacket = .exception 2 none :=
    Result.raised.inj (congrArg Answer.result same.1)
  have countEq := same.2
  subst directPacket
  subst bodySteps
  exact ⟨by simpa using packets, steps⟩

/-- Bounded memory alone does not validate captured dangling addresses. -/
def dangling : Env Unit := [(1, .address 0)]

def danglingRead : Expr Unit := .read (.variable 1)

theorem dangling_not_fixed : environment (shift 0) dangling ≠ dangling := by
  simp [dangling]

theorem dangling_direct_fault :
    Progress.Evaluates (step parameters) (start Suspensions.empty dangling danglingRead)
      ⟨Suspensions.empty, .stuck (.missingAddress 0)⟩ 3 :=
  Progress.search_sound (fuel := 8) (by rfl)

theorem dangling_force_fault :
    Progress.Evaluates (step parameters)
      (start Suspensions.empty dangling (force (.delay danglingRead)))
      ⟨(Suspensions.delay Suspensions.empty danglingRead dangling).1,
        .stuck .expectedReferenceValue⟩ 10 :=
  Progress.search_sound (fuel := 16) (by rfl)

end Examples.SuspensionForceObservation

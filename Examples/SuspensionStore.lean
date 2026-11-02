import Applications.Suspensions.Store

/-!
# Captured environments, recursive footprints and successive cache writes

These are concrete clients of the generic memory laws. Code is an opaque
natural-number identifier; the examples do not pretend to execute its body.
The evaluator supplies that separate correspondence. Values distinguish
ordinary numbers from addresses, with references and suspensions sharing the
same memory address space.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionStore
open Suspensions

inductive Payload where
  | number (value : Nat)
  | address (location : Nat)

private abbrev Env := List (Nat × Payload)
private abbrev MemoryState := State Nat Env Payload

private def captured : Env := [(10, .number 1)]
private def otherEnv : Env := [(10, .number 2)]
private def initial : MemoryState :=
  { empty with exceptionNames := {17, 23} }

private theorem initial_bounded : Bounded initial := fun _ _ => rfl

private def target : MemoryState × Nat := delay initial 42 captured
private def unrelated : MemoryState × Nat := delay target.1 99 otherEnv
private def withReference : MemoryState × Nat := allocate unrelated.1 (.value (.number 41))

private theorem target_bounded : Bounded target.1 := delay_bounded initial_bounded 42 captured
private theorem unrelated_bounded : Bounded unrelated.1 := delay_bounded target_bounded 99 otherEnv
private theorem reference_bounded : Bounded withReference.1 :=
  allocate_bounded unrelated_bounded (.value (.number 41))

private theorem target_lookup :
    withReference.1.memory target.2 = some (.thunk 42 captured) := by
  have first := delay_captures initial 42 captured
  have kept := allocate_retains target_bounded first (.thunk 99 otherEnv)
  exact allocate_retains unrelated_bounded kept (.value (.number 41))

private theorem unrelated_lookup :
    withReference.1.memory unrelated.2 = some (.thunk 99 otherEnv) :=
  allocate_retains unrelated_bounded (delay_captures target.1 99 otherEnv) (.value (.number 41))

private theorem reference_lookup :
    withReference.1.memory withReference.2 = some (.value (.number 41)) :=
  allocate_lookup unrelated.1 (.value (.number 41))

/-- Creation stores the original lexical binding, even though an unrelated
later creation uses a shadowing environment. The ordinary reference cell is
retained alongside the two thunks in the same address space. -/
theorem creation_captures_environment :
    target.2 = 0 ∧ withReference.1.next = 3 ∧
      withReference.1.memory target.2 = some (.thunk 42 [(10, .number 1)]) ∧
      withReference.1.memory unrelated.2 = some (.thunk 99 [(10, .number 2)]) ∧
      withReference.1.memory withReference.2 = some (.value (.number 41)) ∧
      withReference.1.exceptionNames = {17, 23} ∧ Bounded withReference.1 :=
  ⟨rfl, rfl, target_lookup, unrelated_lookup, reference_lookup, rfl, reference_bounded⟩

/-- The deterministic choice is a witness of the frontier-free source
allocation relation, rather than a replacement definition of freshness. -/
theorem creation_realizes_fresh_choice :
    FreshAllocation initial.memory (.thunk 42 captured) target.2 target.1.memory :=
  delay_realizes initial_bounded 42 captured

/-- Equal code and environment do not cause two independent creations to
share an identity. The second creation also retains the first stored thunk. -/
theorem repeated_creation_is_distinct :
    (delay target.1 42 captured).2 ≠ target.2 ∧
      (delay target.1 42 captured).1.memory target.2 = some (.thunk 42 captured) :=
  ⟨allocate_distinct initial (.thunk 42 captured) (.thunk 42 captured),
    allocate_retains target_bounded (delay_captures initial 42 captured) (.thunk 42 captured)⟩

private def extendEnv (old : Env) : Env := (99, .address target.2) :: old
private def rebound : MemoryState := srec withReference.1 {target.2} extendEnv

private theorem recursive_targets : RecursiveTargets withReference.1 {target.2} := by
  intro address inside
  have equal : address = target.2 := Finset.mem_singleton.mp inside
  subst address
  exact ⟨42, captured, target_lookup⟩

private theorem rebound_target :
    rebound.memory target.2 = some (.thunk 42 (extendEnv captured)) :=
  srec_thunk extendEnv (by simp) target_lookup

private theorem rebound_unrelated :
    rebound.memory unrelated.2 = some (.thunk 99 otherEnv) :=
  (srec_other withReference.1 {target.2} extendEnv (by decide)).trans unrelated_lookup

private theorem rebound_reference :
    rebound.memory withReference.2 = some (.value (.number 41)) :=
  (srec_other withReference.1 {target.2} extendEnv (by decide)).trans reference_lookup

/-- Only the selected thunk acquires its recursive address binding. Code 42,
the unrelated thunk, the reference, the finite memory domain and the exception
names remain intact. The new environment refers to its own address zero. -/
theorem recursive_extension_footprint :
    rebound.memory 0 = some (.thunk 42 [(99, .address 0), (10, .number 1)]) ∧
      rebound.memory 1 = some (.thunk 99 [(10, .number 2)]) ∧
      rebound.memory 2 = some (.value (.number 41)) ∧
      domain rebound = domain withReference.1 ∧
      rebound.next = 3 ∧ rebound.exceptionNames = {17, 23} ∧
      Bounded rebound ∧ RecursiveTargets rebound {target.2} :=
  ⟨rebound_target, rebound_unrelated, rebound_reference,
    srec_domain withReference.1 {target.2} extendEnv, rfl, rfl,
    srec_bounded reference_bounded {target.2} extendEnv, recursive_targets.srec extendEnv⟩

/-- The source applicability premise exposes original unforced thunks and the
corresponding extended closures at every valid recursive target. -/
theorem valid_recursive_binding_updates_closure :
    ∃ code env, withReference.1.memory target.2 = some (.thunk code env) ∧
      rebound.memory target.2 = some (.thunk code (extendEnv env)) :=
  recursive_targets.updated extendEnv (by simp)

/-- The raw total operation leaves an ordinary value unchanged even if that
address is selected. This case does not assert a valid recursive binding. -/
theorem selected_value_is_unchanged :
    (srec withReference.1 {withReference.2} extendEnv).memory withReference.2 =
      some (.value (.number 41)) :=
  srec_value {withReference.2} extendEnv reference_lookup

private def twiceWritten : MemoryState :=
  memoize (memoize rebound target.2 (.number 7)) target.2 (.number 8)

/-- These are the two memory writes available to an inner successful forcing
frame and a later outer successful frame. Their actual evaluator execution is
a separate client; the store laws permit the outer value 8 to overwrite 7. -/
theorem later_successful_write_wins :
    twiceWritten.memory target.2 = some (.value (.number 8)) ∧
      twiceWritten.memory withReference.2 = some (.value (.number 41)) ∧
      twiceWritten.memory unrelated.2 = some (.thunk 99 otherEnv) ∧
      twiceWritten.next = 3 ∧ twiceWritten.exceptionNames = {17, 23} ∧
      domain twiceWritten = domain rebound ∧ Bounded twiceWritten := by
  have reduced : twiceWritten = memoize rebound target.2 (.number 8) :=
    memoize_overwrite rebound target.2 (.number 7) (.number 8)
  have valid := srec_bounded reference_bounded {target.2} extendEnv
  rw [reduced]
  refine ⟨memoize_lookup _ _ _, ?_, ?_, rfl, rfl,
    memoize_domain valid rebound_target _, memoize_bounded valid rebound_target _⟩
  · exact (memoize_other rebound target.2 (.number 8) (by decide)).trans rebound_reference
  · exact (memoize_other rebound target.2 (.number 8) (by decide)).trans rebound_unrelated

/-- The finite frontier accounts for every occupied address, including after
the environment cycle and both writes. -/
theorem finite_memory_observation (address : Nat) :
    address ∈ domain twiceWritten ↔ ∃ cell, twiceWritten.memory address = some cell :=
  mem_domain later_successful_write_wins.2.2.2.2.2.2 address

end Examples.SuspensionStore

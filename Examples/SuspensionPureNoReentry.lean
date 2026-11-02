import Applications.Suspensions.Pure.NoReentry
import Examples.SuspensionPureMachine

/-!
# A mutually recursive source program cannot finish after actual self-entry

The source creates function f and suspension s; s calls f, and f forces s.
Starting from the empty raw heap, an independently reduced 29-transition
prefix reaches a second force while the first memoize occurrence remains at
index 3. The public source theorem then excludes every finite raw result.
Bounded search failure is a consequence for every fuel, not the evidence
used to infer nontermination.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureNoReentry
open Suspensions Suspensions.Pure
open Suspensions.Pure.Domain Suspensions.Pure.Compatibility
open Suspensions.Pure.WorldDomain Suspensions.Pure.Simulation
open Examples.SuspensionPureMachine

private def rawParameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 0
  bindException := 1

private def operations : Empty → Prop := fun _ => False

private theorem compatible : ParametersCompatible operations rawParameters parameters where
  primitive impossible := nomatch impossible
  matchException := rfl
  bindException := rfl

private theorem preserve : ParametersPreserve operations parameters := by
  intro impossible
  cases impossible

private theorem cycle_clauses_allowed : ClausesCodeAllowed operations cycleClauses :=
  (ClausesCodeAllowed.cons_iff _ _ []).mpr
    ⟨.record .nil, (CodeAllowed.variable 2).force, ClausesCodeAllowed.nil⟩

private theorem cycle_body_allowed : CodeAllowed operations cycleBody :=
  (CodeAllowed.apply_iff _ _).mpr
    ⟨CodeAllowed.variable 1, (CodeAllowed.record_iff []).mpr NamedCodeAllowed.nil⟩

private theorem cycle_definitions_allowed :
    NamedCodeAllowed operations (Rhs.toBindings cycleDefinitions) := by
  apply (NamedCodeAllowed.cons_iff _ _ _).mpr
  refine ⟨(CodeAllowed.function_iff _).mpr cycle_clauses_allowed, ?_⟩
  apply (NamedCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨(CodeAllowed.delay_iff _).mpr cycle_body_allowed, NamedCodeAllowed.nil⟩

private theorem cycle_code_allowed : CodeAllowed operations cycleTerm :=
  (CodeAllowed.recursive_iff _ _).mpr
    ⟨cycle_definitions_allowed, (CodeAllowed.variable 2).force,
      Rhs.toBindings_permitted cycleDefinitions, by decide⟩

private def created : Core.Env Empty :=
  [(2, .address 0), (1, .closure cycleClauses [] [])]
private def closedMemory : Core.Machine.Memory Empty :=
  Core.Recursive.closeMemory (Suspensions.delay Suspensions.empty cycleBody []).1 created
private def environment : Core.Env Empty := Core.Recursive.closeEnvironment [] created
private def beforeSecondEntry : Core.Machine.Config Empty :=
  ⟨closedMemory, .pattern environment (.suspended (.variable 0)) (.address 0),
    [.clause environment (.variable 0) [] (.address 0),
     .applicationResult, .applicationResult, .memoize 0 environment (.variable 0),
     .clause environment (.variable 0) [] (.address 0), .applicationResult]⟩

private theorem actual_prefix : Core.Prefix.observe rawParameters 29
    (Core.Machine.start Suspensions.empty [] cycleTerm) = .inr beforeSecondEntry := rfl

private theorem actual_event :
    (Core.Machine.transition rawParameters beforeSecondEntry).2 = .body 0 := rfl

/-- This is a theorem about the original heap machine from an actual source
start, including any hypothetical normal, exceptional or fault completion. -/
theorem cyclic_source_has_no_finite_raw_result :
    ¬Progress.Terminates (Core.Machine.step rawParameters)
      (Core.Machine.start Suspensions.empty [] cycleTerm) :=
  source_reentry_not_terminates compatible preserve WorldAllowed.empty
    (Memory.StateRep.empty parameters) Representation.EnvRep.nil EnvAllowed.nil
    cycle_code_allowed actual_prefix actual_event (frameIndex := 3) rfl

theorem cyclic_source_search_is_none (fuel : Nat) :
    Progress.search (Core.Machine.step rawParameters) fuel
      (Core.Machine.start Suspensions.empty [] cycleTerm) = none := by
  cases found : Progress.search (Core.Machine.step rawParameters) fuel
      (Core.Machine.start Suspensions.empty [] cycleTerm) with
  | none => rfl
  | some result =>
      exact False.elim (cyclic_source_has_no_finite_raw_result
        ⟨result.1, result.2, Progress.search_sound found⟩)

end Examples.SuspensionPureNoReentry

import Applications.Suspensions.Pure.RecursiveStep

/-!
# Recursive creation while an older suspension is active

The outer thunk is already being forced at address 0. Its body creates an
unforced recursive thunk at address 1 and returns that new binding. The five
raw creation transitions correspond to one pure step and retain the older
pending force's executed history. The local theorem supplies the connection;
independent reductions identify its concrete reached configurations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureRecursiveStep
open Suspensions Suspensions.Pure
open Suspensions.Pure.Representation Suspensions.Pure.Domain
open Suspensions.Pure.WorldDomain Suspensions.Pure.History Suspensions.Pure.Simulation

private def rawParameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

private def pureParameters : Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

private def operations : Empty → Prop := fun _ => False
private def definitions : List (Nat × Rhs Empty) := [(1, .delay (.atom (.integer 7)))]
private def outerBody : Core.Expr Empty :=
  .recursive (Rhs.toBindings definitions) (.variable 1)
private def outerMeaning : Meaning Empty := ⟨outerBody, [], none⟩
private def beforeMemory : Core.Machine.Memory Empty :=
  (Suspensions.delay Suspensions.empty outerBody []).1
private def beforeWorld : World Empty := Durability.put (fun _ => none) 0 outerMeaning
private def rawStack : List (Core.Machine.Frame Empty) := [.memoize 0 [] .wildcard]
private def pureStack : List (Machine.Frame Empty) := [.force [] .wildcard]
private def rawBefore : Core.Machine.Config Empty := ⟨beforeMemory, .eval [] outerBody, rawStack⟩
private def pureBefore : Machine.Config Empty := ⟨.eval [] outerBody, pureStack⟩
private def preclose : Core.Machine.Memory Empty :=
  (Suspensions.delay beforeMemory (.atom (.integer 7)) []).1
private def created : Core.Env Empty := [(1, .address 1)]
private def rawAfter : Core.Machine.Config Empty :=
  ⟨Core.Recursive.closeMemory preclose created,
    .eval (Core.Recursive.closeEnvironment [] created) (.variable 1), rawStack⟩
private def pureAfter : Machine.Config Empty :=
  ⟨.eval (bodyEnvironment [] (some (.mk definitions []))) (.variable 1), pureStack⟩

private theorem outer_code : CodeAllowed operations outerBody := by
  apply (CodeAllowed.recursive_iff _ _).mpr
  refine ⟨?_, CodeAllowed.variable 1, Rhs.toBindings_permitted definitions, by decide⟩
  apply (NamedCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨(CodeAllowed.delay_iff _).mpr (CodeAllowed.atom (.integer 7)), NamedCodeAllowed.nil⟩

private theorem before_state : Memory.StateRep pureParameters beforeWorld beforeMemory :=
  ((Memory.StateRep.empty pureParameters).delay EnvRep.nil outerBody).2.1

private theorem before_allowed : WorldAllowed operations beforeWorld :=
  WorldAllowed.empty.put 0 outerMeaning (.suspension outer_code .nil .none)

private theorem pending_history :
    ActiveHistories pureParameters beforeWorld rawStack (.eval [] outerBody) pureStack := by
  intro index address environment inner found
  cases index with
  | zero =>
      have same : Core.Machine.Frame.memoize 0 [] .wildcard =
          .memoize address environment inner := Option.some.inj found
      cases same
      exact ⟨outerMeaning, 0, rfl, rfl⟩
  | succ index => simp [rawStack] at found

/-- Both reached configurations are fixed by the independently calculated
creation prefix. The still-pending outer occurrence has a valid past history
after creation, and no new body was entered during those five transitions. -/
theorem creation_preserves_active_history :
    ∃ world,
      Durability.Extends beforeWorld world ∧ WorldAllowed operations world ∧
      Core.Prefix.observe rawParameters 5 rawBefore = .inr rawAfter ∧
      Recurrence.Reaches pureParameters 1 pureBefore pureAfter ∧
      ConfigRep pureParameters world rawAfter pureAfter ∧
      (∀ index config, index < 5 →
        Core.Prefix.observe rawParameters index rawBefore = .inr config →
        ∀ address, (Core.Machine.transition rawParameters config).2 ≠ .body address) := by
  have frames : FramesRep beforeWorld rawStack pureStack :=
    .cons (.memoize .wildcard (meaning := outerMeaning) rfl .nil) .nil
  obtain ⟨world, rawNext, pureNext, extension, allowed, rawPrefix, purePrefix, represented, events⟩ :=
    recursive_entry rawParameters before_state before_allowed EnvRep.nil EnvAllowed.nil
      outer_code frames pending_history
  have rawKnown : Core.Prefix.observe rawParameters 5 rawBefore = .inr rawAfter := rfl
  have pureKnown : Recurrence.Reaches pureParameters 1 pureBefore pureAfter := rfl
  have rawSame : rawNext = rawAfter := Sum.inr.inj (rawPrefix.symm.trans rawKnown)
  have pureSame : pureNext = pureAfter := Sum.inr.inj (purePrefix.symm.trans pureKnown)
  subst rawNext
  subst pureNext
  exact ⟨world, extension, allowed, rawKnown, pureKnown, represented, events⟩

end Examples.SuspensionPureRecursiveStep

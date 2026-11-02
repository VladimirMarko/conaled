import Applications.Suspensions.Pure.Creation

/-!
# Actual creation supplies a finite recursive-group representation

A mutually dependent function and suspension are created beside an old
occupied cell. The public pending/closing laws connect the actual receipt to
the immutable meanings and to the machine's eight-transition creation prefix.
The cyclic bodies are never evaluated here. A duplicate-name example exposes
the shadowed delay that SRec does not close.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureCreation
open Suspensions Suspensions.Pure Suspensions.Pure.Representation Suspensions.Pure.Creation

private def parameters : Core.Machine.Parameters Empty where
  primitive := fun impossible _ => nomatch impossible
  matchException := 20
  bindException := 21

private def oldBody : Core.Expr Empty := .atom (.integer 41)
private def oldMeaning : Meaning Empty := ⟨oldBody, [], none⟩
private def initial : Core.Machine.Memory Empty :=
  (Suspensions.allocate Suspensions.empty (.value (.atom (.integer 41)))).1
private def initialWorld : World Empty := Durability.put (fun _ => none) 0 oldMeaning
private def rawOuter : Core.Env Empty := [(99, .address 0)]
private def pureOuter : Env Empty := [(99, oldMeaning.value)]

private theorem initial_bounded : Suspensions.Bounded initial :=
  Suspensions.allocate_bounded (s := (Suspensions.empty : Core.Machine.Memory Empty))
    Suspensions.bounded_empty (.value (.atom (.integer 41)))

private theorem initial_world_below :
    ∀ address meaning, initialWorld address = some meaning → address < initial.next := by
  intro address meaning found
  by_cases same : address = 0
  · subst address
    decide
  · simp [initialWorld, Durability.put, same] at found

private theorem outer_represented : EnvRep initialWorld rawOuter pureOuter :=
  .cons (.address rfl) .nil

private def clauses : List (Core.Pattern × Core.Expr Empty) :=
  [(.wildcard, Core.force (.variable 2))]
private def body : Core.Expr Empty := .apply (.variable 1) (.record [])
private def definitions : List (Nat × Rhs Empty) :=
  [(1, .function clauses), (2, .delay body)]
private def group : Suspensions.Pure.Group Empty := .mk definitions pureOuter
private def preclose : Core.Machine.Memory Empty := (Suspensions.delay initial body rawOuter).1
private def template : Core.Env Empty :=
  [(2, .address 1), (1, .closure clauses rawOuter [])]
private def closed := Core.Recursive.closeMemory preclose template
private def closedEnv := Core.Recursive.closeEnvironment rawOuter template
private def newMeaning : Meaning Empty := ⟨body, pureOuter, some group⟩

private theorem creation_receipt :
    Core.Recursive.create initial rawOuter (Rhs.toBindings definitions) [] =
      .ok (preclose, template) := rfl

private theorem distinct_names : (definitions.map Prod.fst).Nodup := by decide

/-- The actual mutual group has a represented closed capture and keeps its
old cell. The final conjunct connects this model to the actual machine prefix. -/
theorem mutual_creation_and_closing :
    ∃ world,
      PendingGroup initialWorld world initial preclose rawOuter group template ∧
      world 1 = some newMeaning ∧
      EnvRep world closedEnv (bodyEnvironment pureOuter (some group)) ∧
      (∃ captured, closed.memory 1 = some (.thunk body captured) ∧
        EnvRep world captured newMeaning.environment) ∧
      closed.memory 0 = some (.value (.atom (.integer 41))) ∧
      Core.Prefix.observe parameters 8
        (Core.Machine.start initial rawOuter
          (.recursive (Rhs.toBindings definitions) (.variable 2))) =
        .inr (Core.Machine.start closed closedEnv (.variable 2)) := by
  obtain ⟨world, pending⟩ := create_pending initial_bounded initial_world_below
    outer_represented distinct_names creation_receipt
  have freshMeaning : world 1 = some newMeaning := by
    have represented := pending.members
    cases represented with
    | delay found rest => exact found
  refine ⟨world, pending, freshMeaning, pending.closed_environment outer_represented,
    pending.closed_new outer_represented freshMeaning rfl, ?_, ?_⟩
  · exact pending.closed_old initial_bounded creation_receipt rfl
  · exact Core.Recursive.enter_body_prefix (Rhs.toBindings_permitted definitions)
      creation_receipt (.variable 2)

/-- The new raw thunk closes over both members and the old outer binding.
Function identifier 1 is independent of the old occupied heap address 0. -/
theorem mutual_raw_footprint :
    closed.next = 2 ∧
      closed.memory 1 = some (.thunk body closedEnv) ∧
      Core.Env.lookup closedEnv 2 = some (.address 1) ∧
      Core.Env.lookup closedEnv 1 = some (.closure clauses rawOuter template) ∧
      Core.Env.lookup closedEnv 99 = some (.address 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def duplicateBody : Core.Expr Empty := .atom (.integer 7)
private def duplicateClauses : List (Core.Pattern × Core.Expr Empty) :=
  [(.wildcard, .atom (.integer 8))]
private def duplicateDefinitions : List (Nat × Rhs Empty) :=
  [(5, .delay duplicateBody), (5, .function duplicateClauses)]
private def duplicateGroup : Suspensions.Pure.Group Empty := .mk duplicateDefinitions []
private def duplicateMemory : Core.Machine.Memory Empty :=
  (Suspensions.delay Suspensions.empty duplicateBody []).1
private def duplicateTemplate : Core.Env Empty :=
  [(5, .closure duplicateClauses [] []), (5, .address 0)]
private def duplicateMeaning : Meaning Empty := ⟨duplicateBody, [], some duplicateGroup⟩
private def duplicateWorld : World Empty :=
  Durability.put (fun _ => none) 0 duplicateMeaning

/-- The raw machine accepts these RHS shapes, but their repeated identifier
hides the allocated delay from the effective SRec targets. -/
theorem duplicate_delay_is_not_closed :
    ¬(duplicateDefinitions.map Prod.fst).Nodup ∧
      Core.Recursive.create Suspensions.empty [] (Rhs.toBindings duplicateDefinitions) [] =
        .ok (duplicateMemory, duplicateTemplate) ∧
      Core.Machine.addressRange (Core.Env.rec duplicateTemplate) = ∅ ∧
      (Core.Recursive.closeMemory duplicateMemory duplicateTemplate).memory 0 =
        some (.thunk duplicateBody []) :=
  ⟨by decide, rfl, rfl, rfl⟩

/-- Giving the shadowed cell a full-group meaning cannot meet the pending
certificate's closure obligation. Distinctness is not a cosmetic premise. -/
theorem duplicate_group_pending_rejected :
    ¬PendingGroup (fun _ => none) duplicateWorld Suspensions.empty duplicateMemory
      [] duplicateGroup duplicateTemplate := by
  intro pending
  rcases pending.entries 0 duplicateMeaning rfl with old | ⟨body, equal, cell, inside⟩
  · cases old
  · rw [duplicate_delay_is_not_closed.2.2.1] at inside
    exact Finset.notMem_empty _ inside

end Examples.SuspensionPureCreation

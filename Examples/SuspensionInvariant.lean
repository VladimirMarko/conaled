import Applications.Suspensions.Invariant

/-!
# Finite memory for successful forcing and cyclic unfinished execution

The positive cases consume the machine invariant from bounded initial memory.
The cyclic case reaches two pending memoize frames for the same address; it
makes no claim that this execution eventually terminates. A forged raw frame
also witnesses why memory boundedness alone is an insufficient premise.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionInvariant
open Suspensions Suspensions.Core Suspensions.Core.Machine

private def parameters : Parameters Unit where
  primitive := fun _ _ => .stuck .primitive
  matchException := 20
  bindException := 21

private def initial : Memory Unit := { Suspensions.empty with exceptionNames := {20, 21} }
private theorem initial_bounded : Bounded initial := fun _ _ => rfl

private def seven : Value Unit := .atom (.integer 7)
private def bodySeven : Expr Unit := .atom (.integer 7)
private def created := Suspensions.delay initial bodySeven []
private def forced := Suspensions.memoize created.1 created.2 seven
private def forceStart := startPattern created.1 [] (.suspended .wildcard) (.address created.2)

private theorem created_bounded : Bounded created.1 :=
  Suspensions.delay_bounded initial_bounded bodySeven []

private theorem force_run :
    Progress.Evaluates (step parameters) forceStart ⟨forced, .matched []⟩ 5 :=
  .next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))

/-- The final finite-domain observation is derived from the actual five-step
evaluation, not assumed as a property of its answer. -/
theorem successful_force_is_finite :
    Progress.Evaluates (step parameters) forceStart ⟨forced, .matched []⟩ 5 ∧
      Bounded forced ∧ forced.next = 1 ∧
      forced.memory 0 = some (.value seven) ∧
      ∀ address, address ∈ Suspensions.domain forced ↔
        ∃ cell, forced.memory address = some cell := by
  have bounded : Bounded forced := startPattern_evaluates_bounded created_bounded force_run
  exact ⟨force_run, bounded, rfl, Suspensions.memoize_lookup created.1 created.2 seven,
    fun address => Suspensions.mem_domain bounded address⟩

private def cycleBody : Expr Unit :=
  .bind (.suspended .wildcard) (.variable 1) (.atom (.integer 0))
private def cycleCreated := Suspensions.delay initial cycleBody []
private def cycleEnv : Env Unit := [(1, .address cycleCreated.2)]
private def cycleMemory : Memory Unit :=
  Suspensions.srec cycleCreated.1 {cycleCreated.2} (fun old => Env.extend old cycleEnv)
private def cycleStart : Config Unit :=
  startPattern cycleMemory [] (.suspended .wildcard) (.address cycleCreated.2)
private def cycleNext : Config Unit :=
  ⟨cycleMemory, .eval cycleEnv cycleBody,
    [.memoize cycleCreated.2 cycleEnv .wildcard,
     .bindMatch cycleEnv (.atom (.integer 0)),
     .memoize cycleCreated.2 [] .wildcard]⟩

private theorem cycle_bounded : Bounded cycleMemory :=
  Suspensions.srec_bounded (Suspensions.delay_bounded initial_bounded cycleBody []) _ _

/-- Five actual forcing transitions reenter the same stored body. The two
pending memoize frames deliberately have the same address. -/
theorem cyclic_prefix_reenters :
    Prefix.observe parameters 5 cycleStart = .inr cycleNext := rfl

theorem cyclic_reentry_keeps_finite_memory :
    Prefix.observe parameters 5 cycleStart = .inr cycleNext ∧
      ConfigBounded cycleNext ∧ cycleMemory.next = 1 ∧
      cycleMemory.memory 0 = some (.thunk cycleBody cycleEnv) := by
  have valid : ConfigBounded cycleStart :=
    startPattern_bounded cycle_bounded [] (.suspended .wildcard) (.address cycleCreated.2)
  exact ⟨cyclic_prefix_reenters,
    observe_unfinished_bounded valid cyclic_prefix_reenters, rfl, rfl⟩

/-- Every supplied finite budget has bounded reached memory, whether its
observation is unfinished or finished. No divergence conclusion is inferred. -/
theorem cyclic_finite_prefixes (budget : Nat) :
    OutcomeBounded (Prefix.observe parameters budget cycleStart) :=
  observe_bounded
    (startPattern_bounded cycle_bounded [] (.suspended .wildcard) (.address cycleCreated.2)) budget

private def forged : Config Unit :=
  ⟨initial, .value seven, [.memoize 0 [] .wildcard]⟩
private def forgedNext : Config Unit :=
  ⟨Suspensions.memoize initial 0 seven, .pattern [] .wildcard seven, []⟩

/-- A raw frame, unreachable from a bounded fresh start, can write at the
frontier without allocating. The invariant excludes this missing premise. -/
theorem bounded_memory_alone_is_insufficient :
    Bounded forged.memory ∧ ¬ ConfigBounded forged ∧
      step parameters forged = .inr forgedNext ∧ ¬ Bounded forgedNext.memory := by
  refine ⟨initial_bounded, ?_, rfl, ?_⟩
  · intro valid
    have head : FrameBounded (Primitive := Unit) initial.next (.memoize 0 [] .wildcard) :=
      ((List.forall_cons _ _ []).mp valid.2).1
    have impossible : 0 < 0 := head 0 [] .wildcard rfl
    exact Nat.not_lt_zero 0 impossible
  · intro bounded
    have absent := bounded 0 (Nat.le_refl 0)
    change (Suspensions.memoize initial 0 seven).memory 0 = none at absent
    rw [Suspensions.memoize_lookup] at absent
    cases absent

end Examples.SuspensionInvariant

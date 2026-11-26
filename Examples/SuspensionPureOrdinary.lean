import Applications.Suspensions.Pure.Ordinary
import Applications.Suspensions.Pure.Forcing

/-!
# Actual ordinary transitions and preserved pending-force history

The examples use the public step correspondence, with explicit raw and pure
answers. Wrong operands and malformed continuation modes remain observable
faults even though every stored value and source expression is admitted by
the hereditary code domain.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureOrdinary
open Suspensions Suspensions.Pure Suspensions.Pure.Representation
open Suspensions.Pure.Memory Suspensions.Pure.History Suspensions.Pure.Simulation
open Suspensions.Pure.Compatibility Suspensions.Pure.Domain Suspensions.Pure.DomainState

def parameters : Machine.Parameters BasicOperation := basicPureParameters 0 1
def rawParameters : Core.Machine.Parameters BasicOperation := basicRawParameters 0 1
def Selected : BasicOperation → Prop := fun _ => True

theorem compatible : ParametersCompatible Selected rawParameters parameters :=
  basic_parameters_compatible 0 1

def world : World BasicOperation := fun _ => none
def memory : Core.Machine.Memory BasicOperation := Suspensions.empty
def integer (value : Int) : Core.Expr BasicOperation := .atom (.integer value)

theorem empty_represented : StateRep parameters world memory := StateRep.empty parameters

/-- Literal evaluation and final delivery are two distinct actual steps. -/
theorem literal_step : OrdinaryStepRep parameters world memory
    (.inr ⟨memory, .value (.atom (.integer 7)), []⟩)
    (.inr ⟨.value (.atom (.integer 7)), []⟩) := by
  exact ordinary_step (ConfigRep.start empty_represented .nil (integer 7))
    (start_allowed (operations := Selected) .nil (CodeAllowed.atom (.integer 7))) compatible trivial

theorem literal_delivery : OrdinaryStepRep parameters world memory
    (.inl ⟨memory, .value (.atom (.integer 7))⟩) (.inl (.value (.atom (.integer 7)))) := by
  cases literal_step with
  | next unchanged represented =>
      exact ordinary_step represented ⟨.atom (.integer 7), trivial⟩ compatible trivial

/-- A nonsuspension operand is still ordinary, with the two corresponding
diagnostic names. No body or cache step is inserted. -/
theorem nonaddress_force : OrdinaryStepRep parameters world memory
    (.inl ⟨memory, .stuck .expectedAddress⟩) (.inl (.stuck .expectedSuspension)) := by
  exact ordinary_step
    (ConfigRep.startPattern empty_represented .nil (.atom (.integer 7)) (.suspended .wildcard))
    (startPattern_allowed (operations := Selected) .nil (.suspended .wildcard) (.atom (.integer 7)))
    compatible trivial

theorem nonaddress_force_has_no_body_event (address : Nat) :
    (Core.Machine.transition rawParameters
      (Core.Machine.startPattern memory [] (.suspended .wildcard) (.atom (.integer 7)))).2 ≠
        .body address := ordinary_event_ne_body rawParameters
          (raw := Core.Machine.startPattern memory [] (.suspended .wildcard) (.atom (.integer 7)))
          trivial address

private theorem no_pending {rawStack : List (Core.Machine.Frame BasicOperation)}
    {control : Machine.Control BasicOperation} {pureStack : List (Machine.Frame BasicOperation)}
    (absent : ∀ address environment inner,
      Core.Machine.Frame.memoize address environment inner ∉ rawStack) :
    ActiveHistories parameters world rawStack control pureStack := by
  intro index address environment inner found
  exact False.elim (absent address environment inner (List.mem_of_getElem? found))

private theorem one_frame_allowed {frame : Machine.Frame BasicOperation}
    (head : FrameAllowed Selected frame) : List.Forall (FrameAllowed Selected) [frame] :=
  (List.forall_cons _ _ _).mpr ⟨head, trivial⟩

private theorem successor_input (atom : Core.Atom) : ConfigRep parameters world
    ⟨memory, .value (.atom atom), [.argument (.primitive .successor)]⟩
    ⟨.value (.atom atom), [.argument (.primitive .successor)]⟩ :=
  ⟨empty_represented, .value (.atom atom),
    .cons (.argument (.primitive BasicOperation.successor)) .nil,
    no_pending (by intro address environment inner; simp)⟩

private theorem successor_allowed (atom : Core.Atom) : ConfigAllowed Selected
    ⟨.value (.atom atom), [.argument (.primitive .successor)]⟩ :=
  ⟨.atom atom, one_frame_allowed (.primitive trivial)⟩

/-- The selected primitive is executed, including its faulting raw input. -/
theorem successor_returns_eight : OrdinaryStepRep parameters world memory
    (.inr ⟨memory, .value (.atom (.integer 8)), []⟩)
    (.inr ⟨.value (.atom (.integer 8)), []⟩) :=
  ordinary_step (successor_input (.integer 7)) (successor_allowed (.integer 7)) compatible trivial

theorem successor_boolean_fault : OrdinaryStepRep parameters world memory
    (.inl ⟨memory, .stuck .primitive⟩) (.inl (.stuck .primitive)) :=
  ordinary_step (successor_input (.boolean true)) (successor_allowed (.boolean true)) compatible trivial

/-- Client composition supplies the independent primitive domain law; the
ordinary correspondence itself requires only relational compatibility. -/
private theorem checked_next {raw nextRaw : Core.Machine.Config BasicOperation}
    {view nextView : Machine.Config BasicOperation}
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed Selected view)
    (ordinary : IsOrdinary raw)
    (rawStep : Core.Machine.step rawParameters raw = .inr nextRaw)
    (pureStep : Machine.step parameters view = .inr nextView) :
    ConfigRep parameters world nextRaw nextView ∧ ConfigAllowed Selected nextView := by
  have moved := ordinary_step represented allowed compatible ordinary
  rw [rawStep, pureStep] at moved
  have retained := step_preserves (basic_parameters_preserve Selected 0 1) allowed
  change OutcomeAllowed Selected (Machine.step parameters view) at retained
  rw [pureStep] at retained
  cases moved with
  | next unchanged nextRep => exact ⟨nextRep, retained⟩

def fallback : List (Core.Pattern × Core.Expr BasicOperation) := [(.wildcard, integer 8)]
def rawReject : Core.Machine.Config BasicOperation :=
  ⟨memory, .pattern [] (.atom (.integer 0)) (.atom (.integer 7)),
    [.clause [] (integer 99) fallback (.atom (.integer 7))]⟩
def pureReject : Machine.Config BasicOperation :=
  ⟨.pattern [] (.atom (.integer 0)) (.atom (.integer 7)),
    [.clause [] (integer 99) fallback (.atom (.integer 7))]⟩

theorem rejecting_clause_represented : ConfigRep parameters world rawReject pureReject :=
  ⟨empty_represented, .pattern _ .nil (.atom (.integer 7)),
    .cons (.clause _ _ .nil (.atom (.integer 7))) .nil,
    no_pending (by intro address environment inner; simp [rawReject])⟩

theorem rejecting_clause_allowed : ConfigAllowed Selected pureReject :=
  ⟨⟨.nil, .atom (.integer 0), .atom (.integer 7)⟩,
    one_frame_allowed ⟨.nil, CodeAllowed.atom (.integer 99),
      (ClausesCodeAllowed.cons_iff _ _ _).mpr
        ⟨.wildcard, CodeAllowed.atom (.integer 8), ClausesCodeAllowed.nil⟩,
      .atom (.integer 7)⟩⟩

/-- Five actual ordinary transitions reject the first pattern, retain its
original argument, select the wildcard clause, and enter body8. Body99 is
never evaluated along this prefix. -/
theorem ordered_fallback_enters_eight :
    Core.Prefix.observe rawParameters 5 rawReject =
      .inr (Core.Machine.start memory [] (integer 8)) ∧
    Recurrence.Reaches parameters 5 pureReject (Machine.start [] (integer 8)) ∧
    ConfigRep parameters world
      (Core.Machine.start memory [] (integer 8)) (Machine.start [] (integer 8)) ∧
    ConfigAllowed Selected (Machine.start [] (integer 8)) := by
  refine ⟨rfl, rfl, ?_⟩
  have rejected := checked_next rejecting_clause_represented rejecting_clause_allowed trivial rfl rfl
  have continued := checked_next rejected.1 rejected.2 trivial rfl rfl
  have selectedClause := checked_next continued.1 continued.2 trivial rfl rfl
  have matched := checked_next selectedClause.1 selectedClause.2 trivial rfl rfl
  exact checked_next matched.1 matched.2 trivial rfl rfl

/-- Restricting stored code does not invent control-mode safety. -/
theorem wrong_return_mode_faults : OrdinaryStepRep parameters world memory
    (.inl ⟨memory, .stuck .invalidContinuation⟩) (.inl (.stuck .invalidContinuation)) := by
  have represented : ConfigRep parameters world
      ⟨memory, .value (.atom (.integer 7)), [.bindMatch [] (integer 99)]⟩
      ⟨.value (.atom (.integer 7)), [.bindMatch [] (integer 99)]⟩ :=
    ⟨empty_represented, .value (.atom (.integer 7)), .cons (.bindMatch _ .nil) .nil,
      no_pending (by intro address environment inner; simp)⟩
  exact ordinary_step represented
    ⟨.atom (.integer 7), one_frame_allowed ⟨.nil, CodeAllowed.atom (.integer 99)⟩⟩ compatible trivial

def pendingMeaning : Meaning BasicOperation := ⟨integer 7, [], none⟩
def pendingWorld : World BasicOperation := Durability.put world 0 pendingMeaning
def pendingMemory : Core.Machine.Memory BasicOperation :=
  (Suspensions.delay memory (integer 7) []).1

theorem pending_memory_represented : StateRep parameters pendingWorld pendingMemory :=
  (empty_represented.delay (.nil) (integer 7)).2.1

theorem pending_body_initial_history : ActiveHistories parameters pendingWorld
    [.memoize 0 [] .wildcard] (.eval [] (integer 7)) [.force [] .wildcard] := by
  intro index address environment inner found
  cases index with
  | zero =>
      have same : Core.Machine.Frame.memoize 0 [] .wildcard =
          .memoize address environment inner := Option.some.inj found
      cases same
      exact ⟨pendingMeaning, 0, rfl, rfl⟩
  | succ index => simp at found

/-- An ordinary body step advances a nonempty pending-force history. -/
theorem pending_literal_step : OrdinaryStepRep parameters pendingWorld pendingMemory
    (.inr ⟨pendingMemory, .value (.atom (.integer 7)), [.memoize 0 [] .wildcard]⟩)
    (.inr ⟨.value (.atom (.integer 7)), [.force [] .wildcard]⟩) := by
  have represented : ConfigRep parameters pendingWorld
      ⟨pendingMemory, .eval [] (integer 7), [.memoize 0 [] .wildcard]⟩
      ⟨.eval [] (integer 7), [.force [] .wildcard]⟩ :=
    ⟨pending_memory_represented, .eval _ .nil, .cons (.memoize _ rfl .nil) .nil,
      pending_body_initial_history⟩
  exact ordinary_step represented
    ⟨⟨.nil, CodeAllowed.atom (.integer 7)⟩, one_frame_allowed ⟨.nil, .wildcard⟩⟩ compatible trivial

/-- The actual past prefix returned by ordinary_step supplies the later cache
certificate. No separately assumed terminating-body proof is needed here. -/
theorem pending_history_justifies_cache :
    let cached := Suspensions.memoize pendingMemory 0 (.atom (.integer 7))
    Core.Machine.transition rawParameters
        ⟨pendingMemory, .value (.atom (.integer 7)), [.memoize 0 [] .wildcard]⟩ =
      (.inr ⟨cached, .pattern [] .wildcard (.atom (.integer 7)), []⟩, .cacheWrite 0) ∧
    ConfigRep parameters pendingWorld ⟨cached, .pattern [] .wildcard (.atom (.integer 7)), []⟩
      ⟨.pattern [] .wildcard (.atom (.integer 7)), []⟩ ∧
    cached.memory 0 = some (.value (.atom (.integer 7))) := by
  cases pending_literal_step with
  | next unchanged represented =>
      have written := return_memoize rawParameters (address := 0) (meaning := pendingMeaning)
        represented.memory rfl (.nil) (.atom (.integer 7)) (.nil) represented.histories
      exact ⟨written.1, written.2.2, rfl⟩

end Examples.SuspensionPureOrdinary

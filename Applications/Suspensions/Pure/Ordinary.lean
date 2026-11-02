import Applications.Suspensions.Pure.Simulation
import Applications.Suspensions.Pure.Compatibility
import Applications.Suspensions.Pure.DomainState

/-!
# Ordinary transitions preserve the pure interpretation

An ordinary source transition takes one actual step in each existing machine.
It retains the raw memory and immutable world. Pending force histories advance
through the same step, including when their addresses are repeated.

Allocation, recursive creation, suspended address lookup and memoize return
belong to their separate correspondence laws. Wrong operands and invalid
continuations remain actual terminal faults. This relation does not assert
output code-domain preservation or a complete finite-run simulation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History Recurrence Compatibility Domain DomainState

attribute [local simp] Core.Machine.proceed Core.Machine.finish Machine.proceed Machine.finish
attribute [local simp] Meaning.value

variable {Primitive : Type}

inductive OrdinaryStepRep (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (initialMemory : Core.Machine.Memory Primitive) :
    Core.Machine.Answer Primitive ⊕ Core.Machine.Config Primitive →
      Machine.Result Primitive ⊕ Machine.Config Primitive → Prop
  | next {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}
      (memory : raw.memory = initialMemory) (represented : ConfigRep parameters world raw view) :
      OrdinaryStepRep parameters world initialMemory (.inr raw) (.inr view)
  | done {raw : Core.Machine.Answer Primitive} {view : Machine.Result Primitive}
      (memory : raw.memory = initialMemory) (represented : ResultRep world raw.result view) :
      OrdinaryStepRep parameters world initialMemory (.inl raw) (.inl view)

/-- The stable-state cases with separate heap/creation proofs. Wrong operands
remain ordinary; this predicate is not a type or well-formedness judgment. -/
def IsOrdinary (config : Core.Machine.Config Primitive) : Prop :=
  match config.control, config.stack with
  | .eval _ (.delay _), _ | .eval _ (.recursive _ _), _ => False
  | .pattern _ (.suspended _) (.address _), _ => False
  | .value _, .memoize _ _ _ :: _ | .raised _, .memoize _ _ _ :: _ => False
  | _, _ => True

/-- Exhaust the separately handled cases by their actual control/stack shapes. -/
theorem not_ordinary_iff (raw : Core.Machine.Config Primitive) :
    ¬IsOrdinary raw ↔
      (∃ environment body, raw.control = .eval environment (.delay body)) ∨
      (∃ environment bindings body, raw.control = .eval environment (.recursive bindings body)) ∨
      (∃ environment inner address,
        raw.control = .pattern environment (.suspended inner) (.address address)) ∨
      (∃ value address environment inner tail,
        raw.control = .value value ∧ raw.stack = .memoize address environment inner :: tail) ∨
      (∃ packet address environment inner tail,
        raw.control = .raised packet ∧ raw.stack = .memoize address environment inner :: tail) := by
  rcases raw with ⟨memory, control, stack⟩
  cases control with
  | eval environment expression => cases expression <;> simp [IsOrdinary]
  | value value =>
      cases stack with
      | nil => simp [IsOrdinary]
      | cons frame tail => cases frame <;> simp [IsOrdinary]
  | raised packet =>
      cases stack with
      | nil => simp [IsOrdinary]
      | cons frame tail => cases frame <;> simp [IsOrdinary]
  | pattern environment pattern value =>
      cases pattern <;> try simp [IsOrdinary]
      case suspended inner => cases value <;> simp
  | matched bindings => simp [IsOrdinary]
  | mismatch => simp [IsOrdinary]
  | clauses environment clauses value => simp [IsOrdinary]
  | rows environment patterns fields bindings => simp [IsOrdinary]
  | recursive environment bindings created body => simp [IsOrdinary]

private abbrev StepAt (rawParameters : Core.Machine.Parameters Primitive)
    (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (memory : Core.Machine.Memory Primitive) (rawControl : Core.Machine.Control Primitive)
    (control : Machine.Control Primitive) (rawStack : List (Core.Machine.Frame Primitive))
    (pureStack : List (Machine.Frame Primitive)) : Prop :=
  OrdinaryStepRep parameters world memory
    (Core.Machine.step rawParameters ⟨memory, rawControl, rawStack⟩)
    (Machine.step parameters ⟨control, pureStack⟩)

variable {parameters : Machine.Parameters Primitive} {world : World Primitive}
  {memory : Core.Machine.Memory Primitive}

private theorem keep_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack first pureStack)
    (represented : ControlRep world rawLast last)
    (moved : ∀ tail, Machine.step parameters ⟨first, tail⟩ = .inr ⟨last, tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawStack⟩) (.inr ⟨last, pureStack⟩) :=
  .next rfl ⟨state, represented, frames, histories.keep (fun tail => Reaches.one (moved tail))⟩

private theorem push_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack first pureStack)
    (represented : ControlRep world rawLast last) (frame : FrameRep world rawFrame pureFrame)
    (ordinary : ∀ address environment inner, rawFrame ≠ .memoize address environment inner)
    (moved : ∀ tail, Machine.step parameters ⟨first, tail⟩ = .inr ⟨last, pureFrame :: tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawFrame :: rawStack⟩) (.inr ⟨last, pureFrame :: pureStack⟩) :=
  .next rfl ⟨state, represented, .cons frame frames,
    histories.push (fun address environment inner same =>
      False.elim (ordinary address environment inner same)) (fun tail => Reaches.one (moved tail))⟩

private theorem pop_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {rawFrame : Core.Machine.Frame Primitive} {pureFrame : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (rawFrame :: rawStack) first (pureFrame :: pureStack))
    (represented : ControlRep world rawLast last)
    (moved : ∀ tail, Machine.step parameters ⟨first, pureFrame :: tail⟩ = .inr ⟨last, tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, rawStack⟩) (.inr ⟨last, pureStack⟩) :=
  .next rfl ⟨state, represented, frames, histories.pop (fun tail => Reaches.one (moved tail))⟩

private theorem replace_step {first last : Machine.Control Primitive}
    {rawLast : Core.Machine.Control Primitive}
    {oldRaw newRaw : Core.Machine.Frame Primitive} {oldPure newPure : Machine.Frame Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (oldRaw :: rawStack) first (oldPure :: pureStack))
    (represented : ControlRep world rawLast last) (frame : FrameRep world newRaw newPure)
    (ordinary : ∀ address environment inner, newRaw ≠ .memoize address environment inner)
    (moved : ∀ tail, Machine.step parameters ⟨first, oldPure :: tail⟩ = .inr ⟨last, newPure :: tail⟩) :
    OrdinaryStepRep parameters world memory
      (.inr ⟨memory, rawLast, newRaw :: rawStack⟩) (.inr ⟨last, newPure :: pureStack⟩) :=
  .next rfl ⟨state, represented, .cons frame frames,
    histories.replace (fun address environment inner same =>
      False.elim (ordinary address environment inner same)) (fun tail => Reaches.one (moved tail))⟩

private theorem finish_step {raw : Core.Machine.Result Primitive} {view : Machine.Result Primitive}
    (represented : ResultRep world raw view) :
    OrdinaryStepRep parameters world memory (.inl ⟨memory, raw⟩) (.inl view) := .done rfl represented

private theorem optional_none {view : Option (Value Primitive)}
    (represented : OptionalRep world none view) : view = none := by
  cases represented
  rfl

private theorem optional_some {raw : Core.Value Primitive} {view : Option (Value Primitive)}
    (represented : OptionalRep world (some raw) view) :
    ∃ value, view = some value ∧ ValueRep world raw value := by
  cases represented with
  | some value => exact ⟨_, rfl, value⟩

private theorem clauses_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (clauses : List (Core.Pattern × Core.Expr Primitive))
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (valueRep : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.clauses environment clauses value) pureStack) :
    StepAt rawParameters parameters world memory (.clauses rawEnvironment clauses rawValue)
      (.clauses environment clauses value) rawStack pureStack := by
  cases clauses with
  | nil => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | cons clause remaining =>
      rcases clause with ⟨pattern, body⟩
      exact push_step state frames histories (.pattern pattern captured valueRep)
        (.clause body remaining captured valueRep)
        (by intro address env inner same; cases same) (fun _ => rfl)

private theorem rows_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment rawFields rawBindings : Core.Env Primitive}
    {environment fields bindings : Env Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (patterns : List (Nat × Core.Pattern))
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (fieldsRep : EnvRep world rawFields fields) (bindingsRep : EnvRep world rawBindings bindings)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.rows environment patterns fields bindings) pureStack) :
    StepAt rawParameters parameters world memory (.rows rawEnvironment patterns rawFields rawBindings)
      (.rows environment patterns fields bindings) rawStack pureStack := by
  cases patterns with
  | nil => exact keep_step state frames histories (.matched bindingsRep) (fun _ => rfl)
  | cons field remaining =>
      rcases field with ⟨label, pattern⟩
      have lookup := fieldsRep.lookup label
      cases rawFound : Core.Env.lookup rawFields label with
      | none =>
          rw [rawFound] at lookup
          have pureFound := optional_none lookup
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, rawFound, pureFound] using
            (finish_step (parameters := parameters) (memory := memory) (world := world)
              (.stuck (raw := .missingField label) rfl))
      | some rawValue =>
          rw [rawFound] at lookup
          obtain ⟨value, pureFound, valueRep⟩ := optional_some lookup
          have result := push_step state frames histories (.pattern pattern captured valueRep)
            (.row remaining captured fieldsRep bindingsRep)
            (by intro address env inner same; cases same)
            (fun tail => by simp [Machine.step, Machine.transition, pureFound])
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, rawFound, pureFound] using result

private theorem matched_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawBindings : Core.Env Primitive} {bindings : Env Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (bindingsRep : EnvRep world rawBindings bindings)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.matched bindings) pureStack) :
    StepAt rawParameters parameters world memory (.matched rawBindings) (.matched bindings)
      rawStack pureStack := by
  cases frames with
  | nil => exact finish_step (.matched bindingsRep)
  | cons frame frames =>
      cases frame <;> try exact finish_step (.stuck rfl)
      case bindMatch body captured =>
        exact pop_step state frames histories (.eval body (captured.extend bindingsRep)) (fun _ => rfl)
      case clause body remaining captured valueRep =>
        exact pop_step state frames histories (.eval body (captured.extend bindingsRep)) (fun _ => rfl)
      case row remaining captured fieldsRep earlierRep =>
        exact pop_step state frames histories
          (.rows remaining captured fieldsRep (earlierRep.extend bindingsRep)) (fun _ => rfl)
      case layered name valueRep =>
        exact pop_step state frames histories
          (.matched ((EnvRep.cons valueRep EnvRep.nil).extend bindingsRep)) (fun _ => rfl)

private theorem mismatch_step {operations : Primitive → Prop}
    {rawParameters : Core.Machine.Parameters Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack .mismatch pureStack) :
    StepAt rawParameters parameters world memory .mismatch .mismatch rawStack pureStack := by
  cases frames with
  | nil => exact finish_step .mismatch
  | cons frame frames =>
      cases frame <;> try exact finish_step (.stuck rfl)
      case clause body remaining captured valueRep =>
        exact pop_step state frames histories (.clauses remaining captured valueRep) (fun _ => rfl)
      case bindMatch body captured =>
        have packet : ValueRep world (.exception rawParameters.bindException none)
            (.exception parameters.bindException none) := by
          rw [compatible.bindException]
          exact .exception .none
        exact pop_step state frames histories (.raised packet) (fun _ => rfl)
      case applicationResult =>
        have packet : ValueRep world (.exception rawParameters.matchException none)
            (.exception parameters.matchException none) := by
          rw [compatible.matchException]
          exact .exception .none
        exact pop_step state frames histories (.raised packet) (fun _ => rfl)
      case handlerResult original =>
        exact pop_step state frames histories (.raised original) (fun _ => rfl)
      case row remaining captured fieldsRep earlierRep =>
        exact pop_step state frames histories .mismatch (fun _ => rfl)
      case layered name valueRep =>
        exact pop_step state frames histories .mismatch (fun _ => rfl)

private theorem raised_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawPacket : Core.Value Primitive} {packet : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (represented : ValueRep world rawPacket packet)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.raised packet) pureStack)
    (ordinary : IsOrdinary ⟨memory, .raised rawPacket, rawStack⟩) :
    StepAt rawParameters parameters world memory (.raised rawPacket) (.raised packet)
      rawStack pureStack := by
  cases frames with
  | nil => exact finish_step (.raised represented)
  | cons frame frames =>
      cases frame <;> try exact False.elim ordinary
      all_goals try exact pop_step state frames histories (.raised represented) (fun _ => rfl)
      case handler clauses captured =>
        exact replace_step state frames histories (.clauses clauses captured represented)
          (.handlerResult represented) (by intro address env inner same; cases same) (fun _ => rfl)

private theorem eval_step (rawParameters : Core.Machine.Parameters Primitive)
    {operations : Primitive → Prop} {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {expression : Core.Expr Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.eval environment expression) pureStack)
    (allowed : ExpressionAllowed operations expression)
    (ordinary : IsOrdinary ⟨memory, .eval rawEnvironment expression, rawStack⟩) :
    StepAt rawParameters parameters world memory (.eval rawEnvironment expression)
      (.eval environment expression) rawStack pureStack := by
  cases allowed with
  | atom atom => exact keep_step state frames histories (.value (.atom atom)) (fun _ => rfl)
  | «variable» name =>
      have lookup := captured.lookup name
      cases rawFound : Core.Env.lookup rawEnvironment name with
      | none =>
          rw [rawFound] at lookup
          have pureFound := optional_none lookup
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, rawFound, pureFound] using
            (finish_step (parameters := parameters) (memory := memory) (world := world)
              (.stuck (raw := .unboundVariable name) rfl))
      | some rawValue =>
          rw [rawFound] at lookup
          obtain ⟨value, pureFound, valueRep⟩ := optional_some lookup
          have result := keep_step state frames histories (.value valueRep)
            (fun tail => by simp [Machine.step, Machine.transition, pureFound])
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, rawFound, pureFound] using result
  | @primitive operation selected =>
      exact keep_step state frames histories (.value (.primitive operation)) (fun _ => rfl)
  | constructor tag =>
      exact keep_step state frames histories (.value (.constructor .none)) (fun _ => rfl)
  | @constructorArgument tag body allowed =>
      exact push_step state frames histories (.eval body captured) (.constructor tag)
        (by intro address env inner same; cases same) (fun _ => rfl)
  | @record fields allowed =>
      cases fields with
      | nil => exact keep_step state frames histories (.value (.record .nil)) (fun _ => rfl)
      | cons field remaining =>
          rcases field with ⟨label, body⟩
          exact push_step state frames histories (.eval body captured) (.record label remaining captured .nil)
            (by intro address env inner same; cases same) (fun _ => rfl)
  | function allowed =>
      exact keep_step state frames histories (.value (.closure captured)) (fun _ => rfl)
  | @apply function argument operator operand =>
      exact push_step state frames histories (.eval function captured) (.function argument captured)
        (by intro address env inner same; cases same) (fun _ => rfl)
  | @bind pattern value body matching right continuation =>
      exact push_step state frames histories (.eval value captured) (.bindValue pattern body captured)
        (by intro address env inner same; cases same) (fun _ => rfl)
  | recursive definitions continuation => exact False.elim ordinary
  | @branch condition yes no test positive negative =>
      exact push_step state frames histories (.eval condition captured) (.branch yes no captured)
        (by intro address env inner same; cases same) (fun _ => rfl)
  | delay allowed => exact False.elim ordinary
  | @raise packet allowed =>
      exact push_step state frames histories (.eval packet captured) .raise
        (by intro address env inner same; cases same) (fun _ => rfl)
  | @handle body clauses bodyAllowed handlers =>
      exact push_step state frames histories (.eval body captured) (.handler clauses captured)
        (by intro address env inner same; cases same) (fun _ => rfl)

private theorem primitive_step (rawParameters : Core.Machine.Parameters Primitive)
    (operation : Primitive) {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (.argument (.primitive operation) :: rawStack)
      (.value value) (.argument (.primitive operation) :: pureStack))
    (outputs : PrimitiveResultRep world (rawParameters.primitive operation rawValue)
      (parameters.primitive operation value)) :
    StepAt rawParameters parameters world memory (.value rawValue) (.value value)
      (.argument (.primitive operation) :: rawStack) (.argument (.primitive operation) :: pureStack) := by
  generalize rawResult : rawParameters.primitive operation rawValue = rawOutput at outputs
  generalize pureResult : parameters.primitive operation value = pureOutput at outputs
  cases outputs with
  | value represented =>
      have result := pop_step state frames histories (.value represented)
        (fun tail => by simp [Machine.step, Machine.transition, pureResult])
      simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
        Machine.transition, rawResult, pureResult] using result
  | raised represented =>
      have result := pop_step state frames histories (.raised represented)
        (fun tail => by simp [Machine.step, Machine.transition, pureResult])
      simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
        Machine.transition, rawResult, pureResult] using result
  | stuck represented =>
      simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
        Machine.transition, rawResult, pureResult] using
        (finish_step (parameters := parameters) (memory := memory) (.stuck represented))

private theorem argument_step {operations : Primitive → Prop}
    {rawParameters : Core.Machine.Parameters Primitive}
    {rawValue rawFunction : Core.Value Primitive} {value function : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (state : StateRep parameters world memory) (operand : ValueRep world rawValue value)
    (operator : ValueRep world rawFunction function) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world (.argument rawFunction :: rawStack)
      (.value value) (.argument function :: pureStack))
    (allowed : ValueAllowed operations function) :
    StepAt rawParameters parameters world memory (.value rawValue) (.value value)
      (.argument rawFunction :: rawStack) (.argument function :: pureStack) := by
  cases operator <;> try exact finish_step (.stuck rfl)
  case closure captured =>
    exact replace_step state frames histories (.clauses _ captured operand) .applicationResult
      (by intro address env inner same; cases same) (fun _ => rfl)
  case recursiveClosure captured members =>
    exact replace_step state frames histories (.clauses _ (GroupRep.bodyEnvironment members captured) operand)
      .applicationResult (by intro address env inner same; cases same) (fun _ => rfl)
  case primitive operation =>
    exact primitive_step rawParameters operation state frames histories
      (compatible.primitive operation ((ValueAllowed.primitive_iff operation).mp allowed)
        world _ _ operand)
  case constructor argument =>
    cases argument with
    | none => exact pop_step state frames histories (.value (.constructor (.some operand))) (fun _ => rfl)
    | some represented => exact finish_step (.stuck rfl)
  case exception argument =>
    cases argument with
    | none => exact pop_step state frames histories (.value (.exception (.some operand))) (fun _ => rfl)
    | some represented => exact finish_step (.stuck rfl)

private theorem value_step {operations : Primitive → Prop}
    {rawParameters : Core.Machine.Parameters Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (state : StateRep parameters world memory) (represented : ValueRep world rawValue value)
    (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.value value) pureStack)
    (allowed : List.Forall (FrameAllowed operations) pureStack)
    (ordinary : IsOrdinary ⟨memory, .value rawValue, rawStack⟩) :
    StepAt rawParameters parameters world memory (.value rawValue) (.value value)
      rawStack pureStack := by
  cases frames with
  | nil => exact finish_step (.value represented)
  | cons frame frames =>
      obtain ⟨headAllowed, _⟩ := (List.forall_cons _ _ _).mp allowed
      cases frame <;> try exact finish_step (.stuck rfl)
      case constructor tag =>
        exact pop_step state frames histories (.value (.constructor (.some represented))) (fun _ => rfl)
      case record label remaining captured done =>
        have fields := done.append (EnvRep.cons (name := label) represented EnvRep.nil)
        cases remaining with
        | nil => exact pop_step state frames histories (.value (.record fields)) (fun _ => rfl)
        | cons field remaining =>
            rcases field with ⟨nextLabel, expression⟩
            exact replace_step state frames histories (.eval expression captured)
              (.record nextLabel remaining captured fields)
              (by intro address env inner same; cases same) (fun _ => rfl)
      case function argument captured =>
        exact replace_step state frames histories (.eval argument captured) (.argument represented)
          (by intro address env inner same; cases same) (fun _ => rfl)
      case argument function =>
        exact argument_step compatible state represented function frames histories headAllowed
      case bindValue pattern body captured =>
        exact replace_step state frames histories (.pattern pattern captured represented)
          (.bindMatch body captured) (by intro address env inner same; cases same) (fun _ => rfl)
      case branch yes no captured =>
        cases represented <;> try exact finish_step (.stuck rfl)
        case atom atom =>
          cases atom with
          | integer number => exact finish_step (.stuck rfl)
          | boolean selected =>
              cases selected <;> exact pop_step state frames histories (.eval _ captured) (fun _ => rfl)
      case raise =>
        cases represented <;> try exact finish_step (.stuck rfl)
        case exception argument =>
          exact pop_step state frames histories (.raised (.exception argument)) (fun _ => rfl)
      case handler clauses captured =>
        exact pop_step state frames histories (.value represented) (fun _ => rfl)
      case handlerResult original =>
        exact pop_step state frames histories (.value represented) (fun _ => rfl)
      case applicationResult =>
        exact pop_step state frames histories (.value represented) (fun _ => rfl)
      case memoize inner found captured => exact False.elim ordinary

private theorem constructor_pattern_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (tag : Nat) (argument : Option Core.Pattern)
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (represented : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern environment (.constructor tag argument) value) pureStack) :
    StepAt rawParameters parameters world memory (.pattern rawEnvironment (.constructor tag argument) rawValue)
      (.pattern environment (.constructor tag argument) value) rawStack pureStack := by
  cases represented with
  | atom atom => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | record fields => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | primitive operation => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | exception payload => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | address found => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | closure capture => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | recursiveClosure capture members => exact keep_step state frames histories .mismatch (fun _ => rfl)
  | @constructor actual rawArgument pureArgument payload =>
      cases argument with
      | none =>
          cases payload with
          | some payload => exact keep_step state frames histories .mismatch (fun _ => rfl)
          | none =>
              by_cases same : tag = actual
              · have result := keep_step state frames histories (.matched .nil)
                  (fun tail => by simp [Machine.step, Machine.transition, same])
                simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
                  Machine.transition, same] using result
              · have result := keep_step state frames histories .mismatch
                  (fun tail => by simp [Machine.step, Machine.transition, same])
                simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
                  Machine.transition, same] using result
      | some inner =>
          cases payload with
          | none => exact keep_step state frames histories .mismatch (fun _ => rfl)
          | some payload =>
              by_cases same : tag = actual
              · have result := keep_step state frames histories (.pattern inner captured payload)
                  (fun tail => by simp [Machine.step, Machine.transition, same])
                simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
                  Machine.transition, same] using result
              · have result := keep_step state frames histories .mismatch
                  (fun tail => by simp [Machine.step, Machine.transition, same])
                simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
                  Machine.transition, same] using result

private theorem exception_value_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (name tag : Nat) (argument : Option Core.Pattern)
    (rawFound : Core.Env.lookup rawEnvironment name = some (.exception tag none))
    (pureFound : Env.lookup environment name = some (.exception tag none))
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (represented : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern environment (.exception name argument) value) pureStack) :
    StepAt rawParameters parameters world memory (.pattern rawEnvironment (.exception name argument) rawValue)
      (.pattern environment (.exception name argument) value) rawStack pureStack := by
  cases represented <;>
    simp only [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
      Machine.transition, rawFound, pureFound]
  all_goals
    try
      exact keep_step state frames histories .mismatch
        (fun tail => by simp [Machine.step, Machine.transition, pureFound])
  case exception actual rawArgument pureArgument payload =>
    cases argument with
    | none =>
        cases payload with
        | some payload =>
            exact keep_step state frames histories .mismatch
              (fun tail => by simp [Machine.step, Machine.transition, pureFound])
        | none =>
            by_cases same : tag = actual
            · have result := keep_step state frames histories (.matched .nil)
                (fun tail => by simp [Machine.step, Machine.transition, pureFound, same])
              simpa [same] using result
            · have result := keep_step state frames histories .mismatch
                (fun tail => by simp [Machine.step, Machine.transition, pureFound, same])
              simpa [same] using result
    | some inner =>
        cases payload with
        | none =>
            exact keep_step state frames histories .mismatch
              (fun tail => by simp [Machine.step, Machine.transition, pureFound])
        | some payload =>
            by_cases same : tag = actual
            · have result := keep_step state frames histories (.pattern inner captured payload)
                (fun tail => by simp [Machine.step, Machine.transition, pureFound, same])
              simpa [same] using result
            · have result := keep_step state frames histories .mismatch
                (fun tail => by simp [Machine.step, Machine.transition, pureFound, same])
              simpa [same] using result

private theorem exception_pattern_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (name : Nat) (argument : Option Core.Pattern)
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (represented : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern environment (.exception name argument) value) pureStack) :
    StepAt rawParameters parameters world memory (.pattern rawEnvironment (.exception name argument) rawValue)
      (.pattern environment (.exception name argument) value) rawStack pureStack := by
  have lookup := captured.lookup name
  cases rawFound : Core.Env.lookup rawEnvironment name with
  | none =>
      rw [rawFound] at lookup
      have pureFound := optional_none lookup
      simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
        Machine.transition, rawFound, pureFound] using
        (finish_step (parameters := parameters) (memory := memory) (world := world)
          (.stuck (raw := .invalidExceptionBinding name) rfl))
  | some rawBinding =>
      rw [rawFound] at lookup
      obtain ⟨binding, pureFound, boundRep⟩ := optional_some lookup
      cases boundRep <;> try simpa [StepAt, Core.Machine.step, Core.Machine.transition,
        Machine.step, Machine.transition, rawFound, pureFound, Meaning.value] using
          (finish_step (parameters := parameters) (memory := memory) (world := world)
            (.stuck (raw := .invalidExceptionBinding name) rfl))
      case exception tag rawArgument pureArgument payload =>
        cases payload with
        | none =>
            exact exception_value_step rawParameters name tag argument rawFound pureFound
              state captured represented frames histories
        | some payload =>
            simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
              Machine.transition, rawFound, pureFound] using
              (finish_step (parameters := parameters) (memory := memory) (world := world)
                (.stuck (raw := .invalidExceptionBinding name) rfl))

private theorem record_pattern_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (patterns : List (Nat × Core.Pattern))
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (represented : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack
      (.pattern environment (.record patterns) value) pureStack) :
    StepAt rawParameters parameters world memory (.pattern rawEnvironment (.record patterns) rawValue)
      (.pattern environment (.record patterns) value) rawStack pureStack := by
  cases represented <;> try exact finish_step (.stuck rfl)
  case record fields =>
    cases patterns with
    | nil =>
        cases fields with
        | nil => exact keep_step state frames histories (.matched .nil) (fun _ => rfl)
        | cons head tail => exact finish_step (.stuck rfl)
    | cons pattern remaining =>
        cases fields with
        | nil =>
            exact keep_step state frames histories
              (.rows (pattern :: remaining) captured .nil .nil) (fun _ => rfl)
        | cons head tail =>
            exact keep_step state frames histories
              (.rows (pattern :: remaining) captured (.cons head tail) .nil) (fun _ => rfl)

private theorem pattern_step (rawParameters : Core.Machine.Parameters Primitive)
    {rawEnvironment : Core.Env Primitive} {environment : Env Primitive}
    {rawValue : Core.Value Primitive} {value : Value Primitive} {pattern : Core.Pattern}
    {rawStack : List (Core.Machine.Frame Primitive)} {pureStack : List (Machine.Frame Primitive)}
    (state : StateRep parameters world memory) (captured : EnvRep world rawEnvironment environment)
    (represented : ValueRep world rawValue value) (frames : FramesRep world rawStack pureStack)
    (histories : ActiveHistories parameters world rawStack (.pattern environment pattern value) pureStack)
    (allowed : PatternAllowed pattern)
    (ordinary : IsOrdinary ⟨memory, .pattern rawEnvironment pattern rawValue, rawStack⟩) :
    StepAt rawParameters parameters world memory (.pattern rawEnvironment pattern rawValue)
      (.pattern environment pattern value) rawStack pureStack := by
  cases allowed with
  | wildcard => exact keep_step state frames histories (.matched .nil) (fun _ => rfl)
  | «variable» name =>
      exact keep_step state frames histories (.matched (.cons represented .nil)) (fun _ => rfl)
  | atom atom =>
      cases represented <;> try exact keep_step state frames histories .mismatch (fun _ => rfl)
      case atom actual =>
        by_cases same : atom = actual
        · have result := keep_step state frames histories (.matched .nil)
            (fun tail => by simp [Machine.step, Machine.transition, same])
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, same] using result
        · have result := keep_step state frames histories .mismatch
            (fun tail => by simp [Machine.step, Machine.transition, same])
          simpa [StepAt, Core.Machine.step, Core.Machine.transition, Machine.step,
            Machine.transition, same] using result
  | constructor tag =>
      exact constructor_pattern_step rawParameters tag none state captured represented frames histories
  | @constructorArgument tag inner allowed =>
      exact constructor_pattern_step rawParameters tag (some inner) state captured represented frames histories
  | exception name =>
      exact exception_pattern_step rawParameters name none state captured represented frames histories
  | @exceptionArgument name inner allowed =>
      exact exception_pattern_step rawParameters name (some inner) state captured represented frames histories
  | @record patterns allowed =>
      exact record_pattern_step rawParameters patterns state captured represented frames histories
  | suspended allowed =>
      cases represented <;> try exact finish_step (.stuck expectedAddress_related)
      case address found => exact False.elim ordinary
  | @layered name inner allowed =>
      exact push_step state frames histories (.pattern inner captured represented) (.layered name represented)
        (by intro address env inner same; cases same) (fun _ => rfl)

/-- Every admitted ordinary raw step is matched by the actual pure step.
Primitive output-domain preservation is deliberately a separate law. -/
theorem ordinary_step {operations : Primitive → Prop}
    {rawParameters : Core.Machine.Parameters Primitive}
    {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (compatible : ParametersCompatible operations rawParameters parameters) (ordinary : IsOrdinary raw) :
    OrdinaryStepRep parameters world raw.memory
      (Core.Machine.step rawParameters raw) (Machine.step parameters view) := by
  rcases raw with ⟨memory, rawControl, rawStack⟩
  rcases view with ⟨control, pureStack⟩
  rcases represented with ⟨state, controls, frames, histories⟩
  obtain ⟨controlAllowed, frameAllowed⟩ := allowed
  cases controls with
  | eval expression captured =>
      exact eval_step rawParameters state captured frames histories controlAllowed.2.effects ordinary
  | value valueRep =>
      exact value_step compatible state valueRep frames histories frameAllowed ordinary
  | raised valueRep =>
      exact raised_step rawParameters state valueRep frames histories ordinary
  | pattern pattern captured valueRep =>
      exact pattern_step rawParameters state captured valueRep frames histories controlAllowed.2.1 ordinary
  | matched bindings => exact matched_step rawParameters state bindings frames histories
  | mismatch => exact mismatch_step compatible state frames histories
  | clauses clauses captured valueRep =>
      exact clauses_step rawParameters clauses state captured valueRep frames histories
  | rows patterns captured fields bindings =>
      exact rows_step rawParameters patterns state captured fields bindings frames histories

/-- The shape restriction alone rules out an uncached body-entry label in the
actual raw transition. It does not claim that arbitrary excluded-effect raw
programs are represented by the pure machine. -/
theorem ordinary_event_ne_body (rawParameters : Core.Machine.Parameters Primitive)
    {raw : Core.Machine.Config Primitive} (ordinary : IsOrdinary raw) (address : Nat) :
    (Core.Machine.transition rawParameters raw).2 ≠ .body address := by
  rcases raw with ⟨memory, control, stack⟩
  cases control <;>
    simp only [Core.Machine.transition, Core.Machine.proceed, Core.Machine.finish]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all [IsOrdinary])
      | split at *

end Suspensions.Pure.Simulation

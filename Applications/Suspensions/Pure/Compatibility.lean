import Applications.Suspensions.Pure.Representation
import Applications.Suspensions.Pure.Machine
import Applications.Suspensions.Machine

/-!
# Primitive and outcome compatibility for the pure interpretation

Primitive implementations remain ordinary machine parameters. The law below
relates their actual outputs on represented inputs in every immutable world.
It assumes no expression evaluation, termination or heap invariant.

`ValueRep` by itself does not restrict the source code or primitive tokens
inside returned values. An execution bridge also needs preservation of its
admissible-value policy. The concrete basis's output-origin theorems below
support that separate argument without choosing the policy here.

The fault correspondence is partial. Nonaddress forcing corresponds to a
nonsuspension operand in the pure machine. Missing raw addresses and reference
cell-kind faults have no corresponding pure fault; their exclusion in an
execution theorem must follow from its memory/domain and effect hypotheses.
Pure excluded-effect faults likewise have no image here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Compatibility
open Representation

/-- The common diagnostic observations, without inventing images for faults
which require separate domain/effect arguments in an execution bridge. -/
def faultView : Core.Machine.Fault → Option Machine.Fault
  | .unboundVariable name => some (.unboundVariable name)
  | .missingAddress _ => none
  | .expectedFunction => some .expectedFunction
  | .expectedBoolean => some .expectedBoolean
  | .expectedAddress => some .expectedSuspension
  | .expectedReferenceValue => none
  | .expectedException => some .expectedException
  | .expectedRecord => some .expectedRecord
  | .expectedEmptyRecord => some .expectedEmptyRecord
  | .missingField label => some (.missingField label)
  | .invalidExceptionBinding name => some (.invalidExceptionBinding name)
  | .invalidRecursiveRhs name => some (.invalidRecursiveRhs name)
  | .invalidContinuation => some .invalidContinuation
  | .primitive => some .primitive

def FaultRep (raw : Core.Machine.Fault) (view : Machine.Fault) : Prop :=
  faultView raw = some view

theorem expectedAddress_related : FaultRep .expectedAddress .expectedSuspension := rfl

theorem missingAddress_unrelated (address : Nat) (view : Machine.Fault) :
    ¬ FaultRep (.missingAddress address) view := by
  simp [FaultRep, faultView]

theorem referenceValue_unrelated (view : Machine.Fault) :
    ¬ FaultRep .expectedReferenceValue view := by
  simp [FaultRep, faultView]

theorem excludedEffect_unrelated (raw : Core.Machine.Fault) (effect : Machine.ExcludedEffect) :
    ¬ FaultRep raw (.excludedEffect effect) := by
  cases raw <;> simp [FaultRep, faultView]

theorem FaultRep.unique {raw : Core.Machine.Fault} {first second : Machine.Fault}
    (left : FaultRep raw first) (right : FaultRep raw second) : first = second :=
  Option.some.inj (left.symm.trans right)

inductive PrimitiveResultRep {Primitive : Type} (world : World Primitive) :
    Core.Machine.PrimitiveResult Primitive → Machine.PrimitiveResult Primitive → Prop
  | value {raw : Core.Value Primitive} {view : Value Primitive}
      (represented : ValueRep world raw view) : PrimitiveResultRep world (.value raw) (.value view)
  | raised {raw : Core.Value Primitive} {view : Value Primitive}
      (represented : ValueRep world raw view) : PrimitiveResultRep world (.raised raw) (.raised view)
  | stuck {raw : Core.Machine.Fault} {view : Machine.Fault}
      (represented : FaultRep raw view) : PrimitiveResultRep world (.stuck raw) (.stuck view)

/-- Outcome classes remain distinct. Reached raw memory is deliberately a
separate component of the future simulation invariant. -/
inductive ResultRep {Primitive : Type} (world : World Primitive) :
    Core.Machine.Result Primitive → Machine.Result Primitive → Prop
  | value {raw : Core.Value Primitive} {view : Value Primitive}
      (represented : ValueRep world raw view) : ResultRep world (.value raw) (.value view)
  | raised {raw : Core.Value Primitive} {view : Value Primitive}
      (represented : ValueRep world raw view) : ResultRep world (.raised raw) (.raised view)
  | matched {raw : Core.Env Primitive} {view : Env Primitive}
      (represented : EnvRep world raw view) : ResultRep world (.matched raw) (.matched view)
  | mismatch : ResultRep world .mismatch .mismatch
  | stuck {raw : Core.Machine.Fault} {view : Machine.Fault}
      (represented : FaultRep raw view) : ResultRep world (.stuck raw) (.stuck view)

variable {Primitive : Type}

theorem PrimitiveResultRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Machine.PrimitiveResult Primitive} {view : Machine.PrimitiveResult Primitive}
    (represented : PrimitiveResultRep before raw view) : PrimitiveResultRep after raw view := by
  cases represented with
  | value related => exact .value (related.mono extension)
  | raised related => exact .raised (related.mono extension)
  | stuck related => exact .stuck related

theorem ResultRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Machine.Result Primitive} {view : Machine.Result Primitive}
    (represented : ResultRep before raw view) : ResultRep after raw view := by
  cases represented with
  | value related => exact .value (related.mono extension)
  | raised related => exact .raised (related.mono extension)
  | matched related => exact .matched (related.mono extension)
  | mismatch => exact .mismatch
  | stuck related => exact .stuck related

theorem primitiveResult_atom_iff {world : World Primitive} (atom : Core.Atom)
    (view : Machine.PrimitiveResult Primitive) :
    PrimitiveResultRep world (.value (.atom atom)) view ↔ view = .value (.atom atom) := by
  constructor
  · intro represented
    cases represented with
    | value related => cases related; rfl
  · intro equal
    subst view
    exact .value (.atom atom)

/-- A single operation's compatibility, quantified over arbitrary worlds,
including worlds that give distinct raw addresses the same pure meaning. -/
def OperationCompatible
    (raw : Core.Value Primitive → Core.Machine.PrimitiveResult Primitive)
    (view : Value Primitive → Machine.PrimitiveResult Primitive) : Prop :=
  ∀ (world : World Primitive) (rawInput : Core.Value Primitive) (viewInput : Value Primitive),
    ValueRep world rawInput viewInput → PrimitiveResultRep world (raw rawInput) (view viewInput)

/-- Require laws only for the selected basis operations. Tag agreement is
separate from primitive behavior; source basis validity remains separate too. -/
structure ParametersCompatible (operations : Primitive → Prop)
    (raw : Core.Machine.Parameters Primitive) (view : Machine.Parameters Primitive) : Prop where
  primitive : ∀ operation, operations operation →
    OperationCompatible (raw.primitive operation) (view.primitive operation)
  matchException : raw.matchException = view.matchException
  bindException : raw.bindException = view.bindException

theorem ParametersCompatible.restrict {first second : Primitive → Prop}
    {raw : Core.Machine.Parameters Primitive} {view : Machine.Parameters Primitive}
    (compatible : ParametersCompatible first raw view)
    (included : ∀ operation, second operation → first operation) :
    ParametersCompatible second raw view where
  primitive operation allowed := compatible.primitive operation (included operation allowed)
  matchException := compatible.matchException
  bindException := compatible.bindException

def identityRaw (value : Core.Value Primitive) : Core.Machine.PrimitiveResult Primitive :=
  .value value

def identityPure (value : Value Primitive) : Machine.PrimitiveResult Primitive := .value value

theorem identity_compatible : OperationCompatible (identityRaw (Primitive := Primitive)) identityPure :=
  fun _ _ _ represented => .value represented

/-- A concrete scalar adapter. Other value shapes give a deterministic
primitive fault; no pointer, closure-code or allocation observation occurs. -/
def onIntegerRaw (operation : Int → Core.Atom) :
    Core.Value Primitive → Core.Machine.PrimitiveResult Primitive
  | .atom (.integer value) => .value (.atom (operation value))
  | _ => .stuck .primitive

def onIntegerPure (operation : Int → Core.Atom) : Value Primitive → Machine.PrimitiveResult Primitive
  | .atom (.integer value) => .value (.atom (operation value))
  | _ => .stuck .primitive

theorem onInteger_compatible (operation : Int → Core.Atom) :
    OperationCompatible (onIntegerRaw (Primitive := Primitive) operation) (onIntegerPure operation) := by
  intro world raw view represented
  cases represented with
  | atom atom =>
      cases atom with
      | boolean value => exact .stuck rfl
      | integer value => exact .value (.atom (operation value))
  | constructor _ => exact .stuck rfl
  | record _ => exact .stuck rfl
  | primitive _ => exact .stuck rfl
  | exception _ => exact .stuck rfl
  | address _ => exact .stuck rfl
  | closure _ => exact .stuck rfl
  | recursive_closure _ _ => exact .stuck rfl

def onBooleanRaw (operation : Bool → Core.Atom) :
    Core.Value Primitive → Core.Machine.PrimitiveResult Primitive
  | .atom (.boolean value) => .value (.atom (operation value))
  | _ => .stuck .primitive

def onBooleanPure (operation : Bool → Core.Atom) : Value Primitive → Machine.PrimitiveResult Primitive
  | .atom (.boolean value) => .value (.atom (operation value))
  | _ => .stuck .primitive

theorem onBoolean_compatible (operation : Bool → Core.Atom) :
    OperationCompatible (onBooleanRaw (Primitive := Primitive) operation) (onBooleanPure operation) := by
  intro world raw view represented
  cases represented with
  | atom atom =>
      cases atom with
      | boolean value => exact .value (.atom (operation value))
      | integer value => exact .stuck rfl
  | constructor _ => exact .stuck rfl
  | record _ => exact .stuck rfl
  | primitive _ => exact .stuck rfl
  | exception _ => exact .stuck rfl
  | address _ => exact .stuck rfl
  | closure _ => exact .stuck rfl
  | recursive_closure _ _ => exact .stuck rfl

/-- A usable small basis, without any claim to be the complete SML basis. -/
inductive BasicOperation where
  | identity
  | successor
  | isZero
  | negateBoolean
  deriving DecidableEq

def basicRaw : BasicOperation → Core.Value BasicOperation → Core.Machine.PrimitiveResult BasicOperation
  | .identity => identityRaw
  | .successor => onIntegerRaw fun value => .integer (value + 1)
  | .isZero => onIntegerRaw fun value => .boolean (decide (value = 0))
  | .negateBoolean => onBooleanRaw fun value => .boolean (!value)

def basicPure : BasicOperation → Value BasicOperation → Machine.PrimitiveResult BasicOperation
  | .identity => identityPure
  | .successor => onIntegerPure fun value => .integer (value + 1)
  | .isZero => onIntegerPure fun value => .boolean (decide (value = 0))
  | .negateBoolean => onBooleanPure fun value => .boolean (!value)

theorem basic_operation_compatible (operation : BasicOperation) :
    OperationCompatible (basicRaw operation) (basicPure operation) := by
  cases operation with
  | identity => exact identity_compatible
  | successor => exact onInteger_compatible _
  | isZero => exact onInteger_compatible _
  | negateBoolean => exact onBoolean_compatible _

private theorem integerRaw_origin (operation : Int → Core.Atom) (input : Core.Value Primitive) :
    (∃ atom, onIntegerRaw operation input = .value (.atom atom)) ∨
      onIntegerRaw operation input = .stuck .primitive := by
  cases input
  case atom atom =>
    cases atom with
    | boolean value => exact .inr rfl
    | integer value => exact .inl ⟨operation value, rfl⟩
  all_goals exact .inr rfl

private theorem integerPure_origin (operation : Int → Core.Atom) (input : Value Primitive) :
    (∃ atom, onIntegerPure operation input = .value (.atom atom)) ∨
      onIntegerPure operation input = .stuck .primitive := by
  cases input
  case atom atom =>
    cases atom with
    | boolean value => exact .inr rfl
    | integer value => exact .inl ⟨operation value, rfl⟩
  all_goals exact .inr rfl

private theorem booleanRaw_origin (operation : Bool → Core.Atom) (input : Core.Value Primitive) :
    (∃ atom, onBooleanRaw operation input = .value (.atom atom)) ∨
      onBooleanRaw operation input = .stuck .primitive := by
  cases input
  case atom atom =>
    cases atom with
    | boolean value => exact .inl ⟨operation value, rfl⟩
    | integer value => exact .inr rfl
  all_goals exact .inr rfl

private theorem booleanPure_origin (operation : Bool → Core.Atom) (input : Value Primitive) :
    (∃ atom, onBooleanPure operation input = .value (.atom atom)) ∨
      onBooleanPure operation input = .stuck .primitive := by
  cases input
  case atom atom =>
    cases atom with
    | boolean value => exact .inl ⟨operation value, rfl⟩
    | integer value => exact .inr rfl
  all_goals exact .inr rfl

/-- The basis introduces no new closure, suspension or primitive token.
Identity may return its existing input; scalar results are atoms or faults. -/
theorem basicRaw_output_origin (operation : BasicOperation) (input : Core.Value BasicOperation) :
    basicRaw operation input = .value input ∨
      (∃ atom, basicRaw operation input = .value (.atom atom)) ∨
      basicRaw operation input = .stuck .primitive := by
  cases operation with
  | identity => exact .inl rfl
  | successor => exact .inr (integerRaw_origin _ input)
  | isZero => exact .inr (integerRaw_origin _ input)
  | negateBoolean => exact .inr (booleanRaw_origin _ input)

theorem basicPure_output_origin (operation : BasicOperation) (input : Value BasicOperation) :
    basicPure operation input = .value input ∨
      (∃ atom, basicPure operation input = .value (.atom atom)) ∨
      basicPure operation input = .stuck .primitive := by
  cases operation with
  | identity => exact .inl rfl
  | successor => exact .inr (integerPure_origin _ input)
  | isZero => exact .inr (integerPure_origin _ input)
  | negateBoolean => exact .inr (booleanPure_origin _ input)

def basicRawParameters (matchTag bindTag : Nat) : Core.Machine.Parameters BasicOperation :=
  ⟨basicRaw, matchTag, bindTag⟩

def basicPureParameters (matchTag bindTag : Nat) : Machine.Parameters BasicOperation :=
  ⟨basicPure, matchTag, bindTag⟩

theorem basic_parameters_compatible (matchTag bindTag : Nat) :
    ParametersCompatible (fun _ => True)
      (basicRawParameters matchTag bindTag) (basicPureParameters matchTag bindTag) where
  primitive operation _ := basic_operation_compatible operation
  matchException := rfl
  bindException := rfl

end Suspensions.Pure.Compatibility

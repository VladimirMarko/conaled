import Applications.Suspensions.Pure.Compatibility
import Applications.Suspensions.Relocation

/-!
# Primitive compatibility and an address-observation discriminator

Identity, integer successor/zero test and Boolean negation use the public
compatibility law. Their mismatched inputs retain a primitive fault.

The diagnostic address-equality operation is equivariant under every injective
address renaming but has no counterpart satisfying the immutable-meaning law.
Two ordinary delays can have distinct addresses with the same pure meaning.
Aliased and distinct pairs then have one pure input but different raw Boolean
results. This is an excluded diagnostic operation, not a claim that Standard
ML permits equality on suspension types.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureCompatibility
open Suspensions
open Pure.Compatibility
open Pure.Representation

private def emptyWorld : World BasicOperation := fun _ => none

theorem basic_basis_compatible :
    ParametersCompatible (fun _ => True) (basicRawParameters 10 11) (basicPureParameters 10 11) :=
  basic_parameters_compatible 10 11

theorem successor_case :
    PrimitiveResultRep emptyWorld
      (basicRaw .successor (.atom (.integer 41)))
      (basicPure .successor (.atom (.integer 41))) ∧
    basicRaw .successor (.atom (.integer 41)) = .value (.atom (.integer 42)) ∧
    basicPure .successor (.atom (.integer 41)) = .value (.atom (.integer 42)) :=
  ⟨basic_operation_compatible .successor emptyWorld _ _ (.atom (.integer 41)), rfl, rfl⟩

theorem zero_case :
    PrimitiveResultRep emptyWorld
      (basicRaw .isZero (.atom (.integer 0)))
      (basicPure .isZero (.atom (.integer 0))) ∧
    basicRaw .isZero (.atom (.integer 0)) = .value (.atom (.boolean true)) ∧
    basicPure .isZero (.atom (.integer 0)) = .value (.atom (.boolean true)) :=
  ⟨basic_operation_compatible .isZero emptyWorld _ _ (.atom (.integer 0)), rfl, rfl⟩

theorem negation_case :
    PrimitiveResultRep emptyWorld
      (basicRaw .negateBoolean (.atom (.boolean true)))
      (basicPure .negateBoolean (.atom (.boolean true))) ∧
    basicRaw .negateBoolean (.atom (.boolean true)) = .value (.atom (.boolean false)) ∧
    basicPure .negateBoolean (.atom (.boolean true)) = .value (.atom (.boolean false)) :=
  ⟨basic_operation_compatible .negateBoolean emptyWorld _ _ (.atom (.boolean true)), rfl, rfl⟩

theorem wrong_scalar_case :
    PrimitiveResultRep emptyWorld
      (basicRaw .negateBoolean (.atom (.integer 3)))
      (basicPure .negateBoolean (.atom (.integer 3))) ∧
    basicRaw .negateBoolean (.atom (.integer 3)) = .stuck .primitive ∧
    basicPure .negateBoolean (.atom (.integer 3)) = .stuck .primitive :=
  ⟨basic_operation_compatible .negateBoolean emptyWorld _ _ (.atom (.integer 3)), rfl, rfl⟩

/-- A later admissibility policy only needs to include atoms and the input;
this uses the public output-origin law, without choosing that policy. -/
theorem basic_preserves_value_policy (policy : Pure.Value BasicOperation → Prop)
    (atoms : ∀ atom, policy (.atom atom)) (operation : BasicOperation)
    (input output : Pure.Value BasicOperation) (allowed : policy input)
    (returned : basicPure operation input = .value output) : policy output := by
  rcases basicPure_output_origin operation input with identity | ⟨atom, scalar⟩ | fault
  · have equal : output = input := Pure.Machine.PrimitiveResult.value.inj (returned.symm.trans identity)
    rw [equal]
    exact allowed
  · have equal : output = .atom atom := Pure.Machine.PrimitiveResult.value.inj
      (returned.symm.trans scalar)
    rw [equal]
    exact atoms atom
  · rw [returned] at fault
    cases fault

theorem wrong_force_operand_related :
    ResultRep emptyWorld (.stuck .expectedAddress) (.stuck .expectedSuspension) :=
  .stuck expectedAddress_related

/-- The fault-table entry is exercised at the actual forcing transitions. -/
theorem wrong_force_operand_connected :
    Core.Machine.step (basicRawParameters 10 11)
        (Core.Machine.startPattern Suspensions.empty [] (.suspended .wildcard)
          (.atom (.integer 5))) =
      .inl ⟨Suspensions.empty, .stuck .expectedAddress⟩ ∧
    Pure.Machine.step (basicPureParameters 10 11)
        (Pure.Machine.startPattern [] (.suspended .wildcard) (.atom (.integer 5))) =
      .inl (.stuck .expectedSuspension) ∧
    ResultRep emptyWorld (.stuck .expectedAddress) (.stuck .expectedSuspension) :=
  ⟨rfl, rfl, wrong_force_operand_related⟩

theorem missing_address_has_no_image (view : Pure.Machine.Fault) :
    ¬ FaultRep (.missingAddress 0) view := missingAddress_unrelated 0 view

theorem reference_kind_has_no_image (view : Pure.Machine.Fault) :
    ¬ FaultRep .expectedReferenceValue view := referenceValue_unrelated view

theorem raised_case :
    ResultRep emptyWorld (.raised (.exception 10 none)) (.raised (.exception 10 none)) :=
  .raised (.exception .none)

theorem matching_cases :
    ResultRep emptyWorld (.matched [(2, .atom (.integer 5))])
      (.matched [(2, .atom (.integer 5))]) ∧
    ResultRep emptyWorld .mismatch .mismatch :=
  ⟨.matched (.cons (.atom (.integer 5)) .nil), .mismatch⟩

theorem raised_is_not_a_value :
    ¬ ResultRep emptyWorld (.raised (.exception 10 none)) (.value (.exception 10 none)) := by
  intro represented
  cases represented

theorem mismatched_basis_tags_rejected :
    ¬ ParametersCompatible (fun _ => True)
      (basicRawParameters 10 11) (basicPureParameters 12 11) := by
  intro compatible
  have different : (10 : Nat) ≠ 12 := by decide
  exact different compatible.matchException

namespace Diagnostic

/-- The diagnostic takes a record with exactly two address-valued fields.
Their labels are irrelevant to this operation; the examples use distinct
labels 0 and 1. All other shapes give the primitive fault. -/
def pointerEqualRaw {Primitive : Type} :
    Core.Value Primitive → Core.Machine.PrimitiveResult Primitive
  | .record fields => match fields with
    | [first, second] => match first.2, second.2 with
      | .address left, .address right => .value (.atom (.boolean (decide (left = right))))
      | _, _ => .stuck .primitive
    | _ => .stuck .primitive
  | _ => .stuck .primitive

def pointerParameters : Core.Machine.Parameters Unit :=
  ⟨fun _ => pointerEqualRaw, 10, 11⟩

theorem pointer_equal_equivariant (rename : Nat → Nat) (injective : Function.Injective rename) :
    Core.Relocation.Equivariant pointerParameters rename := by
  intro operation input
  change pointerEqualRaw (Core.Renaming.value rename input) =
    Core.Relocation.primitiveResult rename (pointerEqualRaw input)
  cases input
  case record fields =>
    cases fields with
    | nil => simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]
    | cons first rest =>
        rcases first with ⟨firstLabel, firstValue⟩
        cases rest with
        | nil => simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]
        | cons second remaining =>
            rcases second with ⟨secondLabel, secondValue⟩
            cases remaining with
            | cons third tail =>
                rcases third with ⟨thirdLabel, thirdValue⟩
                simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]
            | nil =>
                cases firstValue
                case address left =>
                  cases secondValue
                  case address right =>
                    simp [pointerEqualRaw, Core.Relocation.primitiveResult, injective.eq_iff]
                  all_goals
                    simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]
                all_goals
                  simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]
  all_goals simp [pointerEqualRaw, Core.Relocation.primitiveResult, Core.Relocation.fault]

def meaning : Meaning Unit := ⟨.atom (.integer 7), [], none⟩

def world : World Unit := fun address =>
  if address = 0 ∨ address = 1 then some meaning else none

theorem world_zero : world 0 = some meaning := rfl

theorem world_one : world 1 = some meaning := rfl

private def firstDelay := Suspensions.delay (Suspensions.empty : Core.Machine.Memory Unit)
  meaning.body []

def memory : Core.Machine.Memory Unit := (Suspensions.delay firstDelay.1 meaning.body []).1

/-- The noninjective semantic world is compatible with the actual cells
created by two ordinary delay allocations; this is not an execution theorem. -/
theorem two_delays_same_meaning :
    memory.next = 2 ∧
    memory.memory 0 = some (.thunk meaning.body []) ∧
    memory.memory 1 = some (.thunk meaning.body []) ∧
    world 0 = some meaning ∧ world 1 = some meaning ∧
    EnvRep world [] meaning.captured :=
  ⟨rfl, rfl, rfl, world_zero, world_one, .nil⟩

theorem world_addresses_allocated (address : Nat) (foundMeaning : Meaning Unit)
    (found : world address = some foundMeaning) : ∃ cell, memory.memory address = some cell := by
  by_cases selected : address = 0 ∨ address = 1
  · rcases selected with zero | one
    · subst address
      exact ⟨_, rfl⟩
    · subst address
      exact ⟨_, rfl⟩
  · simp [world, selected] at found

def aliasedInput : Core.Value Unit := .record [(0, .address 0), (1, .address 0)]

def distinctInput : Core.Value Unit := .record [(0, .address 0), (1, .address 1)]

def pureInput : Pure.Value Unit := .record [(0, meaning.value), (1, meaning.value)]

theorem aliased_rep : ValueRep world aliasedInput pureInput :=
  .record (.cons (.address world_zero) (.cons (.address world_zero) .nil))

theorem distinct_rep : ValueRep world distinctInput pureInput :=
  .record (.cons (.address world_zero) (.cons (.address world_one) .nil))

theorem identity_preserves_alias_abstraction :
    PrimitiveResultRep world (identityRaw aliasedInput) (identityPure pureInput) ∧
    PrimitiveResultRep world (identityRaw distinctInput) (identityPure pureInput) :=
  ⟨identity_compatible world _ _ aliased_rep, identity_compatible world _ _ distinct_rep⟩

/-- One pure input cannot return both distinct Boolean atoms. Quantification
over every world therefore excludes physical address equality. -/
theorem pointer_equality_no_compatible_pure
    (operation : Pure.Value Unit → Pure.Machine.PrimitiveResult Unit) :
    ¬ OperationCompatible pointerEqualRaw operation := by
  intro compatible
  have aliased := compatible world aliasedInput pureInput aliased_rep
  have distinct := compatible world distinctInput pureInput distinct_rep
  have trueResult : operation pureInput = .value (.atom (.boolean true)) :=
    (primitiveResult_atom_iff (.boolean true) _).mp aliased
  have falseResult : operation pureInput = .value (.atom (.boolean false)) :=
    (primitiveResult_atom_iff (.boolean false) _).mp distinct
  have impossible := trueResult.symm.trans falseResult
  cases impossible

theorem pointer_parameters_not_compatible (parameters : Pure.Machine.Parameters Unit) :
    ¬ ParametersCompatible (fun _ => True) pointerParameters parameters := by
  intro compatible
  exact pointer_equality_no_compatible_pure (parameters.primitive ())
    (compatible.primitive () trivial)

end Diagnostic
end Examples.SuspensionPureCompatibility

import Applications.Suspensions.Pure.Domain
import Examples.SuspensionPureValues

/-!
# Hereditary domains admit recursive meanings and reject hidden effects

The existing mutual function/suspension and returned-closure examples retain
their exact finite descriptors and lookups. The domain imposes no termination
or typing premise: an atom applied as a function is admitted and faults in
both machines. Conversely, representation compatibility alone permits an
operation to return effect-bearing code; the hereditary output law rejects it.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureDomain
open Suspensions Suspensions.Pure Suspensions.Pure.Domain
open Examples.SuspensionPureValues

private def noOperations : Unit → Prop := fun _ => False

private theorem mutual_clauses_code : ClausesCodeAllowed noOperations mutualClauses := by
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨.record .nil, (CodeAllowed.variable 2).force, ClausesCodeAllowed.nil⟩

private theorem mutual_body_code : CodeAllowed noOperations mutualSuspensionBody :=
  (CodeAllowed.apply_iff _ _).mpr
    ⟨CodeAllowed.variable 1, (CodeAllowed.record_iff []).mpr NamedCodeAllowed.nil⟩

private theorem mutual_definitions_code :
    NamedCodeAllowed noOperations (Rhs.toBindings mutualBindings) := by
  apply (NamedCodeAllowed.cons_iff _ _ _).mpr
  refine ⟨(CodeAllowed.function_iff _).mpr mutual_clauses_code, ?_⟩
  apply (NamedCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨(CodeAllowed.delay_iff _).mpr mutual_body_code, NamedCodeAllowed.nil⟩

theorem mutual_source_code : CodeAllowed noOperations
    (.recursive (Rhs.toBindings mutualBindings) (Core.force (.variable 2))) :=
  (CodeAllowed.recursive_iff _ _).mpr
    ⟨mutual_definitions_code, (CodeAllowed.variable 2).force,
      Rhs.toBindings_permitted mutualBindings, mutual_source_distinct⟩

private theorem mutual_outer_allowed : EnvAllowed noOperations mutualOuter :=
  .cons (.atom (.integer 99)) (.cons (.atom (.boolean true)) .nil)

/-- Permitted source syntax produces the exact expected descriptor without
assuming a decoder result or any body evaluation. -/
theorem mutual_source_decoded :
    ∃ decoded, Rhs.ofBindings (Rhs.toBindings mutualBindings) = .ok decoded ∧
      Rhs.toBindings decoded = Rhs.toBindings mutualBindings ∧ decoded = mutualBindings := by
  obtain ⟨decoded, found, source⟩ := decode_permitted mutual_source_permitted
  exact ⟨decoded, found, source,
    Except.ok.inj (found.symm.trans (Rhs.ofBindings_toBindings mutualBindings))⟩

theorem mutual_group_allowed : GroupAllowed noOperations mutualGroup := by
  obtain ⟨decoded, found, _, same⟩ := mutual_source_decoded
  subst decoded
  exact GroupAllowed.of_decoded mutual_definitions_code mutual_source_distinct
    found mutual_outer_allowed

theorem mutual_environment_allowed : EnvAllowed noOperations mutualEnvironment :=
  bodyEnvironment_allowed mutual_outer_allowed (.some mutual_group_allowed)

/-- The original cyclic source dependency is admitted. Both actual member
lookups pass through the generic environment-preservation and lookup laws. -/
theorem mutual_cycle_allowed :
    ValueAllowed noOperations (.suspension mutualSuspensionBody mutualOuter (some mutualGroup)) ∧
    ValueAllowed noOperations (.closure mutualClauses mutualOuter (some mutualGroup)) ∧
    (∃ captured recursive,
      Env.lookup mutualEnvironment 2 =
        some (.suspension mutualSuspensionBody captured recursive) ∧
      Env.lookup (bodyEnvironment captured recursive) 1 =
        some (.closure mutualClauses captured recursive) ∧
      bodyEnvironment captured recursive = mutualEnvironment) :=
  ⟨mutual_environment_allowed.lookup mutual_suspension_lookup,
    mutual_environment_allowed.lookup mutual_function_lookup, mutual_round_trip⟩

private theorem cached_clauses_code : ClausesCodeAllowed noOperations cachedClauses := by
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  refine ⟨.variable 2, ?_, ClausesCodeAllowed.nil⟩
  apply (CodeAllowed.branch_iff _ _ _).mpr
  exact ⟨CodeAllowed.variable 2, CodeAllowed.atom (.integer 7),
    (CodeAllowed.apply_iff _ _).mpr
      ⟨(CodeAllowed.variable 1).force, CodeAllowed.atom (.boolean true)⟩⟩

private theorem cached_definitions_code :
    NamedCodeAllowed noOperations [(1, .delay cachedCode)] := by
  apply (NamedCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨(CodeAllowed.delay_iff _).mpr ((CodeAllowed.function_iff _).mpr cached_clauses_code),
    NamedCodeAllowed.nil⟩

private theorem cached_outer_allowed : EnvAllowed noOperations cachedOuter :=
  .cons (.atom (.integer 41)) .nil

theorem cached_group_allowed : GroupAllowed noOperations cachedGroup :=
  GroupAllowed.of_decoded cached_definitions_code (by decide) rfl cached_outer_allowed

theorem returned_closure_allowed : ValueAllowed noOperations cachedClosure :=
  .closure cached_clauses_code
    (bodyEnvironment_allowed cached_outer_allowed (.some cached_group_allowed)) .none

/-- Formation really returns the admitted closure, whose capture still finds
the same recursive suspension. No body of that suspension is evaluated here. -/
theorem returned_closure_connected (parameters : Machine.Parameters Unit) :
    ValueAllowed noOperations cachedClosure ∧
    Progress.Evaluates (Machine.step parameters) (Machine.start cachedBodyEnvironment cachedCode)
      (.value cachedClosure) 2 ∧
    Env.lookup cachedBodyEnvironment 1 = some (.suspension cachedCode cachedOuter (some cachedGroup)) :=
  ⟨returned_closure_allowed, .next rfl (.done rfl), cached_suspension_lookup⟩

private def badApplication : Core.Expr Unit :=
  .apply (.atom (.integer 3)) (.atom (.integer 4))

/-- The domain is not a typing theorem. This pure application is admitted and
retains the independently expected function fault in both actual machines. -/
theorem admitted_application_faults (raw : Core.Machine.Parameters Unit)
    (pure : Machine.Parameters Unit) :
    CodeAllowed noOperations badApplication ∧
    Progress.Evaluates (Core.Machine.step raw)
      (Core.Machine.start Suspensions.empty [] badApplication)
      ⟨Suspensions.empty, .stuck .expectedFunction⟩ 5 ∧
    Progress.Evaluates (Machine.step pure) (Machine.start [] badApplication)
      (.stuck .expectedFunction) 5 ∧
    Compatibility.ResultRep (fun _ => none)
      (Primitive := Unit) (.stuck .expectedFunction) (.stuck .expectedFunction) :=
  ⟨(CodeAllowed.apply_iff _ _).mpr
      ⟨CodeAllowed.atom (.integer 3), CodeAllowed.atom (.integer 4)⟩,
    .next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))),
    .next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))), .stuck rfl⟩

/-- A forbidden nested RHS is rejected even when delayed by an outer body. -/
theorem nested_invalid_recursive_rhs_rejected :
    ¬ CodeAllowed noOperations
      (.delay (.recursive [(3, .atom (.integer 0))] (.variable 3))) := by
  intro allowed
  have declaration := (CodeAllowed.delay_iff _).mp allowed
  have permitted := ((CodeAllowed.recursive_iff _ _).mp declaration).2.2.1
  have shape := (Core.Recursive.permitted_cons 3 (.atom (.integer 0)) []).mp permitted
  cases shape.1

theorem duplicate_descriptor_rejected :
    ¬ GroupAllowed noOperations
      (.mk [(5, .delay (.atom (.integer 7))), (5, .function [])] []) := by
  intro allowed
  have different := allowed.distinct
  have repeated : ¬([5, 5] : List Nat).Nodup := by decide
  exact repeated different

/-- Token selection is hereditary through data, not just closure bodies. -/
theorem nested_unselected_token_rejected :
    ¬ ValueAllowed noOperations (.record [(0, .primitive ())]) := by
  intro allowed
  have environment := (ValueAllowed.record_iff _).mp allowed
  have token := environment.lookup (name := 0) (by rfl)
  exact (ValueAllowed.primitive_iff ()).mp token

theorem scalar_basis_preserves_domain (selected : Compatibility.BasicOperation → Prop) :
    ParametersPreserve selected (Compatibility.basicPureParameters 10 11) :=
  basic_parameters_preserve selected 10 11

theorem successor_domain_connected :
    PrimitiveResultAllowed (fun _ => True)
      (Compatibility.basicPure .successor (.atom (.integer 41))) ∧
    Compatibility.basicPure .successor (.atom (.integer 41)) = .value (.atom (.integer 42)) :=
  ⟨basic_operation_preserves (fun _ => True) .successor _ (.atom (.integer 41)), rfl⟩

namespace Diagnostic

private def allOperations : Unit → Prop := fun _ => True

private def badClauses : List (Core.Pattern × Core.Expr Unit) :=
  [(.wildcard, .reference (.atom (.integer 0)))]

def badRaw (_ : Core.Value Unit) : Core.Machine.PrimitiveResult Unit :=
  .value (.closure badClauses [] [])

def badPure (_ : Value Unit) : Machine.PrimitiveResult Unit :=
  .value (.closure badClauses [] none)

theorem bad_output_compatible : Compatibility.OperationCompatible badRaw badPure :=
  fun _ _ _ _ => .value (.closure .nil)

theorem bad_output_rejected : ¬ ValueAllowed allOperations (.closure badClauses [] none) := by
  intro allowed
  have clauses := ((ValueAllowed.closure_iff _ _ _).mp allowed).1
  have body := ((ClausesCodeAllowed.cons_iff _ _ []).mp clauses).2.1
  exact reference_excluded allOperations _ body.effects

theorem bad_operation_not_preserving : ¬ OperationPreserves allOperations badPure := by
  intro preserves
  have result := preserves (.atom (.integer 0)) (.atom (.integer 0))
  exact bad_output_rejected ((PrimitiveResultAllowed.value_iff _).mp result)

/-- The two laws discharge different obligations: a related output may still
contain effect-bearing source code. -/
theorem compatibility_does_not_supply_domain :
    Compatibility.OperationCompatible badRaw badPure ∧ ¬ OperationPreserves allOperations badPure :=
  ⟨bad_output_compatible, bad_operation_not_preserving⟩

end Diagnostic
end Examples.SuspensionPureDomain

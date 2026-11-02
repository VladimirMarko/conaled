import Applications.Suspensions.Static
import Applications.Suspensions.Names
import Examples.SuspensionMachine

/-!
# Source-sensitive static suspension clients

The source calculation predicts that the 1990 imperative-variable rule plus
Appendix A's non-expansive suspension rule generalizes the cached reference.
This file checks that derivation for the very same runtime expression used by
`Examples.SuspensionMachine.cached_reference_integer`; it does not assume a
global preservation theorem for the published extension.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionStatic
open Suspensions Suspensions.Core Suspensions.Static

def applicative : TyVar := ⟨0, false, false⟩
def imperative : TyVar := ⟨0, false, true⟩

def identity {Primitive : Type} : Expr Primitive :=
  .function [(.variable 2, .variable 2)]

def delayedReference {Primitive : Type} : Expr Primitive :=
  .delay (.reference identity)

def referenceType (t : Ty) : Ty := .suspension (.reference (.arrow t t))

/-- Expansiveness alone does not prevent generalization in the 1990 rules. -/
theorem expansive_applicative_generalizes :
    (generalize ∅ (Expr.reference (identity : Expr Empty))
      (.reference (.arrow (.variable applicative) (.variable applicative)))).quantified =
        {applicative} := by
  ext a
  simp [generalize, nonExpansive, Ty.vars, applicative]

/-- The same expansive reference allocation with an imperative variable does
not generalize that variable. -/
theorem expansive_imperative_is_monomorphic :
    (generalize ∅ (Expr.reference (identity : Expr Empty))
      (.reference (.arrow (.variable imperative) (.variable imperative)))).quantified = ∅ := by
  ext a
  simp [generalize, nonExpansive, Ty.vars, imperative]

/-- Appendix A's suspension rule changes exactly that decision. -/
theorem delay_generalizes_imperative :
    (generalize ∅ (delayedReference : Expr Empty)
      (referenceType (.variable imperative))).quantified = {imperative} := by
  ext a
  simp [generalize, delayedReference, nonExpansive, referenceType, Ty.vars]

/-- Equality belongs to the reference identity, never to the suspension itself. -/
theorem reference_to_suspension_equality (names : Nat → Bool) :
    Ty.AdmitsEquality names (.reference (.suspension (.arrow .integer .integer))) ∧
      ¬ Ty.AdmitsEquality names (.suspension (.arrow .integer .integer)) := by
  exact ⟨.reference _, Ty.not_suspension_equality names _⟩

/-- A closed function type satisfies the source imperative restriction. -/
theorem closed_function_is_imperative : Ty.Imperative (.arrow .boolean .boolean) := by
  exact (Ty.imperative_arrow _ _).mpr ⟨Ty.imperative_boolean, Ty.imperative_boolean⟩

/-- Looking up an exception name is a hygiene dependency even without ordinary
variable occurrences in its pattern. -/
theorem exception_pattern_name_is_recorded (name : Nat) :
    name ∈ Names.patternNames (.exception name none) := by
  simp [Names.patternNames, Names.optionalPatternNames]

def cachedScheme : Scheme := ⟨{imperative}, referenceType (.variable imperative)⟩

theorem generalize_cached {Primitive : Type} :
    generalize ∅ (delayedReference : Expr Primitive) (referenceType (.variable imperative)) =
      cachedScheme := by
  simp [generalize, delayedReference, nonExpansive, referenceType, Ty.vars, cachedScheme]

theorem cachedScheme_instance (names : Nat → Bool) (replacement : Ty)
    (permitted : replacement.Imperative) :
    cachedScheme.Instantiates names (referenceType replacement) := by
  have instantiated := Scheme.instantiate_single names imperative
    (referenceType (.variable imperative)) replacement (by simp [imperative]) (fun _ => permitted)
  simpa [cachedScheme, referenceType, Ty.substitute] using instantiated

theorem cachedScheme_integer (names : Nat → Bool) :
    cachedScheme.Instantiates names (referenceType .integer) :=
  cachedScheme_instance names .integer Ty.imperative_integer

theorem cachedScheme_boolean (names : Nat → Bool) :
    cachedScheme.Instantiates names (referenceType .boolean) :=
  cachedScheme_instance names .boolean Ty.imperative_boolean

theorem identity_type {Primitive : Type} (signature : Signature Primitive)
    (context : Context) (t : Ty) (allowed : context.VariableAllowed 2) :
    HasType signature context identity (.arrow t t) := by
  apply HasType.function (by simp [identity])
  apply ClausesHaveType.cons (bindings := Finmap.singleton 2 (.variable (.mono t)))
  · exact .variable allowed
  · exact .variable (context.variable_lookup 2 t) (Scheme.mono_instantiates _ _)
  · exact .nil

theorem delayed_reference_type {Primitive : Type} (signature : Signature Primitive) :
    HasType signature Context.empty delayedReference (referenceType (.variable imperative)) := by
  apply HasType.delay
  apply HasType.reference
  · simp [Ty.imperative_arrow, Ty.imperative_variable, imperative]
  · exact identity_type signature Context.empty (.variable imperative)
      (Context.variableAllowed_empty 2)

def cachedContext : Context :=
  Context.empty.extend (Finmap.singleton 1 (.variable cachedScheme))

theorem cachedContext_lookup :
    cachedContext.values.lookup 1 = some (.variable cachedScheme) := by
  simp [cachedContext, Context.extend, Context.empty]

theorem cachedContext_force_name : cachedContext.VariableAllowed 0 := by
  simp [Context.VariableAllowed, cachedContext, Context.extend, Context.empty,
    Bindings.lookup_singleton]

theorem constant_integer_type {Primitive : Type} (signature : Signature Primitive)
    (context : Context) :
    HasType signature context (.function [(.wildcard, .atom (.integer 0))])
      (.arrow .integer .integer) := by
  apply HasType.function (by simp)
  apply ClausesHaveType.cons (bindings := ∅)
  · exact .wildcard
  · exact .atom _
  · exact .nil

theorem cached_assignment_type {Primitive : Type} (signature : Signature Primitive) :
    HasType signature cachedContext
      (.assign (force (.variable 1)) (.function [(.wildcard, .atom (.integer 0))])) .unit := by
  apply HasType.assign (t := .arrow .integer .integer)
  · apply force_type signature cachedContext_force_name
    exact .variable cachedContext_lookup (cachedScheme_integer _)
  · exact constant_integer_type signature cachedContext

theorem cached_read_boolean_type {Primitive : Type} (signature : Signature Primitive) :
    HasType signature cachedContext
      (.apply (.read (force (.variable 1))) (.atom (.boolean true))) .boolean := by
  apply HasType.apply (input := .boolean)
  · apply HasType.read
    apply force_type signature cachedContext_force_name
    exact .variable cachedContext_lookup (cachedScheme_boolean _)
  · exact .atom _

/-- The source-derived static half of SUSP-STAT-001 uses the exact public runtime
term, including both uses of the one generalized suspension binding. -/
theorem cachedReference_boolean {Primitive : Type} (signature : Signature Primitive) :
    HasType signature Context.empty
      (Examples.SuspensionMachine.cachedReference : Expr Primitive) .boolean := by
  unfold Examples.SuspensionMachine.cachedReference
  apply HasType.bind (input := referenceType (.variable imperative))
    (bindings := Finmap.singleton 1 (.variable (.mono (referenceType (.variable imperative)))))
  · exact delayed_reference_type signature
  · exact .variable (Context.variableAllowed_empty 1)
  · have closed : closeBindings Context.empty (delayedReference : Expr Primitive)
        (Finmap.singleton 1 (.variable (.mono (referenceType (.variable imperative))))) =
          Finmap.singleton 1 (.variable cachedScheme) := by
      rw [closeBindings_singleton, Context.freeVars_empty, generalize_cached]
    change HasType signature
      (Context.empty.extend (closeBindings Context.empty (delayedReference : Expr Primitive)
        (Finmap.singleton 1 (.variable (.mono (referenceType (.variable imperative))))))) _ .boolean
    rw [closed]
    change HasType signature cachedContext _ .boolean
    apply HasType.bind (input := .unit) (bindings := ∅)
    · exact cached_assignment_type signature
    · exact .wildcard
    · simpa only [closeBindings_empty, Context.extend_empty] using cached_read_boolean_type signature

def machineSignature : Signature Examples.SuspensionMachine.Primitive where
  equalityNames := fun _ => false
  primitives := fun _ => .mono (.arrow .integer .integer)
  constructors := fun _ => none

/-- A concrete, scoped preservation counterexample for the published extension:
the checked Boolean-typed expression actually returns the integer atom0.
This does not assert a complete Standard ML type system or assume its safety. -/
theorem cached_reference_type_mismatch :
    HasType machineSignature Context.empty Examples.SuspensionMachine.cachedReference .boolean ∧
    ∃ answer events steps,
      Progress.Evaluates (Core.Machine.tracedStep Examples.SuspensionMachine.parameters)
        (Core.Machine.start Examples.SuspensionMachine.initial []
          Examples.SuspensionMachine.cachedReference, []) (answer, events) steps ∧
      answer.result = .value (.atom (.integer 0)) ∧ atomType (.integer 0) ≠ .boolean := by
  refine ⟨cachedReference_boolean machineSignature, ?_⟩
  obtain ⟨answer, events, steps, evaluated, returned, _⟩ :=
    Examples.SuspensionMachine.cached_reference_integer
  refine ⟨answer, events, steps, evaluated, returned, ?_⟩
  intro impossible
  cases impossible

def forceScheme : Scheme :=
  ⟨{applicative}, .arrow (.suspension (.variable applicative)) (.variable applicative)⟩

/-- Unlike ref, the derived force scheme has no imperative or equality restriction. -/
theorem forceScheme_unrestricted (names : Nat → Bool) (t : Ty) :
    forceScheme.Instantiates names (.arrow (.suspension t) t) := by
  have instantiated := Scheme.instantiate_single names applicative
    (.arrow (.suspension (.variable applicative)) (.variable applicative)) t
      (by simp [applicative]) (by simp [applicative])
  simpa [forceScheme, Ty.substitute] using instantiated

theorem force_generalization :
    generalize ∅
      (Expr.function [(.suspended (.variable 0), .variable 0)] : Expr Empty)
      (.arrow (.suspension (.variable applicative)) (.variable applicative)) = forceScheme := by
  simp [generalize, nonExpansive, Ty.vars, forceScheme]

def emptySignature : Signature Empty where
  equalityNames := fun _ => false
  primitives := fun operation => nomatch operation
  constructors := fun _ => none

def lazyContext (a : TyVar) : Context := ⟨{a}, ∅⟩

def lazyClauses : List (Pattern × Expr Empty) :=
  [(.variable 1, .delay (.variable 1))]

theorem lazyClauses_type (a : TyVar) :
    ClausesHaveType emptySignature (lazyContext a) lazyClauses
      (.variable a) (.suspension (.variable a)) := by
  apply ClausesHaveType.cons (bindings := Finmap.singleton 1 (.variable (.mono (.variable a))))
  · apply PatternHasType.variable
    simp [Context.VariableAllowed, lazyContext]
  · exact .delay (.variable ((lazyContext a).variable_lookup 1 (.variable a))
      (Scheme.mono_instantiates _ _))
  · exact .nil

/-- The fresh-name theorem works at an open input type with either combination
of the source variable attributes, preserving its ambient scope. -/
theorem lazyFunction_with_open_input (a : TyVar) :
    HasType emptySignature (lazyContext a)
      (lazyFunction (Names.fresh (lazyContext a).values.keys lazyClauses) lazyClauses)
      (.arrow (.variable a) (.suspension (.variable a))) := by
  apply lazyFunction_fresh_type emptySignature (lazyClauses_type a)
  · simp [lazyClauses]
  · simp [Ty.vars, lazyContext]
  · simp [Context.VariableAllowed, lazyContext]

/-- Adding an otherwise unused parameter can change Clos when its type variable
was not already in ambient scope. This explains the transport theorem's premise. -/
theorem unscoped_parameter_changes_closure :
    (generalize Context.empty.freeVars (identity : Expr Empty)
      (.arrow (.variable applicative) (.variable applicative))).quantified = {applicative} ∧
    (generalize (Context.empty.bindVariable 9 (.variable applicative)).freeVars
      (identity : Expr Empty) (.arrow (.variable applicative) (.variable applicative))).quantified = ∅ := by
  constructor
  · simp [generalize, identity, nonExpansive, Ty.vars]
  · simp [generalize, identity, nonExpansive, Context.freeVars, Context.bindVariable,
      Context.extend, Context.empty, Binding.freeVars, Ty.vars]

end Examples.SuspensionStatic

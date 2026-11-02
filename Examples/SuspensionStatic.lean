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

end Examples.SuspensionStatic

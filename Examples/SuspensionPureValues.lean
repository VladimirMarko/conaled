import Applications.Suspensions.Pure.Value

/-!
# Finite recursive suspension meanings

The first case represents `f () = force s; s = $(f ())`. Both directions of
the dependency use the same finite descriptor and recover the same body
environment. This is a representation fact, not a termination assertion.

The second case represents the closure obtained by evaluating the body of
`s = $(fn b => if b then 7 else (force s) true)`. Its capture includes the
same suspension meaning. No heap acyclicity assumption or cyclic Lean value
is used. Actual execution and the later result 7 are separate obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureValues
open Suspensions
open Pure

private def NoOperations : Unit → Prop := fun _ => False

def mutualClauses : List (Core.Pattern × Core.Expr Unit) :=
  [(.record [], Core.force (.variable 2))]

def mutualSuspensionBody : Core.Expr Unit := .apply (.variable 1) (.record [])

def mutualBindings : List (Nat × Rhs Unit) :=
  [(1, .function mutualClauses), (2, .delay mutualSuspensionBody)]

/-- The group must override the older binding of identifier 1. -/
def mutualOuter : Pure.Env Unit :=
  [(1, .atom (.integer 99)), (9, .atom (.boolean true))]

def mutualGroup : Group Unit := .mk mutualBindings mutualOuter

def mutualEnvironment : Pure.Env Unit := bodyEnvironment mutualOuter (some mutualGroup)

theorem mutual_source_roundtrip :
    Rhs.ofBindings [(1, .function mutualClauses), (2, .delay mutualSuspensionBody)] =
      .ok mutualBindings :=
  Rhs.ofBindings_toBindings mutualBindings

theorem mutual_source_permitted :
    List.Forall (fun binding => Core.RecursiveRhs binding.2) (Rhs.toBindings mutualBindings) :=
  Rhs.toBindings_permitted mutualBindings

theorem mutual_source_distinct : ((Rhs.toBindings mutualBindings).map Prod.fst).Nodup := by
  rw [Rhs.toBindings_names]
  decide

theorem mutual_source_allowed : ExpressionAllowed NoOperations
    (.recursive (Rhs.toBindings mutualBindings) (Core.force (.variable 2))) := by
  apply ExpressionAllowed.recursive
  · exact .cons (.function (.cons (.record .nil) (force_allowed (.variable 2)) .nil))
      (.cons (.delay (.apply (.variable 1) (.record .nil))) .nil)
  · exact force_allowed (.variable 2)

theorem mutual_function_lookup :
    Pure.Env.lookup mutualEnvironment 1 =
      some (.closure mutualClauses mutualOuter (some mutualGroup)) :=
  bodyEnvironment_lookup (Group.lookup_function (by rfl))

theorem mutual_suspension_lookup :
    Pure.Env.lookup mutualEnvironment 2 =
      some (.suspension mutualSuspensionBody mutualOuter (some mutualGroup)) :=
  bodyEnvironment_lookup (Group.lookup_delay (by rfl))

theorem mutual_outer_retained :
    Pure.Env.lookup mutualEnvironment 9 = some (.atom (.boolean true)) := by
  rw [mutualEnvironment, bodyEnvironment_outer (group := mutualGroup) (name := 9) (by rfl)]
  rfl

/-- Entering s finds f with the same descriptor; entering f would recover
exactly the same environment, rather than a larger recursive value. -/
theorem mutual_round_trip :
    ∃ captured recursive,
      Pure.Env.lookup mutualEnvironment 2 =
        some (.suspension mutualSuspensionBody captured recursive) ∧
      Pure.Env.lookup (bodyEnvironment captured recursive) 1 =
        some (.closure mutualClauses captured recursive) ∧
      bodyEnvironment captured recursive = mutualEnvironment :=
  ⟨mutualOuter, some mutualGroup, mutual_suspension_lookup, mutual_function_lookup, rfl⟩

def cachedClauses : List (Core.Pattern × Core.Expr Unit) :=
  [(.variable 2,
    .branch (.variable 2) (.atom (.integer 7))
      (.apply (Core.force (.variable 1)) (.atom (.boolean true))))]

def cachedCode : Core.Expr Unit := .function cachedClauses

def cachedOuter : Pure.Env Unit := [(9, .atom (.integer 41))]

def cachedGroup : Group Unit := .mk [(1, .delay cachedCode)] cachedOuter

def cachedBodyEnvironment : Pure.Env Unit := bodyEnvironment cachedOuter (some cachedGroup)

/-- Ordinary function formation captures the already closed environment.
The closure itself has no additional recursive descriptor. -/
def cachedClosure : Pure.Value Unit := .closure cachedClauses cachedBodyEnvironment none

theorem cached_source_allowed : ExpressionAllowed NoOperations
    (.recursive [(1, .delay cachedCode)]
      (.apply (Core.force (.variable 1)) (.atom (.boolean false)))) := by
  apply ExpressionAllowed.recursive
  · exact .cons (.delay (.function (.cons (.variable 2)
      (.branch (.variable 2) (.atom (.integer 7))
        (.apply (force_allowed (.variable 1)) (.atom (.boolean true)))) .nil))) .nil
  · exact .apply (force_allowed (.variable 1)) (.atom (.boolean false))

theorem cached_suspension_lookup :
    Pure.Env.lookup cachedBodyEnvironment 1 =
      some (.suspension cachedCode cachedOuter (some cachedGroup)) :=
  bodyEnvironment_lookup (Group.lookup_delay (by rfl))

/-- The cached closure may refer back to the suspension whose body created
it. Following that value's descriptor recovers the exact original capture. -/
theorem cached_closure_backedge :
    ∃ captured recursive,
      cachedClosure = .closure cachedClauses captured recursive ∧
      Pure.Env.lookup (bodyEnvironment captured recursive) 1 =
        some (.suspension cachedCode cachedOuter (some cachedGroup)) ∧
      bodyEnvironment cachedOuter (some cachedGroup) = captured :=
  ⟨cachedBodyEnvironment, none, rfl, cached_suspension_lookup, rfl⟩

theorem recursive_pattern_effect_excluded :
    ¬ ExpressionAllowed NoOperations
      (.function [(.reference .wildcard, .atom (.integer 0))]) := by
  intro allowed
  cases allowed with
  | function clauses =>
      cases clauses with
      | cons matching _ _ => exact reference_pattern_excluded _ matching

/-- Fixed exceptions are retained; this does not generate an exception name. -/
theorem fixed_exception_allowed : ExpressionAllowed NoOperations
    (.handle (.raise (.variable 7)) [(.exception 7 none, .atom (.integer 0))]) :=
  .handle (.raise (.variable 7)) (.cons (.exception 7) (.atom (.integer 0)) .nil)

/-- Absence of effects does not turn an unsupported recursive RHS into a
source-valid declaration. The separate RHS decoder rejects it. -/
theorem invalid_recursive_rhs_effect_free : ExpressionAllowed NoOperations
    (.recursive [(3, .atom (.integer 0))] (.variable 3)) :=
  .recursive (.cons (.atom (.integer 0)) .nil) (.variable 3)

theorem invalid_recursive_rhs_rejected :
    Rhs.ofBindings (Primitive := Unit) [(3, .atom (.integer 0))] = .error 3 := rfl

end Examples.SuspensionPureValues

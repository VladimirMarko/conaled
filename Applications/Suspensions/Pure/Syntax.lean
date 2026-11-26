import Applications.Suspensions.Syntax

/-!
# The effect boundary for pure suspension programs

These predicates use the existing source-core syntax. They exclude reference
expressions, reference patterns and generative exception declarations, while
retaining functions, data, recursive groups, suspensions and fixed exceptions.
The primitive predicate selects operations; it does not assert any semantic
law about their implementations.

Effect restrictions and source well-formedness are separate. These predicates
do not require distinct binders, nonempty matches, permitted recursive RHS
shapes, typing, hygiene, termination or absence of recursive forcing.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure

mutual
  inductive PatternAllowed : Core.Pattern → Prop
    | wildcard : PatternAllowed .wildcard
    | variable (name : Nat) : PatternAllowed (.variable name)
    | atom (value : Core.Atom) : PatternAllowed (.atom value)
    | constructor (tag : Nat) : PatternAllowed (.constructor tag none)
    | constructor_argument {tag : Nat} {inner : Core.Pattern}
        (argument : PatternAllowed inner) :
        PatternAllowed (.constructor tag (some inner))
    | exception (name : Nat) : PatternAllowed (.exception name none)
    | exception_argument {name : Nat} {inner : Core.Pattern}
        (argument : PatternAllowed inner) :
        PatternAllowed (.exception name (some inner))
    | record {fields : List (Nat × Core.Pattern)}
        (allowed : PatternFieldsAllowed fields) : PatternAllowed (.record fields)
    | suspended {inner : Core.Pattern} (allowed : PatternAllowed inner) :
        PatternAllowed (.suspended inner)
    | layered {name : Nat} {inner : Core.Pattern} (allowed : PatternAllowed inner) :
        PatternAllowed (.layered name inner)

  inductive PatternFieldsAllowed : List (Nat × Core.Pattern) → Prop
    | nil : PatternFieldsAllowed []
    | cons {label : Nat} {pattern : Core.Pattern} {rest : List (Nat × Core.Pattern)}
        (head : PatternAllowed pattern) (tail : PatternFieldsAllowed rest) :
        PatternFieldsAllowed ((label, pattern) :: rest)
end

mutual
  inductive ExpressionAllowed {Primitive : Type} (operations : Primitive → Prop) :
      Core.Expr Primitive → Prop
    | atom (value : Core.Atom) : ExpressionAllowed operations (.atom value)
    | variable (name : Nat) : ExpressionAllowed operations (.variable name)
    | primitive {operation : Primitive} (allowed : operations operation) :
        ExpressionAllowed operations (.primitive operation)
    | constructor (tag : Nat) : ExpressionAllowed operations (.constructor tag none)
    | constructor_argument {tag : Nat} {body : Core.Expr Primitive}
        (allowed : ExpressionAllowed operations body) :
        ExpressionAllowed operations (.constructor tag (some body))
    | record {fields : List (Nat × Core.Expr Primitive)}
        (allowed : NamedExpressionsAllowed operations fields) :
        ExpressionAllowed operations (.record fields)
    | function {clauses : List (Core.Pattern × Core.Expr Primitive)}
        (allowed : ClausesAllowed operations clauses) :
        ExpressionAllowed operations (.function clauses)
    | apply {function argument : Core.Expr Primitive}
        (operator : ExpressionAllowed operations function)
        (operand : ExpressionAllowed operations argument) :
        ExpressionAllowed operations (.apply function argument)
    | bind {pattern : Core.Pattern} {value body : Core.Expr Primitive}
        (matching : PatternAllowed pattern)
        (right : ExpressionAllowed operations value)
        (continuation : ExpressionAllowed operations body) :
        ExpressionAllowed operations (.bind pattern value body)
    | recursive {bindings : List (Nat × Core.Expr Primitive)} {body : Core.Expr Primitive}
        (definitions : NamedExpressionsAllowed operations bindings)
        (continuation : ExpressionAllowed operations body) :
        ExpressionAllowed operations (.recursive bindings body)
    | branch {condition yes no : Core.Expr Primitive}
        (test : ExpressionAllowed operations condition)
        (positive : ExpressionAllowed operations yes)
        (negative : ExpressionAllowed operations no) :
        ExpressionAllowed operations (.branch condition yes no)
    | delay {body : Core.Expr Primitive} (allowed : ExpressionAllowed operations body) :
        ExpressionAllowed operations (.delay body)
    | raise {packet : Core.Expr Primitive} (allowed : ExpressionAllowed operations packet) :
        ExpressionAllowed operations (.raise packet)
    | handle {body : Core.Expr Primitive} {clauses : List (Core.Pattern × Core.Expr Primitive)}
        (bodyAllowed : ExpressionAllowed operations body)
        (handlers : ClausesAllowed operations clauses) :
        ExpressionAllowed operations (.handle body clauses)

  inductive NamedExpressionsAllowed {Primitive : Type} (operations : Primitive → Prop) :
      List (Nat × Core.Expr Primitive) → Prop
    | nil : NamedExpressionsAllowed operations []
    | cons {name : Nat} {expression : Core.Expr Primitive}
        {rest : List (Nat × Core.Expr Primitive)}
        (head : ExpressionAllowed operations expression)
        (tail : NamedExpressionsAllowed operations rest) :
        NamedExpressionsAllowed operations ((name, expression) :: rest)

  inductive ClausesAllowed {Primitive : Type} (operations : Primitive → Prop) :
      List (Core.Pattern × Core.Expr Primitive) → Prop
    | nil : ClausesAllowed operations []
    | cons {pattern : Core.Pattern} {body : Core.Expr Primitive}
        {rest : List (Core.Pattern × Core.Expr Primitive)}
        (matching : PatternAllowed pattern)
        (right : ExpressionAllowed operations body)
        (tail : ClausesAllowed operations rest) :
        ClausesAllowed operations ((pattern, body) :: rest)
end

theorem reference_pattern_excluded (inner : Core.Pattern) :
    ¬ PatternAllowed (.reference inner) := by
  intro allowed
  cases allowed

variable {Primitive : Type}

theorem reference_excluded (operations : Primitive → Prop) (body : Core.Expr Primitive) :
    ¬ ExpressionAllowed operations (.reference body) := by
  intro allowed
  cases allowed

theorem read_excluded (operations : Primitive → Prop) (body : Core.Expr Primitive) :
    ¬ ExpressionAllowed operations (.read body) := by
  intro allowed
  cases allowed

theorem assign_excluded (operations : Primitive → Prop) (target body : Core.Expr Primitive) :
    ¬ ExpressionAllowed operations (.assign target body) := by
  intro allowed
  cases allowed

theorem newException_excluded (operations : Primitive → Prop) (name : Nat)
    (body : Core.Expr Primitive) :
    ¬ ExpressionAllowed operations (.newException name body) := by
  intro allowed
  cases allowed

theorem force_allowed {operations : Primitive → Prop} {body : Core.Expr Primitive}
    (allowed : ExpressionAllowed operations body) :
    ExpressionAllowed operations (Core.force body) :=
  .apply (.function (.cons (.suspended (.variable 0)) (.variable 0) .nil)) allowed

/-- This establishes only the effect predicate. The existing static theorem
supplies the independent freshness and typing conditions for the macro. -/
theorem lazyFunction_allowed {operations : Primitive → Prop} (fresh : Nat)
    {clauses : List (Core.Pattern × Core.Expr Primitive)}
    (allowed : ClausesAllowed operations clauses) :
    ExpressionAllowed operations (Core.lazyFunction fresh clauses) :=
  .function (.cons (.variable fresh)
    (.delay (force_allowed (.apply (.function allowed) (.variable fresh)))) .nil)

end Suspensions.Pure

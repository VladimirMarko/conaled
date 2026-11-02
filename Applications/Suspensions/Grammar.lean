import Applications.Suspensions.Syntax

/-!
# The suspension surface productions and precedence

Okasaki's thesis Appendix A, p131, reserves the word dollar and adds expression
and pattern productions at lower precedence than every inherited alternative.
This module is a source-specific grammar adapter over preclassified tokens. It
handles identifiers, application, constructor/exception patterns and grouping
explicitly. Already delimited inherited atomic/full phrases are opaque
parameters with Core embeddings. Their internal lexical and syntactic analysis
is outside this fragment; no complete Standard ML lexer/parser is claimed.

The inherited identifier predicate is a parameter. The new restriction excludes
exactly the spelling dollar, not every symbolic identifier containing that
character. Identifier roles have already been classified as in SML90 §2.4.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Grammar
open Core

inductive Role where
  | valueVariable (name : Nat)
  | valueConstructor (tag : Nat)
  | exceptionConstructor (name : Nat)

structure Identifier (inheritedIdentifier : String → Prop) where
  spelling : String
  inherited : inheritedIdentifier spelling
  notDollar : spelling ≠ "$"
  role : Role

/-- There is no identifier token whose spelling is the newly reserved word. -/
theorem dollar_not_identifier (inheritedIdentifier : String → Prop) :
    ¬ ∃ name : Identifier inheritedIdentifier, name.spelling = "$" := by
  rintro ⟨name, spelling⟩
  exact name.notDollar spelling

namespace Role

def expression {Primitive : Type} : Role → Expr Primitive
  | .valueVariable name => .variable name
  | .valueConstructor tag => .constructor tag none
  | .exceptionConstructor name => .variable name

def pattern : Role → Pattern
  | .valueVariable name => .variable name
  | .valueConstructor tag => .constructor tag none
  | .exceptionConstructor name => .exception name none

end Role

/-- The opaque categories preserve the distinction between inherited atomic
phrases and the inherited alternatives at the full expression/pattern level.
An opaque token represents an already delimited phrase, not an arbitrary span
that the adapter is permitted to swallow. -/
structure Base (Primitive : Type) where
  identifier : String → Prop
  atomicExpression : Type
  expression : Type
  atomicPattern : Type
  pattern : Type
  embedAtomicExpression : atomicExpression → Expr Primitive
  embedExpression : expression → Expr Primitive
  embedAtomicPattern : atomicPattern → Pattern
  embedPattern : pattern → Pattern

inductive Token {Primitive : Type} (base : Base Primitive) where
  | identifier (name : Identifier base.identifier)
  | dollar
  | leftParen
  | rightParen
  | atomicExpression (phrase : base.atomicExpression)
  | expression (phrase : base.expression)
  | atomicPattern (phrase : base.atomicPattern)
  | pattern (phrase : base.pattern)

mutual
  inductive ParsesExpression {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Expr Primitive → Prop
    | dollar {tokens : List (Token base)} {body : Expr Primitive}
        (parsed : ParsesExpression base tokens body) :
        ParsesExpression base (.dollar :: tokens) (.delay body)
    | application {tokens : List (Token base)} {e : Expr Primitive}
        (parsed : ParsesApplication base tokens e) : ParsesExpression base tokens e
    | inherited (phrase : base.expression) :
        ParsesExpression base [.expression phrase] (base.embedExpression phrase)

  inductive ParsesApplication {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Expr Primitive → Prop
    | atomic {tokens : List (Token base)} {e : Expr Primitive}
        (parsed : ParsesAtomicExpression base tokens e) : ParsesApplication base tokens e
    | apply {functionTokens argumentTokens : List (Token base)}
        {function argument : Expr Primitive}
        (operator : ParsesApplication base functionTokens function)
        (operand : ParsesAtomicExpression base argumentTokens argument) :
        ParsesApplication base (functionTokens ++ argumentTokens) (.apply function argument)

  inductive ParsesAtomicExpression {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Expr Primitive → Prop
    | identifier (name : Identifier base.identifier) :
        ParsesAtomicExpression base [.identifier name] name.role.expression
    | parentheses {tokens : List (Token base)} {e : Expr Primitive}
        (parsed : ParsesExpression base tokens e) :
        ParsesAtomicExpression base (.leftParen :: tokens ++ [.rightParen]) e
    | inherited (phrase : base.atomicExpression) :
        ParsesAtomicExpression base [.atomicExpression phrase] (base.embedAtomicExpression phrase)
end

mutual
  inductive ParsesPattern {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Pattern → Prop
    | dollar {tokens : List (Token base)} {p : Pattern}
        (parsed : ParsesPattern base tokens p) :
        ParsesPattern base (.dollar :: tokens) (.suspended p)
    | higher {tokens : List (Token base)} {p : Pattern}
        (parsed : ParsesHigherPattern base tokens p) : ParsesPattern base tokens p
    | inherited (phrase : base.pattern) :
        ParsesPattern base [.pattern phrase] (base.embedPattern phrase)

  inductive ParsesHigherPattern {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Pattern → Prop
    | atomic {tokens : List (Token base)} {p : Pattern}
        (parsed : ParsesAtomicPattern base tokens p) : ParsesHigherPattern base tokens p
    | constructor (name : Identifier base.identifier) {tag : Nat}
        (classified : name.role = .valueConstructor tag)
        {tokens : List (Token base)} {argument : Pattern}
        (parsed : ParsesAtomicPattern base tokens argument) :
        ParsesHigherPattern base (.identifier name :: tokens) (.constructor tag (some argument))
    | exception (name : Identifier base.identifier) {identity : Nat}
        (classified : name.role = .exceptionConstructor identity)
        {tokens : List (Token base)} {argument : Pattern}
        (parsed : ParsesAtomicPattern base tokens argument) :
        ParsesHigherPattern base (.identifier name :: tokens) (.exception identity (some argument))

  inductive ParsesAtomicPattern {Primitive : Type} (base : Base Primitive) :
      List (Token base) → Pattern → Prop
    | identifier (name : Identifier base.identifier) :
        ParsesAtomicPattern base [.identifier name] name.role.pattern
    | parentheses {tokens : List (Token base)} {p : Pattern}
        (parsed : ParsesPattern base tokens p) :
        ParsesAtomicPattern base (.leftParen :: tokens ++ [.rightParen]) p
    | inherited (phrase : base.atomicPattern) :
        ParsesAtomicPattern base [.atomicPattern phrase] (base.embedAtomicPattern phrase)
end

/-- An unparenthesized dollar expression is not an atomic application argument. -/
theorem ParsesAtomicExpression.head {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {e : Expr Primitive}
    (parsed : ParsesAtomicExpression base tokens e) :
    ∃ first rest, tokens = first :: rest ∧ first ≠ .dollar := by
  cases parsed with
  | identifier name => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩
  | parentheses _ => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩
  | inherited phrase => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩

theorem ParsesApplication.head {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {e : Expr Primitive}
    (parsed : ParsesApplication base tokens e) :
    ∃ first rest, tokens = first :: rest ∧ first ≠ .dollar := by
  cases parsed with
  | atomic atom => exact atom.head
  | @apply functionTokens argumentTokens function argument operator operand =>
    obtain ⟨argumentHead, argumentRest, argumentShape, _⟩ := operand.head
    obtain ⟨first, rest, shape, notDollar⟩ := operator.head
    exact ⟨first, rest ++ argumentTokens, by simp only [shape, List.cons_append], notDollar⟩
termination_by tokens.length
decreasing_by
  simp_wf
  simpa [argumentShape] using Nat.succ_pos argumentRest.length

theorem ParsesApplication.not_dollar {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {e : Expr Primitive}
    (parsed : ParsesApplication base tokens e) (rest : List (Token base)) :
    tokens ≠ .dollar :: rest := by
  intro begins
  obtain ⟨first, tail, shape, notDollar⟩ := parsed.head
  exact notDollar (List.cons.inj (shape.symm.trans begins)).1

/-- A leading dollar consumes the entire following expression, including a
following application or an inherited full alternative. -/
theorem expression_dollar_iff {Primitive : Type} {base : Base Primitive}
    (tokens : List (Token base)) (e : Expr Primitive) :
    ParsesExpression base (.dollar :: tokens) e ↔
      ∃ body, ParsesExpression base tokens body ∧ e = .delay body := by
  constructor
  · intro parsed
    cases parsed with
    | dollar body => exact ⟨_, body, rfl⟩
    | application application => exact False.elim (application.not_dollar tokens rfl)
  · rintro ⟨body, parsed, rfl⟩
    exact .dollar parsed

theorem ParsesAtomicPattern.head {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {p : Pattern} (parsed : ParsesAtomicPattern base tokens p) :
    ∃ first rest, tokens = first :: rest ∧ first ≠ .dollar := by
  cases parsed with
  | identifier name => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩
  | parentheses _ => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩
  | inherited phrase => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩

theorem ParsesHigherPattern.head {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {p : Pattern} (parsed : ParsesHigherPattern base tokens p) :
    ∃ first rest, tokens = first :: rest ∧ first ≠ .dollar := by
  cases parsed with
  | atomic atom => exact atom.head
  | constructor name classified argument => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩
  | exception name classified argument => exact ⟨_, _, rfl, by intro impossible; cases impossible⟩

theorem ParsesHigherPattern.not_dollar {Primitive : Type} {base : Base Primitive}
    {tokens : List (Token base)} {p : Pattern} (parsed : ParsesHigherPattern base tokens p)
    (rest : List (Token base)) : tokens ≠ .dollar :: rest := by
  intro begins
  obtain ⟨first, tail, shape, notDollar⟩ := parsed.head
  exact notDollar (List.cons.inj (shape.symm.trans begins)).1

theorem pattern_dollar_iff {Primitive : Type} {base : Base Primitive}
    (tokens : List (Token base)) (p : Pattern) :
    ParsesPattern base (.dollar :: tokens) p ↔
      ∃ inner, ParsesPattern base tokens inner ∧ p = .suspended inner := by
  constructor
  · intro parsed
    cases parsed with
    | dollar inner => exact ⟨_, inner, rfl⟩
    | higher higher => exact False.elim (higher.not_dollar tokens rfl)
  · rintro ⟨inner, parsed, rfl⟩
    exact .dollar parsed

theorem dollar_expression_not_application {Primitive : Type} {base : Base Primitive}
    (tokens : List (Token base)) (function argument : Expr Primitive) :
    ¬ ParsesExpression base (.dollar :: tokens) (.apply function argument) := by
  intro parsed
  obtain ⟨_, _, impossible⟩ := (expression_dollar_iff tokens _).mp parsed
  cases impossible

theorem dollar_pattern_not_constructor {Primitive : Type} {base : Base Primitive}
    (tokens : List (Token base)) (tag : Nat) (argument : Option Pattern) :
    ¬ ParsesPattern base (.dollar :: tokens) (.constructor tag argument) := by
  intro parsed
  obtain ⟨_, _, impossible⟩ := (pattern_dollar_iff tokens _).mp parsed
  cases impossible

end Suspensions.Grammar

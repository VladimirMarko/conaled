import Applications.Suspensions.Grammar

/-!
# Checked dollar precedence cases

These are derivations over the explicitly prelexed token sequence. The chosen
small inherited lexicon contains valid source identifiers, including the old
symbolic identifier dollar and the still-valid longer identifier dollar-plus.
There are no opaque inherited phrases in these concrete clients.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionGrammar
open Suspensions.Core Suspensions.Grammar

def base : Base Empty where
  identifier := fun text => text ∈ ["f", "x", "C", "$", "$+"]
  atomicExpression := Empty
  expression := Empty
  atomicPattern := Empty
  pattern := Empty
  embedAtomicExpression := fun impossible => nomatch impossible
  embedExpression := fun impossible => nomatch impossible
  embedAtomicPattern := fun impossible => nomatch impossible
  embedPattern := fun impossible => nomatch impossible

def f : Identifier base.identifier := ⟨"f", by decide, by decide, .valueVariable 0⟩
def x : Identifier base.identifier := ⟨"x", by decide, by decide, .valueVariable 1⟩
def c : Identifier base.identifier := ⟨"C", by decide, by decide, .valueConstructor 2⟩
def dollarPlus : Identifier base.identifier := ⟨"$+", by decide, by decide, .valueVariable 3⟩

/-- Reservation removes the exact dollar word even though the inherited
identifier class admitted it. It does not remove all longer symbolic names. -/
theorem exact_reserved_word :
    base.identifier "$" ∧
      (¬ ∃ name : Identifier base.identifier, name.spelling = "$") ∧
      dollarPlus.spelling = "$+" := by
  exact ⟨by decide, dollar_not_identifier _, rfl⟩

/-- The source phrase dollar-f-space-x delays the full application. -/
theorem dollar_application :
    ParsesExpression base [.dollar, .identifier f, .identifier x]
      (.delay (.apply (.variable 0) (.variable 1))) := by
  exact .dollar (.application (.apply (.atomic (.identifier f)) (.identifier x)))

/-- Grouping places the dollar expression in the argument's atomic position. -/
theorem application_dollar_argument :
    ParsesExpression base [.identifier f, .leftParen, .dollar, .identifier x, .rightParen]
      (.apply (.variable 0) (.delay (.variable 1))) := by
  exact .application (.apply (.atomic (.identifier f))
    (.parentheses (.dollar (.application (.atomic (.identifier x))))))

theorem dollar_application_rejects_wrong_precedence :
    ¬ ParsesExpression base [.dollar, .identifier f, .identifier x]
      (.apply (.delay (.variable 0)) (.variable 1)) :=
  dollar_expression_not_application _ _ _

/-- Constructor application is inside the leading suspension pattern. -/
theorem dollar_constructor_pattern :
    ParsesPattern base [.dollar, .identifier c, .identifier x]
      (.suspended (.constructor 2 (some (.variable 1)))) := by
  exact .dollar (.higher (.constructor c rfl (.identifier x)))

/-- The grouped suspension pattern is the constructor's atomic argument. -/
theorem constructor_dollar_argument :
    ParsesPattern base [.identifier c, .leftParen, .dollar, .identifier x, .rightParen]
      (.constructor 2 (some (.suspended (.variable 1)))) := by
  exact .higher (.constructor c rfl (.parentheses (.dollar (.higher (.atomic (.identifier x))))))

theorem dollar_constructor_rejects_wrong_precedence :
    ¬ ParsesPattern base [.dollar, .identifier c, .identifier x]
      (.constructor 2 (some (.suspended (.variable 1)))) :=
  dollar_pattern_not_constructor _ _ _

end Examples.SuspensionGrammar

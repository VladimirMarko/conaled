import Applications.Suspensions.Return

/-! Actual expression failures are raised packets; direct pattern failure has
its separate mismatch result. These do not depend on a global typing theorem. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionReturn
open Suspensions.Core Suspensions.Core.Machine

def parameters : Parameters Unit := ⟨fun _ _ => .stuck .primitive, 0, 1⟩
def memory : Memory Unit := Suspensions.empty

def application : Expr Unit :=
  .apply (.function [(.atom (.integer 0), .atom (.integer 2))]) (.atom (.integer 1))

def binding : Expr Unit :=
  .bind (.atom (.integer 0)) (.atom (.integer 1)) (.atom (.integer 2))

theorem application_raises_match :
    ∃ steps, Progress.Evaluates (step parameters) (start memory [] application)
      ⟨memory, .raised (.exception 0 none)⟩ steps :=
  ⟨_, Progress.search_sound (fuel := 30) (by rfl)⟩

theorem binding_raises_bind :
    ∃ steps, Progress.Evaluates (step parameters) (start memory [] binding)
      ⟨memory, .raised (.exception 1 none)⟩ steps :=
  ⟨_, Progress.search_sound (fuel := 20) (by rfl)⟩

theorem direct_pattern_fails :
    Progress.Evaluates (step parameters)
      (startPattern memory [] (.atom (.integer 0)) (.atom (.integer 1)))
      ⟨memory, .mismatch⟩ 2 := .next rfl (.done rfl)

/-- Even arbitrary untyped expression syntax cannot expose the pattern
machine's binding-environment result through the public expression start. -/
theorem expression_never_returns_bindings {s t : Memory Unit} {env bindings : Env Unit}
    {expression : Expr Unit} {steps : Nat}
    (impossible : Progress.Evaluates (step parameters) (start s env expression)
      ⟨t, .matched bindings⟩ steps) : False :=
  Return.expression_result impossible

end Examples.SuspensionReturn

import Applications.Suspensions.Pure.Representation

/-!
# Finite representation of recursive captures

The mutually dependent function/suspension template becomes a represented
closed environment through the public unrolling theorem. A separate group
whose body returns a closure demonstrates a represented closure capture that
refers back to that suspension. These are representation claims, not cache
validity or execution/termination claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureRepresentation
open Suspensions Suspensions.Pure Suspensions.Pure.Representation

def mutualClauses : List (Core.Pattern × Core.Expr Empty) :=
  [(.wildcard, Core.force (.variable 1))]

def mutualBody : Core.Expr Empty := .apply (.variable 0) (.record [])

def mutualGroup : Suspensions.Pure.Group Empty :=
  .mk [(0, .function mutualClauses), (1, .delay mutualBody)] []

def mutualTemplate : Core.Env Empty :=
  [(1, .address 0), (0, .closure mutualClauses [] [])]

def mutualMeaning : Meaning Empty := ⟨mutualBody, [], some mutualGroup⟩

def mutualWorld : World Empty := Durability.put (fun _ => none) 0 mutualMeaning

theorem mutual_template_represented : GroupRep mutualWorld mutualTemplate mutualGroup :=
  .delay rfl (.function .nil (.nil _))

theorem mutual_closed_environment :
    EnvRep mutualWorld (Core.Env.rec mutualTemplate) mutualGroup.members :=
  mutual_template_represented.unroll

theorem mutual_body_environment :
    EnvRep mutualWorld (Core.Env.extend [] (Core.Env.rec mutualTemplate))
      (bodyEnvironment [] (some mutualGroup)) :=
  mutual_template_represented.bodyEnvironment .nil

theorem mutual_function_retains_template :
    ValueRep mutualWorld (.closure mutualClauses [] mutualTemplate)
      (.closure mutualClauses [] (some mutualGroup)) :=
  .recursive_closure .nil mutual_template_represented

def laterMeaning : Meaning Empty := ⟨.atom (.integer 99), [], none⟩

def extendedWorld : World Empty := Durability.put mutualWorld 4 laterMeaning

theorem old_meanings_preserved : Durability.Extends mutualWorld extendedWorld :=
  Durability.extends_put mutualWorld 4 laterMeaning rfl

theorem extended_mutual_environment :
    EnvRep extendedWorld (Core.Env.rec mutualTemplate) mutualGroup.members :=
  (mutual_template_represented.mono old_meanings_preserved).unroll

/-- A raw address cannot acquire an arbitrary meaning without a World entry. -/
theorem missing_meaning_rejected :
    ¬ValueRep (fun _ => none) (.address 0) mutualMeaning.value := by
  have absent (view : Value Empty) : ¬ValueRep (fun _ => none) (.address 0) view := by
    intro represented
    cases represented with
    | address found => cases found
  exact absent _

def closureClauses : List (Core.Pattern × Core.Expr Empty) :=
  [(.variable 1, .branch (.variable 1) (.atom (.integer 7))
    (.apply (Core.force (.variable 0)) (.atom (.boolean true))))]

def closureBody : Core.Expr Empty := .function closureClauses

def closureGroup : Suspensions.Pure.Group Empty := .mk [(0, .delay closureBody)] []

def closureTemplate : Core.Env Empty := [(0, .address 0)]

def closureMeaning : Meaning Empty := ⟨closureBody, [], some closureGroup⟩

def closureWorld : World Empty := Durability.put (fun _ => none) 0 closureMeaning

theorem closure_template_represented : GroupRep closureWorld closureTemplate closureGroup :=
  .delay rfl (.nil _)

/-- The ordinary function value produced by the delayed body may capture the
same suspension's address. No acyclicity premise enters its representation. -/
theorem returned_closure_capture :
    ValueRep closureWorld (.closure closureClauses (Core.Env.rec closureTemplate) [])
      (.closure closureClauses closureGroup.members none) :=
  .closure closure_template_represented.unroll

theorem captured_member_is_same_meaning :
    Env.lookup closureGroup.members 0 = some closureMeaning.value := rfl

end Examples.SuspensionPureRepresentation

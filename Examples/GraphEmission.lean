import SquareKit.Internal.GraphEmission

open SquareKit.Internal

#emit_graph GraphEmitted.forward GraphEmitted.backward

example : 6 = (fun n : Nat => n * 2) ((fun n => n + 1) 2) :=
  GraphEmitted.forward Nat Nat Nat (fun n => n + 1) (fun n => n * 2) 6 2
    ⟨3, rfl, rfl⟩

example : ∃ y : Nat, y = 2 + 1 ∧ 6 = y * 2 :=
  GraphEmitted.backward Nat Nat Nat (fun n => n + 1) (fun n => n * 2) 6 2 rfl

example {A B C : Type v} (f : A → B) (g : B → C) (x : A) (z : C)
    (h : ∃ y, y = f x ∧ z = g y) :
    GraphEmitted.forward A B C f g z x h = (GraphTarget.graph_equivalence f g x z).mp h :=
  Subsingleton.elim _ _

example {A B C : Type v} (f : A → B) (g : B → C) (x : A) (z : C)
    (h : z = g (f x)) :
    GraphEmitted.backward A B C f g z x h = (Graph.inSet f g x z).mpr h :=
  Subsingleton.elim _ _

example (x : Nat) : (x, true) = (x, true) :=
  GraphEmitted.forward Nat (Option Nat) (Nat × Bool)
    some (fun y => (y.getD 0, true)) (x, true) x ⟨some x, rfl, rfl⟩

example (A : Type 1) (x : A) : ∃ y : A, y = x ∧ x = y :=
  GraphEmitted.backward A A A id id x x rfl

open Lean Meta Elab Command GraphEmission GraphTarget

/-- Match the designated diagnostic; an unrelated failure does not pass a test. -/
def expectFailure (message : String) (action : TermElabM Unit) : TermElabM Unit := do
  let result ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  match result with
  | none => throwError "expected failure: {message}"
  | some actual =>
    unless (actual.splitOn message).length > 1 do
      throwError "expected diagnostic '{message}', got '{actual}'"

run_elab do
  let (ty, body) ← emit forwardDeclaration
  checkShape ty
  checkShape (← expandHelpers body)
  expectFailure "graph unsupported projection: Prod.0" <|
    checkShape (.proj ``Prod 0 (.bvar 0))
  expectFailure "graph unsupported projection: And.2" <|
    checkShape (.proj ``And 2 (.bvar 0))
  expectFailure "graph unsupported constructor: letE" <|
    checkShape (.letE `h (.sort .zero) (.bvar 0) (.bvar 0) false)
  expectFailure "graph expression is not closed" <| install `BadBinder ty (.bvar 0)
  expectFailure "graph name already exists" <| install `GraphEmitted.forward ty body
  expectFailure "graph unknown constant: MissingGraphPrimitive" <|
    discard (auditClosure [`MissingGraphPrimitive])
  expectFailure "graph unapproved dependency: Classical.choice" <|
    discard (auditClosure [``Classical.choice])
  expectFailure "graph unapproved dependency: propext" <|
    discard (auditClosure [``propext])
  expectFailure "graph environment signature mismatch: Eq" <|
    checkEnvironment (environmentManifest.map fun (n, sig) =>
      (n, if n == ``Eq then "wrong type or recursor metadata" else sig))
  expectFailure "graph unapproved dependency: Exists.intro" <|
    discard (auditClosure [``Exists] (primitives.filter (· != ``Exists.intro)))
  let badUniverse := body.replace fun
    | .const ``Eq us => some (.const ``Eq (us.map Level.succ))
    | _ => none
  expectFailure "type mismatch" <| install `BadUniverse ty badUniverse
  -- A closed binder corruption must also fail at the kernel boundary.
  let swapped := body.replace fun
    | .bvar 0 => some (.bvar 1)
    | _ => none
  expectFailure "type mismatch" <| install `BadClosedBinder ty swapped
  let (_, reverseBody) ← emit backwardDeclaration
  expectFailure "type mismatch" <| install `BadDirection ty reverseBody
  -- All three carriers coincide; reversing f and g remains well-typed.
  let wrong ← Term.elabType (← `(∀ (f g : Nat → Nat) (z x : Nat),
    (∃ y, y = f x ∧ z = g y) → z = f (g x)))
  let right ← Term.elabType (← `(∀ (f g : Nat → Nat) (z x : Nat),
    (∃ y, y = f x ∧ z = g y) → z = g (f x)))
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrong ← instantiateMVars wrong
  let right ← instantiateMVars right
  check wrong
  check right
  let mut actual := ty.instantiateLevelParams [`v] [.zero]
  for _ in [:3] do actual := actual.bindingBody!.instantiate1 (mkConst ``Nat)
  compareType actual right
  expectFailure "graph expected-type mismatch" <| compareType actual wrong

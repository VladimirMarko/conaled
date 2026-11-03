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

namespace GraphEmissionChecked
open SquareKit.Internal
open GraphTarget

/-- An outer equality survives both the object and proof binders of elimWith. -/
def retained : GraphTarget.Formula [.input, .input] := .eq (.var .zero) (.var (.succ .zero))
def witness : GraphTarget.Formula [.middle, .input, .input] :=
  .eq (.var .zero) (.app .first (.var (.succ .zero)))
def mapped : GraphTarget.Formula [.input, .input] :=
  .eq (.app .first (.var .zero)) (.app .first (.var (.succ .zero)))

def withDeclaration : GraphTarget.Declaration :=
  ⟨[.input, .input], .conj retained (.ex witness), mapped, .elimWith (.congr .left)⟩

/-- Substitution replaces both source variables with applications, in reversed order. -/
def swapApplications : GraphTarget.Sub [.middle, .middle] [.input, .input]
  | _, .zero => .app .first (.var (.succ .zero))
  | _, .succ .zero => .app .first (.var .zero)

def middleEquality : GraphTarget.Formula [.middle, .middle] :=
  .eq (.var .zero) (.var (.succ .zero))

def substitutionDeclaration : GraphTarget.Declaration :=
  ⟨[.input, .input], middleEquality.subst swapApplications,
    (GraphTarget.Formula.eq (.var (.succ .zero)) (.var .zero)).subst swapApplications,
    .subst swapApplications (.symm .ident)⟩

def quantified : GraphTarget.Formula [.input] :=
  .ex (.eq (.var .zero) (.app .first (.var (.succ .zero))))

def chooseOlder : GraphTarget.Sub [.input] [.input, .input]
  | _, .zero => .var (.succ .zero)

def underBinderDeclaration : GraphTarget.Declaration :=
  ⟨[.input, .input], quantified.subst chooseOlder, quantified.subst chooseOlder,
    .subst chooseOlder (.ident : Code quantified quantified)⟩

example : GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit withDeclaration) := GraphEmissionPure.emit_typed _
example : GraphEmissionPure.ArtifactDenotes.{1} (GraphEmissionPure.emit substitutionDeclaration)
    substitutionDeclaration.denote.{1} := GraphEmissionPure.emit_denotes _
example : GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit underBinderDeclaration) := GraphEmissionPure.emit_typed _

def sourceForward : GraphEmissionPure.SourceProgram :=
  ⟨[.input, .output], Graph.composite .first .second, Graph.result .first .second, forward⟩

example : GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit sourceForward.target) ∧
    GraphEmissionPure.ArtifactDenotes.{0} (GraphEmissionPure.emit sourceForward.target) sourceForward.denote.{0} :=
  GraphEmissionPure.source_emission sourceForward

/-- Independently written raw predicate: at the existential binder the stack is
w, x, z, g, f, C, B, A. The different indices distinguish all three uses. -/
def expectedPredicate : CoreSyntax.Expr :=
  .app2 (.const ``And [])
    (.app3 (.const ``Eq [.succ (.param `v)]) (.bvar 6) (.bvar 0)
      (.app (.bvar 4) (.bvar 1)))
    (.app3 (.const ``Eq [.succ (.param `v)]) (.bvar 5) (.bvar 2)
      (.app (.bvar 3) (.bvar 0)))

def endpoints : GraphEmissionPure.Assignment [.input, .output]
  | _, .zero => .bvar 0
  | _, .succ .zero => .bvar 1

example : GraphEmissionPure.formula GraphEmissionPure.parameterModel.shift.shift endpoints forwardDeclaration.premise =
    CoreSyntax.Expr.app2 (.const ``Exists [.succ (.param `v)]) (.bvar 5)
      (.lam (.bvar 5) expectedPredicate) := rfl

/-- The raw syntax connection also carries the independently computed arithmetic meaning. -/
example : CoreSyntax.InLean
    (fun e => GraphEmissionPure.FormulaDenotes (Graph.model (fun n : Nat => n + 1) (fun n => n * 2))
      GraphEmissionPure.parameterModel.shift.shift endpoints
      (Graph.environment (fun n : Nat => n + 1) (fun n => n * 2) 2 6)
      e (∃ y : Nat, y = 3 ∧ 6 = y * 2))
    (GraphEmissionPure.formula GraphEmissionPure.parameterModel.shift.shift endpoints forwardDeclaration.premise).toLean :=
  GraphEmissionPure.formula_toLean_denotes _ _ _ _ _

/-- The proved conversion keeps the universe argument rather than erasing it. -/
example : (CoreSyntax.Expr.const ``Eq [.zero]).toLean ≠
    (CoreSyntax.Expr.const ``Eq [.succ (.param `v)]).toLean := by
  intro h
  have h' := CoreSyntax.Expr.toLean_injective h
  cases h'

set_option hygiene false in
def expectedWith : TermElabM Expr := Term.withLevelNames [`v] do
  let ty ← Term.elabType (← `(∀ (A B C : Type v) (f : A → B) (_g : B → C) (old new : A),
    (new = old ∧ ∃ w, w = f new) → f new = f old))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars ty

run_elab do
  checkExactEnvironment
  for (name, d) in [(`GraphEmitted.withOuter, withDeclaration),
      (`GraphEmitted.substituted, substitutionDeclaration),
      (`GraphEmitted.underBinder, underBinderDeclaration)] do
    installProduced name d
  compareType (GraphEmissionPure.emit withDeclaration).1 (← expectedWith)
  expectFailure "graph exact environment mismatch: Eq" <|
    checkExactEnvironment (GraphPrimitiveEnvironment.declarations.map fun ci =>
      match ci with
      | .inductInfo i => if i.name == ``Eq then .inductInfo { i with numParams := i.numParams + 1 } else ci
      | _ => ci)
  expectFailure "graph exact environment mismatch: Eq.trans" <|
    checkExactEnvironment (GraphPrimitiveEnvironment.declarations.map fun ci =>
      match ci with
      | .thmInfo t => if t.name == ``Eq.trans then .thmInfo { t with value := .sort .zero } else ci
      | _ => ci)

example (x y : Nat) (h : x = y) : some x = some y :=
  GraphEmitted.withOuter Nat (Option Nat) Bool some (fun _ => true) y x ⟨h, some x, rfl⟩

example (f : Nat → Option Nat) (x y : Nat) (h : f y = f x) : f x = f y :=
  GraphEmitted.substituted Nat (Option Nat) Bool f (fun _ => true) y x h

example (f : Nat → Option Nat) (old new : Nat) (h : ∃ w, w = f old) : ∃ w, w = f old :=
  GraphEmitted.underBinder Nat (Option Nat) Bool f (fun _ => true) old new h

end GraphEmissionChecked

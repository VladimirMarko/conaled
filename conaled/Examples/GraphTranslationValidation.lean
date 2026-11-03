import Examples.GraphEmission
import SquareKit.Internal.GraphArtifactTransform

/-! Kernel-checked validator success and precise rejection cases. The two
construction paths install actual declarations and retain their literal records.
Record capture and host installation are executed driver boundaries. -/
namespace GraphTranslationValidation
open Lean SquareKit.Internal GraphTarget GraphEmissionPure
open GraphTranslationValidator GraphArtifactTransform GraphArtifactEquality

abbrev forwardSource := GraphEmissionChecked.sourceForward

def backwardSource : SourceProgram :=
  ⟨[.input, .output], Graph.result .first .second, Graph.composite .first .second, backward⟩

def doubleCertificate : Certificate forwardSource := ⟨1, .symm (.symm forward)⟩

def direct : ConstantInfo := payload `GraphValidated.direct (.original forwardSource)

def transformed : ConstantInfo :=
  (transform (payload `GraphValidated.transformed (.original forwardSource))).getD direct

/-- The raw transformer produces a different proof syntax with a checked replay
correspondence. It does not receive or call the producer's Code traversal. -/
theorem transformed_eq : transformed = payload `GraphValidated.transformed doubleCertificate := by
  rfl

theorem transformed_body_differs : transformed.value? true ≠
    (payload `GraphValidated.transformed (.original forwardSource)).value? true := by
  intro h
  have hn : (transformed.value? true |>.bind CoreSyntax.Expr.ofLean |>.map nodes) ≠
      ((payload `GraphValidated.transformed (.original forwardSource)).value? true |>.bind CoreSyntax.Expr.ofLean |>.map nodes) := by decide
  exact hn (congrArg (fun o => (o.bind CoreSyntax.Expr.ofLean).map nodes) h)

theorem direct_checked : check 10000 forwardSource `GraphValidated.direct
    GraphPrimitiveEnvironment.declarations direct (.original forwardSource) = .ok () :=
  check_payload _ rfl (by decide)

theorem transformed_checked : check 10000 forwardSource `GraphValidated.transformed
    GraphPrimitiveEnvironment.declarations transformed doubleCertificate = .ok () := by
  rw [transformed_eq]
  exact check_payload _ rfl (by decide)

example : check 10000 forwardSource `GraphValidated.transformed
    GraphPrimitiveEnvironment.declarations (renameDeclaration `witness transformed) doubleCertificate = .ok () := by
  rw [check_rename]
  exact transformed_checked

theorem transformed_preserves : Validated.{0} forwardSource `GraphValidated.transformed
    GraphPrimitiveEnvironment.declarations transformed := check_sound transformed_checked

/-- The statement exercises the source theorem obtained through validator
soundness, on heterogeneous carriers and concrete computations. -/
example (x : Nat) : (x + 1, true) = (x + 1, true) :=
  transformed_preserves.source
    (Graph.model (fun n : Nat => some (n + 1)) (fun n => (n.getD 0, true)))
    (Graph.environment (fun n : Nat => some (n + 1)) (fun n => (n.getD 0, true)) x (x + 1, true))
    ⟨some (x + 1), rfl, rfl⟩

/-- This is a well-typed theorem proving the opposite direction, with the name
and universe metadata expected by the request. The intended-type gate rejects it. -/
def wrongConclusion : ConstantInfo := payload `GraphValidated.direct (.original backwardSource)

example : ArtifactTyped (emit backwardSource.target) := emit_typed _

example : check 10000 forwardSource `GraphValidated.direct
    GraphPrimitiveEnvironment.declarations wrongConclusion (.original forwardSource) = .error .type := by
  simp only [check, Certificate.original, approvedEnvironment_checked]
  rfl

/-- Both identities are well typed. Interchanging same-sort object binders
changes the intended premise and conclusion and requires a correspondence. -/
def identitySource (flipped : Bool) : SourceProgram :=
  let x : SourceTerm [.input, .input] .input := .var .zero
  let y : SourceTerm [.input, .input] .input := .var (.succ .zero)
  let p : SourceFormula [.input, .input] := if flipped then .eq y x else .eq x y
  ⟨[.input, .input], p, p, .ident⟩

def permuted : ConstantInfo := payload `GraphValidated.identity (.original (identitySource true))

example : ArtifactTyped (emit (identitySource true).target) := emit_typed _

example : check 10000 (identitySource false) `GraphValidated.identity
    GraphPrimitiveEnvironment.declarations permuted (.original (identitySource false)) = .error .type := by
  simp only [check, Certificate.original, approvedEnvironment_checked]
  rfl

example : check 10000 forwardSource `GraphValidated.direct
    [] direct (.original forwardSource) = .error .environment := by rfl

example : check 10000 forwardSource `GraphValidated.direct
    GraphPrimitiveEnvironment.declarations direct { version := 2, code := forward } = .error .version := rfl

example : check 10000 forwardSource `GraphValidated.direct
    GraphPrimitiveEnvironment.declarations direct doubleCertificate = .error .body := by
  simp only [check, doubleCertificate, approvedEnvironment_checked]
  rfl

example : check 0 forwardSource `GraphValidated.direct
    GraphPrimitiveEnvironment.declarations direct (.original forwardSource) = .error .limit := by
  simp only [check, Certificate.original, approvedEnvironment_checked]
  rfl


/-- Changing a helper body or recursor metadata fails the environment gate. -/
def changedHelper : List ConstantInfo := GraphPrimitiveEnvironment.declarations.map fun ci =>
  match ci with
  | .thmInfo t => if t.name = ``Eq.trans then .thmInfo { t with value := .sort .zero } else ci
  | _ => ci

def changedRecursor : List ConstantInfo := GraphPrimitiveEnvironment.declarations.map fun ci =>
  match ci with
  | .recInfo t => if t.name = ``Exists.rec then .recInfo { t with numMinors := 0 } else ci
  | _ => ci

example : check 10000 forwardSource `GraphValidated.direct changedHelper direct
    (.original forwardSource) = .error .environment := rfl

example : check 10000 forwardSource `GraphValidated.direct changedRecursor direct
    (.original forwardSource) = .error .environment := rfl

example : check 10000 forwardSource `AnotherName GraphPrimitiveEnvironment.declarations direct
    (.original forwardSource) = .error .name := by
  simp only [check, Certificate.original, approvedEnvironment_checked]
  rfl

def backwardArtifact : ConstantInfo := payload `GraphValidated.backward (.original backwardSource)

theorem backward_checked : check 10000 backwardSource `GraphValidated.backward
    GraphPrimitiveEnvironment.declarations backwardArtifact (.original backwardSource) = .ok () :=
  check_payload _ rfl (by decide)

def roundTrip : SourceProgram := composeSource forward backward

def roundTripCertificate : Certificate roundTrip := ⟨1, .cut doubleCertificate.code backward⟩

theorem roundTrip_checked : check 10000 roundTrip `GraphValidated.roundTrip
    GraphPrimitiveEnvironment.declarations (payload `GraphValidated.roundTrip roundTripCertificate)
    roundTripCertificate = .ok () := check_payload _ rfl (by decide)

example : roundTrip.denote.{0} :=
  compose_preserves (check_sound direct_checked) (check_sound backward_checked)

example : artifactRep.{0}.Rel
    (transformed.type, (transformed.value? true).getD (.sort .zero)) forwardSource.denote.{0} :=
  validatedArtifactSquare.{0}.preserves
    (r := ⟨forwardSource, `GraphValidated.transformed, GraphPrimitiveEnvironment.declarations, transformed⟩)
    ⟨transformed_preserves, rfl⟩

deriving instance Repr for ReducibilityHints
deriving instance Repr for QuotKind
deriving instance Repr for ConstantVal
deriving instance Repr for AxiomVal
deriving instance Repr for DefinitionVal
deriving instance Repr for TheoremVal
deriving instance Repr for OpaqueVal
deriving instance Repr for QuotVal
deriving instance Repr for InductiveVal
deriving instance Repr for ConstructorVal
deriving instance Repr for RecursorRule
deriving instance Repr for RecursorVal
deriving instance Repr for ConstantInfo

open Elab Command Meta in
/-- Capture literal post-installation records. The generated definitions are
ordinary kernel data; subsequent theorems check them by reduction. -/
elab "#capture_validated_graph" : command => do
  liftTermElabM do
    GraphEmission.checkExactEnvironment
    for ci in [direct, transformed, backwardArtifact] do
      let .thmInfo t := ci | throwError "validator expected theorem"
      GraphEmission.installDeclaration (.thmDecl t)
  let records ← liftTermElabM do
    return [(← getConstInfo `GraphValidated.direct), (← getConstInfo `GraphValidated.transformed)]
  for (n, ci) in [`installedDirect, `installedTransformed].zip records do
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term (reprStr ci)
    elabCommand (← `(def $(mkIdent n) : Lean.ConstantInfo := $(⟨stx⟩)))
  let envRecords ← liftTermElabM do
    GraphPrimitiveEnvironment.declarations.mapM fun ci => getConstInfo ci.name
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term ((reprStr envRecords).replace "._@" ".«_@»")
  elabCommand (← `(def $(mkIdent `installedEnvironment) : List Lean.ConstantInfo := $(⟨stx⟩)))

#capture_validated_graph

/-- These equations are kernel checked against literal records captured from
getConstInfo, rather than a hash, native evaluator, or acceptance assumption. -/
theorem installedDirect_eq : installedDirect = direct := rfl
theorem installedTransformed_eq : installedTransformed = transformed := rfl
theorem installedEnvironment_eq : installedEnvironment = GraphPrimitiveEnvironment.declarations := rfl

theorem installedDirect_checked : check 10000 forwardSource `GraphValidated.direct
    installedEnvironment installedDirect (.original forwardSource) = .ok () := by
  rw [installedEnvironment_eq, installedDirect_eq]
  exact direct_checked

theorem installedTransformed_checked : check 10000 forwardSource `GraphValidated.transformed
    installedEnvironment installedTransformed doubleCertificate = .ok () := by
  rw [installedEnvironment_eq, installedTransformed_eq]
  exact transformed_checked

example : 6 = (2 + 1) * 2 :=
  GraphValidated.transformed Nat Nat Nat (fun n => n + 1) (fun n => n * 2) 6 2
    ⟨3, rfl, rfl⟩

example (A : Type 1) (x : A) : ∃ y : A, y = x ∧ x = y :=
  GraphValidated.backward A A A id id x x rfl

end GraphTranslationValidation

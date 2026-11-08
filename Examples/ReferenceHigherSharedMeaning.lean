import Examples.ReferenceHigherTheoryMaps
import SquareKit.Internal.DependentJudgments.ReferenceSelectedMeaning
import SquareKit.Internal.DependentJudgments.SelectedIdJRealization

/-! The same selected meaning connects reference proof compilation and semantic
realization of its actual contextual target, including the retained higher action. -/
noncomputable section
namespace Examples.ReferenceHigherSharedMeaning
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open Reference ReferenceHigherTheoryMaps SelectedRealization
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
universe u

abbrev actionJudgment : SelectedMeaning.TermJudgment (Fin 4) :=
  ⟨theta, subTy (subTy actionType sigma) tau, subTm (subTm action sigma) tau⟩
abbrev witnessJudgment : SelectedMeaning.TermJudgment (Fin 4) :=
  ⟨theta, subTy (subTy (identity input.toPoints.pathType input.p input.p') sigma) tau,
    subTm (subTm input.h sigma) tau⟩

variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
variable (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => FrozenMemoSignature.environment M A B
local notation "R" => FrozenMemoSignature.theta M A B
local notation "S" => GuardedGroupoidMemo.signature

/-- Build semantic apd from the selected inputs and the J-built section. Local
quotation laws supply the target term; the final action equation is not a field. -/
def semanticAction : Code M env (.term (R).context (R).dependentActionFamily (R).dependentAction) :=
  Code.apd
    ⟨(S).thetaInput.Γ, (R).context_eval⟩
    (Code.identity ⟨(S).thetaInput.A, (R).family_eval⟩
      ⟨(S).thetaInput.x, (R).x_eval⟩ ⟨(S).thetaInput.y, (R).y_eval⟩)
    ⟨(S).thetaInput.parameters.certificateFamily, (R).certificateFamily_eval (FrozenMemoSignature.inputs M A B)⟩
    ⟨(S).thetaInput.p, (R).p_eval⟩ ⟨(S).thetaInput.p', (R).p'_eval⟩
    ⟨(S).thetaInput.h, (R).h_eval⟩
    ⟨(S).thetaInput.parameters.certificateSection, (R).certificateSection_eval⟩

/-- The quotation is the existing native Id/J program in the final dependent
context; it does not replace that program by a returned integer. -/
theorem semanticAction_quote : (semanticAction M A B).quote =
    (S).thetaInput.parameters.dependentAction (S).thetaInput.p (S).thetaInput.p' (S).thetaInput.h := rfl

/-- The endpoint used by apd is independently the transport of the selected
certificate, with the same chosen higher witness. -/
def semanticTransport : Code M env
    (.term (R).context (M.subTy (R).certificateFamily (R).atParallelPath)
      (R).transportedCertificate) :=
  Code.transport
    ⟨(S).thetaInput.Γ, (R).context_eval⟩
    (Code.identity ⟨(S).thetaInput.A, (R).family_eval⟩
      ⟨(S).thetaInput.x, (R).x_eval⟩ ⟨(S).thetaInput.y, (R).y_eval⟩)
    ⟨(S).thetaInput.parameters.certificateFamily,
      (R).certificateFamily_eval (FrozenMemoSignature.inputs M A B)⟩
    ⟨(S).thetaInput.p, (R).p_eval⟩ ⟨(S).thetaInput.p', (R).p'_eval⟩
    ⟨(S).thetaInput.h, (R).h_eval⟩
    ⟨(S).thetaInput.parameters.certificate (S).thetaInput.p, (R).certificateAtPath_eval⟩

/-- The original object substitutions relate the actual compiler output to the
locally constructed semantic program using their native naturality proof. -/
def compiledActionCode : Code M env (.term (R).context (R).dependentActionFamily (R).dependentAction) := by
  refine ⟨(actionJudgment.term.subst firstTemplate).subst secondTemplate, ?_⟩
  rw [compiled_expression]
  exact (Contextual.interpret (S).dependentAction_twice M env
    (FrozenMemoSignature.inputs M A B)).trans (semanticAction M A B).realizes

def firstCompatible := SelectedMeaning.compatible M declarations firstTemplate
def secondCompatible := SelectedMeaning.compatible M
  (declarations.map (Declaration.instantiate firstTemplate)) secondTemplate
def shared := (secondCompatible M).comp (firstCompatible M)

/-- This proof route uses the actual two local-certificate translations. -/
def sharedAction := (shared M).proof.map actionJudgment ⟨RulePresentation.encode action_twice⟩
def sharedWitness := (shared M).proof.map witnessJudgment ⟨RulePresentation.encode witness_twice⟩

/-- Joint comparison at the chosen client: both routes retain the full section,
including its reindexed family and selected transport endpoint. -/
theorem selected_joint :
    (SelectedMeaning.realization M (Fin 2)).decode env _
      ((shared M).realization.map env actionJudgment
        (SelectedMeaning.quote (p := actionJudgment) action_twice)) =
      .term (R).context (R).dependentActionFamily (R).dependentAction :=
  (compiledActionCode M A B).realizes

theorem selected_proof :
    (SelectedMeaning.proofs M
      ((declarations.map (Declaration.instantiate firstTemplate)).map (Declaration.instantiate secondTemplate))).interpret
      env _ (sharedAction M) = .term (R).context (R).dependentActionFamily (R).dependentAction :=
  (compiledActionCode M A B).realizes

/-- A second selected use retains the actual higher binder under both original
object substitutions; it shares compilation and realization composition. -/
theorem selected_witness :
    (SelectedMeaning.realization M (Fin 2)).decode env _
      ((shared M).realization.map env witnessJudgment
        (SelectedMeaning.quote (p := witnessJudgment) witness_twice)) =
      .term (FrozenMemoStages.tauData M A B).display.total
        (FrozenMemoStages.tauHomotopy M A B).family
        (FrozenMemoStages.tauHomotopy M A B).value :=
  Interpretation.selected_witness M A B

/-- The proof route and realization route expose the same selected higher
witness before the independent final-context observation. -/
theorem witness_joint :
    (SelectedMeaning.proofs M
      ((declarations.map (Declaration.instantiate firstTemplate)).map (Declaration.instantiate secondTemplate))).interpret
      env _ (sharedWitness M) =
    (SelectedMeaning.realization M (Fin 2)).decode env _
      ((shared M).realization.map env witnessJudgment
        (SelectedMeaning.quote (p := witnessJudgment) witness_twice)) := rfl

/-- Realization composition is the existing square composition on the same
selected data. No second observation comparison is supplied to the wrapper. -/
theorem shared_square : (shared M).realization.square env actionJudgment =
    Squares.compose
      ((secondCompatible M).realization.square env
        ((SelectedMeaning.connection M firstTemplate).sentence actionJudgment))
      ((firstCompatible M).realization.square
        ((SelectedMeaning.connection M secondTemplate).reduct env) actionJudgment) := rfl

/-- The shared proof route is exactly the previously compiled reference proof. -/
theorem sharedAction_exact : (sharedAction M).down = compiledAction :=
  compilation_stages.symm

/-- Typing is certified separately from selected data: decode the actual shared
proof and discharge its declarations in the independently supplied model. -/
theorem sharedAction_typed :
    (((actionJudgment.claim).instantiate firstTemplate).instantiate secondTemplate).Valid M env :=
  Reference.sound M env (Interpretation.declarations_valid M A B)
    (RulePresentation.decode (sharedAction M).down)

/-- Preservation derived by capability composition also identifies the source
interpretation with the independently constructed final selected section. -/
theorem source_selected :
    actionJudgment.term.eval (Contextual.algebra M)
      ((SelectedMeaning.connection M firstTemplate).reduct
        ((SelectedMeaning.connection M secondTemplate).reduct env)) =
      .term (R).context (R).dependentActionFamily (R).dependentAction :=
  ((shared M).realization.commutes env actionJudgment
    (SelectedMeaning.quote (p := actionJudgment) action_twice)).symm.trans
      (compiledActionCode M A B).realizes

theorem proof_identity :
    (SquareKit.Institutions.ProofMap.identity (SelectedMeaning.proofs M declarations)).map
      actionJudgment ⟨RulePresentation.encode action_twice⟩ =
      ⟨RulePresentation.encode action_twice⟩ := rfl

end Examples.ReferenceHigherSharedMeaning

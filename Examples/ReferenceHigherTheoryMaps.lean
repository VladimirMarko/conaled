import SquareKit.Internal.DependentJudgments.ReferenceFrozenInput
import SquareKit.Internal.DependentJudgments.ReferenceRulePresentation
import SquareKit.Internal.DependentJudgments.ReferenceSignature
import SquareKit.Internal.DependentJudgments.ReferenceSoundness
import Examples.CubicalFrozenHigherObservation
import Examples.ReferenceDependentCalculus

/-! The actual selected higher binder and its J-derived dependent action,
compiled from the independent reference calculus through local theory maps. -/
noncomputable section
namespace Examples.ReferenceHigherTheoryMaps
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open Reference
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

abbrev α : Contextual.Expression (Fin 4) := .var 0
abbrev β : Contextual.Expression (Fin 4) := .var 1
abbrev initial : List (Declaration (Fin 4)) := [.family empty α, .family (extend empty α) β]
def initialA : Derives initial (.has (.ty empty) α) := .familyDecl (by simp [initial]) .empty
def initialB : Derives initial (.has (.ty (extend empty α)) β) :=
  .familyDecl (by simp [initial]) (.extend initialA)
abbrev rawInput := FrozenInput.input initialA initialB
abbrev sectionContext := extend rawInput.Γ rawInput.toPoints.pathType
abbrev chosenFamily : Contextual.Expression (Fin 4) := .var 2
abbrev chosenSection : Contextual.Expression (Fin 4) := .var 3

/-- The section is input data; its dependent action is not a declaration. -/
abbrev declarations : List (Declaration (Fin 4)) := initial ++
  [.family sectionContext chosenFamily, .term sectionContext chosenFamily chosenSection]
def hA : Derives declarations (.has (.ty empty) α) := .familyDecl (by simp [declarations, initial]) .empty
def hB : Derives declarations (.has (.ty (extend empty α)) β) :=
  .familyDecl (by simp [declarations, initial]) (.extend hA)
abbrev input := FrozenInput.input hA hB

def hFamily : Derives declarations (.has (.ty sectionContext) chosenFamily) :=
  .familyDecl (by simp [declarations]) (.extend (.identity input.hx input.hy))
def hSection : Derives declarations (.has (.tm sectionContext chosenFamily) chosenSection) :=
  .termDecl (by simp [declarations]) hFamily

def signature_valid : WellFormedSignature declarations := by
  have h0 : WellFormedSignature ([.family empty α] : List (Declaration (Fin 4))) :=
    .family 0 .nil .empty (by simp [Fresh])
  have ha : Derives [.family empty α] (.has (.ty empty) α) :=
    .familyDecl (by simp) .empty
  have h1 : WellFormedSignature initial :=
    .family 1 h0 (.extend ha) (by simp [Fresh, Declaration.name, α])
  have h2 : WellFormedSignature (initial ++ [.family sectionContext chosenFamily]) :=
    .family 2 h1 (.extend (.identity rawInput.hx rawInput.hy))
      (by simp [Fresh, initial, Declaration.name, α, β])
  have ha' : Derives (initial ++ [.family sectionContext chosenFamily]) (.has (.ty empty) α) :=
    .familyDecl (by simp [initial]) .empty
  have hb' : Derives (initial ++ [.family sectionContext chosenFamily]) (.has (.ty (extend empty α)) β) :=
    .familyDecl (by simp [initial]) (.extend ha')
  have hf : Derives (initial ++ [.family sectionContext chosenFamily])
      (.has (.ty sectionContext) chosenFamily) :=
    .familyDecl (by simp) (.extend (.identity (FrozenInput.input ha' hb').hx (FrozenInput.input ha' hb').hy))
  exact .term 3 h2 hf (by simp [Fresh, initial, Declaration.name, α, β, chosenFamily])

abbrev action := apd input.Γ input.toPoints.pathType chosenFamily input.p input.p' input.h chosenSection
abbrev actionType := identity (subTy chosenFamily (sectionSub input.Γ input.toPoints.pathType input.p'))
  (transport input.Γ input.toPoints.pathType chosenFamily input.p input.p' input.h
    (subTm chosenSection (sectionSub input.Γ input.toPoints.pathType input.p)))
  (subTm chosenSection (sectionSub input.Γ input.toPoints.pathType input.p'))
def action_typed : Derives declarations (.has (.tm input.Γ actionType) action) :=
  Derives.apd hSection input.hp input.hp' input.hh

abbrev sigma := FrozenInput.Substitutions.sigma hA hB
abbrev tau := FrozenInput.Substitutions.tau hA hB
abbrev delta := FrozenInput.Substitutions.delta hA hB
abbrev theta := FrozenInput.Substitutions.theta hA hB
abbrev sigma_typed := FrozenInput.Substitutions.sigma_typed hA hB
abbrev tau_typed := FrozenInput.Substitutions.tau_typed hA hB

def action_once := Derives.subTm action_typed sigma_typed
def action_twice := Derives.subTm action_once tau_typed
def witness_twice := Derives.subTm (.subTm input.hh sigma_typed) tau_typed

def action_subComp := Derives.subTmComp action_typed sigma_typed tau_typed

def motive_typed := Derives.apdMotive hSection input.hp
def branch_typed := Derives.apdBranch hSection input.hp

/-- Formation is retained both in the base context and in the lifted path context. -/
def branch_twice := Derives.subTm (.subTm branch_typed sigma_typed) tau_typed
def motive_once := Derives.subTy motive_typed (.pathSub input.hp sigma_typed)
def motive_twice := Derives.subTy motive_once (.pathSub (.subTm input.hp sigma_typed) tau_typed)
def branch_family_twice := branch_twice.termFamily
def motive_context_twice := motive_twice.typeContext
def action_context_twice := action_twice.termFamily.typeContext
def substitution_contexts := (sigma_typed.subContexts, tau_typed.subContexts)
def composition_operands := action_subComp.eqOperands

/-- These are the original display maps, whose head constructors are pairs. -/
theorem sigma_nonidentity : sigma ≠ identitySub delta := by
  intro h
  cases h

theorem tau_nonidentity : tau ≠ identitySub theta := by
  intro h
  cases h

private abbrev native := Examples.GuardedGroupoidMemo.signature
private abbrev injection (i : Fin 2) : Fin 3 := i.castLE (by decide)
private abbrev liftNative (e : Contextual.Expression (Fin 2)) : Contextual.Expression (Fin 3) := e.subst (fun i => .var (injection i))

/-- First compilation expands the two declared section symbols to the retained
native family and J-built eta section. It is not a final-action assumption. -/
def firstTemplate : Fin 4 → Contextual.Expression (Fin 3) :=
  ![.var 0, .var 1, liftNative native.input.parameters.certificateFamily,
    liftNative native.input.parameters.certificateSection]
/-- Second compilation changes the leaf namespace while keeping native symbols. -/
def secondTemplate : Fin 3 → Contextual.Expression (Fin 2) := ![.var 0, .var 1, .var 0]

private def finalTemplate : Fin 4 → Contextual.Expression (Fin 2) :=
  ![.var 0, .var 1, native.input.parameters.certificateFamily,
    native.input.parameters.certificateSection]
private theorem lift_cancel (e : Contextual.Expression (Fin 2)) :
    (liftNative e).subst secondTemplate = e := by
  change SquareKit.FinitaryTerm.bind secondTemplate
    (SquareKit.FinitaryTerm.bind (fun i => .leaf (injection i)) e) = e
  rw [SquareKit.FinitaryTerm.bind_assoc]
  have hf : (fun i => SquareKit.FinitaryTerm.bind secondTemplate (.leaf (injection i))) =
      SquareKit.FinitaryTerm.leaf := by
    funext i
    fin_cases i <;> rfl
  rw [hf, SquareKit.FinitaryTerm.bind_leaf]
private theorem template_fusion (e : Contextual.Expression (Fin 4)) :
    (e.subst firstTemplate).subst secondTemplate = e.subst finalTemplate := by
  change SquareKit.FinitaryTerm.bind secondTemplate
    (SquareKit.FinitaryTerm.bind firstTemplate e) = _
  rw [SquareKit.FinitaryTerm.bind_assoc]
  have hf : (fun i => SquareKit.FinitaryTerm.bind secondTemplate (firstTemplate i)) =
      finalTemplate := by
    funext i
    fin_cases i <;> first | rfl | exact lift_cancel _
  rw [hf]

def firstMap := RulePresentation.templateMap declarations firstTemplate
def secondMap := RulePresentation.templateMap (declarations.map (Declaration.instantiate firstTemplate)) secondTemplate
def compiledAction := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode action_twice)
def compiledWitness := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode witness_twice)

def compiledSourceWitness := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode input.hh)
def compiledMotive := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode motive_twice)
def compiledBranch := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode branch_twice)
def compiledComposition := (firstMap.comp secondMap).transport (H' := fun _ => Empty)
  (fun _ => id) (RulePresentation.encode action_subComp)
def compiledCompositionOperands := (RulePresentation.decode compiledComposition).eqOperands

theorem compilation_stages : compiledAction =
    RulePresentation.transport secondTemplate
      (RulePresentation.transport firstTemplate (RulePresentation.encode action_twice)) :=
  RulePresentation.transport_comp firstTemplate secondTemplate _

def compiledIndependent := RulePresentation.decode compiledAction

/-- The translated action is precisely the old client, including its chosen
section, higher witness and both original nonidentity object substitutions. -/
theorem compiled_expression :
    ((subTm (subTm action sigma) tau).subst firstTemplate).subst secondTemplate =
      subTm (subTm (native.input.parameters.dependentAction native.input.p native.input.p' native.input.h)
        native.sigma) native.tau := by
  rw [template_fusion]
  simp only [action, input, sigma, tau, FrozenInput.input, FrozenInput.afterQ, FrozenInput.afterH,
    FrozenInput.parallel, FrozenInput.point, FrozenInput.Points.addY, FrozenInput.Points.addZ,
    FrozenInput.Points.addP, FrozenInput.OnePath.addParallel, FrozenInput.Parallel.addH,
    FrozenInput.Points.reindex, FrozenInput.OnePath.reindex, FrozenInput.Parallel.reindex,
    FrozenInput.Homotopy.reindex, FrozenInput.Points.pathType, FrozenInput.Substitutions.sigma,
    FrozenInput.Substitutions.tau, FrozenInput.Substitutions.deltaAfterZ,
    FrozenInput.Substitutions.duplicate, FrozenInput.Substitutions.replaceZ,
    FrozenInput.Substitutions.deltaZType, FrozenInput.Substitutions.uType,
    FrozenInput.Substitutions.withQ, FrozenInput.Substitutions.withH,
    FrozenInput.Substitutions.withParallel, FrozenInput.Substitutions.withP,
    FrozenInput.Substitutions.xyz, FrozenInput.Substitutions.xy, Reference.Tail.map,
    Reference.Tail.reindex, apd, apdMotive, apdBranch, transportMotive, basedJ, endpoint,
    sectionSub, chosenFamily, chosenSection, α, β, finalTemplate, Term.subst]
  simp
  rfl

theorem compiled_witness_expression :
    ((subTm (subTm input.h sigma) tau).subst firstTemplate).subst secondTemplate = native.thetaInput.h := by
  rw [template_fusion]
  simp only [input, sigma, tau, FrozenInput.input, FrozenInput.afterQ, FrozenInput.afterH,
    FrozenInput.parallel, FrozenInput.point, FrozenInput.Points.addY, FrozenInput.Points.addZ,
    FrozenInput.Points.addP, FrozenInput.OnePath.addParallel, FrozenInput.Parallel.addH,
    FrozenInput.Points.reindex, FrozenInput.OnePath.reindex, FrozenInput.Parallel.reindex,
    FrozenInput.Homotopy.reindex, FrozenInput.Points.pathType, FrozenInput.Substitutions.sigma,
    FrozenInput.Substitutions.tau, FrozenInput.Substitutions.deltaAfterZ,
    FrozenInput.Substitutions.duplicate, FrozenInput.Substitutions.replaceZ,
    FrozenInput.Substitutions.deltaZType, FrozenInput.Substitutions.uType,
    FrozenInput.Substitutions.withQ, FrozenInput.Substitutions.withH,
    FrozenInput.Substitutions.withParallel, FrozenInput.Substitutions.withP,
    FrozenInput.Substitutions.xyz, FrozenInput.Substitutions.xy, Reference.Tail.map,
    Reference.Tail.reindex, sectionSub, α, β, finalTemplate, Term.subst]
  simp
  rfl


abbrev compiledDeclarations :=
  (declarations.map (Declaration.instantiate firstTemplate)).map (Declaration.instantiate secondTemplate)

private theorem compiled_context : (sectionContext.subst firstTemplate).subst secondTemplate =
    native.input.parameters.pathContext := by
  rw [template_fusion]
  simp only [sectionContext, rawInput, FrozenInput.input, FrozenInput.afterQ, FrozenInput.afterH,
    FrozenInput.parallel, FrozenInput.point, FrozenInput.Points.addY, FrozenInput.Points.addZ,
    FrozenInput.Points.addP, FrozenInput.OnePath.addParallel, FrozenInput.Parallel.addH,
    FrozenInput.Points.reindex, FrozenInput.OnePath.reindex, FrozenInput.Parallel.reindex,
    FrozenInput.Homotopy.reindex, FrozenInput.Points.pathType, sectionSub, α, β, finalTemplate,
    Term.subst]
  simp
  rfl

private theorem compiled_source_witness : (input.h.subst firstTemplate).subst secondTemplate =
    native.input.h := by
  rw [template_fusion]
  simp only [input, FrozenInput.input, FrozenInput.afterQ, FrozenInput.afterH, FrozenInput.parallel,
    FrozenInput.point, FrozenInput.Points.addY, FrozenInput.Points.addZ, FrozenInput.Points.addP,
    FrozenInput.OnePath.addParallel, FrozenInput.Parallel.addH, FrozenInput.Points.reindex,
    FrozenInput.OnePath.reindex, FrozenInput.Parallel.reindex, FrozenInput.Homotopy.reindex,
    FrozenInput.Points.pathType, sectionSub, α, β, finalTemplate, Term.subst]
  simp
  rfl

private theorem compiled_declarations : compiledDeclarations =
    [.family empty (.var 0), .family (extend empty (.var 0)) (.var 1),
      .family native.input.parameters.pathContext native.input.parameters.certificateFamily,
      .term native.input.parameters.pathContext native.input.parameters.certificateFamily
        native.input.parameters.certificateSection] := by
  simp only [compiledDeclarations, declarations, initial, List.map_cons, List.map_nil,
    Declaration.instantiate, List.cons_append, List.nil_append]
  rw [compiled_context]
  simp only [template_fusion]
  simp [α, β, chosenFamily, chosenSection, finalTemplate]

namespace Interpretation
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
variable (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => Examples.FrozenMemoSignature.environment M A B

/-- The two new declarations are discharged by the retained section's own
native formation/typing derivations, never by the final action theorem. -/
theorem declarations_valid : ∀ d ∈ compiledDeclarations,
    d.encode.eval (Contextual.algebra M) env := by
  intro d hd
  rw [compiled_declarations] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact Examples.FrozenMemoSignature.inputs M A B _ (by simp [Examples.GuardedGroupoidMemo.premises, Declaration.encode, Examples.GuardedGroupoidMemo.alpha, Examples.GuardedGroupoidMemo.beta])
  · exact Examples.FrozenMemoSignature.inputs M A B _ (by simp [Examples.GuardedGroupoidMemo.premises, Declaration.encode, Examples.GuardedGroupoidMemo.alpha, Examples.GuardedGroupoidMemo.beta])
  · exact Contextual.interpret native.input.parameters.certificateSection_typed.family M env
      (Examples.FrozenMemoSignature.inputs M A B)
  · exact Contextual.interpret native.input.parameters.certificateSection_typed M env
      (Examples.FrozenMemoSignature.inputs M A B)

/-- Semantic typing consumes the actual decoded local-certificate translation. -/
theorem compiled_typed :
    (((Claim.has (.tm theta (subTy (subTy actionType sigma) tau))
      (subTm (subTm action sigma) tau)).instantiate firstTemplate).instantiate secondTemplate).Valid M env :=
  Reference.sound M env (declarations_valid M A B) compiledIndependent

theorem compiled_witness_typed :
    (((Claim.has (.tm theta
      (subTy (subTy (identity input.toPoints.pathType input.p input.p') sigma) tau))
      (subTm (subTm input.h sigma) tau)).instantiate firstTemplate).instantiate secondTemplate).Valid M env :=
  Reference.sound M env (declarations_valid M A B) (RulePresentation.decode compiledWitness)

theorem source_witness_typed :
    (((Claim.has (.tm input.Γ (identity input.toPoints.pathType input.p input.p')) input.h).instantiate
      firstTemplate).instantiate secondTemplate).Valid M env :=
  Reference.sound M env (declarations_valid M A B) (RulePresentation.decode compiledSourceWitness)

theorem selected_action :
    (((subTm (subTm action sigma) tau).subst firstTemplate).subst secondTemplate).eval
      (Contextual.algebra M) env =
    .term (Examples.FrozenMemoSignature.theta M A B).context
      (Examples.FrozenMemoSignature.theta M A B).dependentActionFamily
      (Examples.FrozenMemoSignature.theta M A B).dependentAction := by
  rw [compiled_expression]
  exact Examples.FrozenMemoSignature.dependentAction_twice M A B

theorem selected_witness :
    (((subTm (subTm input.h sigma) tau).subst firstTemplate).subst secondTemplate).eval
      (Contextual.algebra M) env =
    .term (Examples.FrozenMemoStages.tauData M A B).display.total
      (Examples.FrozenMemoStages.tauHomotopy M A B).family
      (Examples.FrozenMemoStages.tauHomotopy M A B).value := by
  rw [compiled_witness_expression]
  exact (Examples.FrozenMemoStages.tauHomotopy M A B).eval

def recoveredAction :=
  ((((subTm (subTm action sigma) tau).subst firstTemplate).subst secondTemplate).eval
    (Contextual.algebra M) env).termAt (Examples.FrozenMemoSignature.theta M A B).context
      (Examples.FrozenMemoSignature.theta M A B).dependentActionFamily

theorem recoveredAction_eq : recoveredAction M A B =
    some (Examples.FrozenMemoSignature.theta M A B).dependentAction := by
  unfold recoveredAction
  rw [selected_action]
  exact Value.termAt_term _ _ _

theorem selected_source_witness :
    ((input.h.subst firstTemplate).subst secondTemplate).eval (Contextual.algebra M) env =
    .term (Examples.FrozenMemoStages.inputContext M.toStructuralModel A B) _
      (Examples.FrozenMemoStages.selectedHomotopy M.toStructuralModel A B) := by
  rw [compiled_source_witness]
  exact Examples.FrozenMemoStages.selectedHomotopy_eval M A B

end Interpretation
namespace HigherControl
set_option backward.isDefEq.respectTransparency false
open SquareKit.Cubical SquareKit.Cubical.Presheaf SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoStages

/-- The witness argument fixes the dependent extraction type; the value is
read from the translated expression, not from this argument. -/
private def readLike {M : SquareKit.Internal.PathTransport.Typed.StructuralModel}
    {Γ : M.Context} {A : M.Family Γ} (_ : M.Section Γ A) (v : Value M) := v.termAt Γ A

def recovered := readLike (selectedHomotopy CM cocycleBase cocycleRootedFamily)
  (((input.h.subst firstTemplate).subst secondTemplate).eval (Contextual.algebra cocycleModel)
    (Examples.FrozenMemoSignature.environment cocycleModel cocycleBase cocycleRootedFamily))

theorem recovered_eq : recovered = some (selectedHomotopy CM cocycleBase cocycleRootedFamily) := by
  unfold recovered
  rw [Interpretation.selected_source_witness]
  exact Value.termAt_term _ _ _

/-- Normalize only the known family equality, then observe the recovered cell. -/
def observation : Option Int := recovered.map (fun h =>
  secondObservation (cast (type_eq_of_heq retainedHomotopy) (h.down.reindex assignInput)))

theorem observation_one : observation = some 1 := by
  unfold observation
  rw [recovered_eq]
  change some (secondObservation selectedNormalizedHomotopy) = some 1
  rw [frozenHigherObservation]

/-- Endpoint-only/reflexive replacement would yield zero, so this observation
rejects it for the very witness used by the compiled dependent action. -/
theorem rejects_truncation : observation ≠ some 0 := by
  rw [observation_one]
  exact fun h => Int.one_ne_zero (Option.some.inj h)

theorem rejects_reflexive : observation ≠ some (secondObservation (secondZero terminal.{0})) := by
  rw [secondObservation_zero]
  exact rejects_truncation

end HigherControl

namespace NonemptyTail
open Examples.ReferenceDependentCalculus

/-- A permutation changes free names without imposing new declaration meanings. -/
def rename : Fin 4 → Contextual.Expression (Fin 4) := ![.var 1, .var 0, .var 3, .var 2]
theorem rename_twice (e : Contextual.Expression (Fin 4)) : (e.subst rename).subst rename = e := by
  change SquareKit.FinitaryTerm.bind rename (SquareKit.FinitaryTerm.bind rename e) = e
  rw [SquareKit.FinitaryTerm.bind_assoc]
  have h : (fun i => SquareKit.FinitaryTerm.bind rename (rename i)) = SquareKit.FinitaryTerm.leaf := by
    funext i
    fin_cases i <;> rfl
  rw [h, SquareKit.FinitaryTerm.bind_leaf]

/-- A two-entry dependent tail exercises J, beta and branch-map certificates.
The independent motive mentions the final generic term. -/
def mappedJ := RulePresentation.transport rename (RulePresentation.encode dependentJ)
def mappedBeta := RulePresentation.transport rename
  (RulePresentation.transport rename (RulePresentation.encode beta))
def mappedNaturality := RulePresentation.transport rename
  (RulePresentation.transport rename (RulePresentation.encode naturality))
def typedNaturality := RulePresentation.decode mappedNaturality
def naturalityOperands := typedNaturality.eqOperands

theorem two_stages :
    ((RulePresentation.templateMap Examples.ReferenceDependentCalculus.declarations rename).comp
      (RulePresentation.templateMap
        (Examples.ReferenceDependentCalculus.declarations.map (Declaration.instantiate rename))
        rename)).transport (H' := fun _ => Empty) (fun _ => id)
        (RulePresentation.encode naturality) = mappedNaturality :=
  RulePresentation.transport_comp rename rename _

private theorem declaration_roundtrip (d : Declaration (Fin 4)) :
    (d.instantiate rename).instantiate rename = d := by
  cases d <;> simp only [Declaration.instantiate, rename_twice]
private theorem claim_roundtrip (c : Claim (Fin 4)) :
    (c.instantiate rename).instantiate rename = c := by
  cases c with
  | has b t => cases b <;> simp only [Claim.instantiate, Boundary.instantiate, rename_twice]
  | eq b s t => cases b <;> simp only [Claim.instantiate, Boundary.instantiate, rename_twice]
  | tail Γ T =>
    have ht : (T.instantiate rename).instantiate rename = T := by
      induction T with
      | nil => rfl
      | cons A T ih => simp only [Tail.instantiate, rename_twice, ih]
    simp only [Claim.instantiate, rename_twice, ht]

/-- The auxiliary tail case has an established inhabited dependent model;
its twice-renamed declaration list recovers the original valid list. -/
theorem interpreted_naturality : naturalityClaim.Valid Native.M Native.environment := by
  have hD : ∀ d ∈
      ((Examples.ReferenceDependentCalculus.declarations.map (Declaration.instantiate rename)).map
        (Declaration.instantiate rename)),
      d.encode.eval (Contextual.algebra Native.M) Native.environment := by
    simpa [List.map_map, Function.comp_def, declaration_roundtrip] using
      Native.declarations_valid
  have h := Reference.sound Native.M Native.environment hD typedNaturality
  simpa only [claim_roundtrip] using h
end NonemptyTail
end Examples.ReferenceHigherTheoryMaps

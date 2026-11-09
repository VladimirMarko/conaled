import EmittedBackwardAcceptance
/-! Experimental #135 acceptance of the canonical emitted family and exact environment.
See [scope report](../../docs/research/relative-emitted-acceptance.md). -/
namespace EmittedAcceptance
open ConLeche AcceptanceComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000
set_option pp.deepTerms.threshold 8
measured_theorem helper_list : EmittedEnvironment.helpers = [NativeHelper0.decl, NativeHelper1.decl, NativeHelper2.decl, NativeHelper3.decl, NativeHelper4.decl, NativeHelper5.decl, NativeHelper6.decl, NativeHelper7.decl, NativeHelper8.decl] := by cbv
measured_theorem helpers : EmittedEnvironment.helpers.foldlM (checkDecl .verified (fueledOps .verified 32) []) GraphEnvironment.environment = .ok NativeHelper8.after := by
  rw [helper_list]
  refine fold_cons _ _ _ _ _ _ NativeHelper0.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper1.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper2.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper3.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper4.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper5.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper6.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper7.accepted ?_
  refine fold_cons _ _ _ _ _ _ NativeHelper8.accepted ?_
  rfl
measured_theorem graph_list : EmittedEnvironment.graphDeclarations = [EmittedForwardAcceptance.decl, EmittedBackwardAcceptance.decl] := by cbv
measured_theorem graph : EmittedEnvironment.graphDeclarations.foldlM (checkDecl .verified (fueledOps .verified 32) []) NativeHelper8.after = .ok EmittedBackwardAcceptance.after := by
  rw [graph_list]
  refine fold_cons _ _ _ _ _ _ EmittedForwardAcceptance.accepted ?_
  refine fold_cons _ _ _ _ _ _ EmittedBackwardAcceptance.accepted ?_
  rfl
measured_theorem environment_eq : EmittedBackwardAcceptance.after = EmittedEnvironment.environment := by cbv
measured_theorem accepted : checkDeclsPure (mode := .verified) (fueledOps .verified 32) [] EmittedEnvironment.declarations = .ok EmittedEnvironment.environment := by
  have tail := fold_append (checkDecl .verified (fueledOps .verified 32) []) _ _ _ _ _ helpers graph
  have full := fold_append (checkDecl .verified (fueledOps .verified 32) []) _ _ _ _ _ PrimitiveAcceptance.accepted tail
  rw [environment_eq] at full
  exact full
end EmittedAcceptance
#audit_graph_module

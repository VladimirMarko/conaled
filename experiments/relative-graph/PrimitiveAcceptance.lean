import ExistsInstallerAcceptance
/-! Experimental #135 pure acceptance of the exact preserved primitive stream.
See [scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace PrimitiveAcceptance
open ConLeche
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option pp.deepTerms.threshold 8
measured_theorem equality : checkDecl .verified (fueledOps .verified 32) [] Env.empty (.indDecl eqBasis 2) = .ok AcceptanceStages.equalityEnvironment := by
  simp only [checkDecl, AcceptanceStages.equalityPin]
  cbv
measured_theorem accepted : checkDeclsPure (mode := .verified) (fueledOps .verified 32) [] GraphEnvironment.declarations.toList = .ok GraphEnvironment.environment := by
  exact AcceptanceComposition.fold_three (checkDecl .verified (fueledOps .verified 32) [])
    (.indDecl eqBasis 2) (.indDecl andPin 2) (.indDecl GraphEnvironment.existsBlock 2)
    Env.empty AcceptanceStages.equalityEnvironment AndInstallation.andEnv GraphEnvironment.environment
    equality AndInstallerAcceptance.accepted ExistsInstallerAcceptance.accepted
end PrimitiveAcceptance
#audit_graph_module

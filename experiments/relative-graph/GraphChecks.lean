import ArtifactAudit
import GraphDeclarations

/-! Executed checks, not kernel proofs of checker acceptance. Failure aborts
this file's check. Both constants and projection tables are compared. -/
open ConLeche
private def sameEnvironment (a b : Env) : Bool := a.consts == b.consts && a.tables == b.tables
private def acceptsAs (ds : Array Declaration) (expected : Env) : Bool :=
  match Cached.checkDecls .verified [] ds with
  | .ok actual => sameEnvironment actual expected
  | .error _ => false
private def rejects (ds : Array Declaration) : Bool :=
  match Cached.checkDecls .verified [] ds with
  | .ok _ => false
  | .error _ => true

#eval do
  unless acceptsAs GraphEnvironment.declarations GraphEnvironment.environment do
    throw (IO.userError "Primitive environment acceptance or stored metadata mismatch")
  unless acceptsAs GraphDeclarations.declarations GraphDeclarations.environment do
    throw (IO.userError "Closed graph declaration acceptance or stored metadata mismatch")
  unless rejects #[.indDecl eqBasis 2, .indDecl andPin 2,
      .indDecl GraphEnvironment.existsBlock 1] do
    throw (IO.userError "Wrong Exists parameter count accepted")
  unless rejects (GraphEnvironment.declarations ++ #[Declaration.thmDecl
      ⟨GraphDeclarations.forwardName, [BasisDSL.vN], GraphDeclarations.backwardType⟩
      GraphDeclarations.forwardProof]) do
    throw (IO.userError "Forward proof accepted against backward statement")
  unless !(acceptsAs GraphEnvironment.declarations { GraphEnvironment.environment with tables := [] }) do
    throw (IO.userError "Missing projection tables not detected")
  IO.println "Graph checks: primitive and closed environments accepted; parameter, direction, and table mismatches rejected"

#audit_graph_module

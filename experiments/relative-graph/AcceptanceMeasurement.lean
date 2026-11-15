import ArtifactAudit

/-! Experimental timing command for #135. Generated proof terms are inserted
through Lean's checked addDecl, with no native acceptance oracle. -/
open Lean Elab Command Meta

register_option acceptance.measureTreeSize : Bool := {
  defValue := true
  descr := "Count expression nodes without sharing; disable for very large duplicated proof trees." }

/-- Optional per-attempt side channel keeps phase markers if the compiler is killed.
It is diagnostic output and contributes no proof premise. -/
def recordAcceptanceMeasurement (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush
  if let some path ← IO.getEnv "CONALED_ACCEPTANCE_PHASE_LOG" then
    let stream ← IO.FS.Handle.mk path .append
    stream.putStrLn message
    stream.flush

elab "measured_theorem " n:ident " : " ty:term " := " val:term : command => do
  let start ← IO.monoNanosNow
  liftIO <| recordAcceptanceMeasurement s!"start_generation {n.getId}"
  (← IO.getStdout).flush
  let (type,value) ← liftTermElabM do
    let type ← Term.elabType ty
    let value ← Term.elabTermEnsuringType val type
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars type, ← instantiateMVars value)
  if type.hasSorry || value.hasSorry then
    throwError "Proof generation failed; refusing an admitted declaration"
  let generated ← IO.monoNanosNow
  liftIO <| recordAcceptanceMeasurement s!"proof_generated generation_ns={generated-start}"
  if acceptance.measureTreeSize.get (← getOptions) then
    liftIO <| recordAcceptanceMeasurement s!"expression_nodes={value.sizeWithoutSharing}"
  else
    liftIO <| recordAcceptanceMeasurement "expression_nodes=not_measured"
  (← IO.getStdout).flush
  let name := (← getCurrNamespace) ++ n.getId
  let d := Declaration.thmDecl { name, levelParams := [], type, value }
  let checkStart ← IO.monoNanosNow
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl d
  let checked ← IO.monoNanosNow
  liftIO <| recordAcceptanceMeasurement s!"kernel_declaration_ns={checked-checkStart}"
  (← IO.getStdout).flush
  let renderedStart ← IO.monoNanosNow
  let rendered ← liftTermElabM <| withOptions (fun o => o.set `pp.deepTerms.threshold (3 : Nat)) do
    return (← ppExpr type).pretty 80
  let renderedEnd ← IO.monoNanosNow
  liftIO <| recordAcceptanceMeasurement s!"render_ns={renderedEnd-renderedStart}; rendered_chars={rendered.length}; proposition={rendered.take 1024}"
  (← IO.getStdout).flush

/-- Freeze a computed intermediate representation together with its checked
normalization equation. This is proof-producing cbv, not native evaluation. -/
elab "checked_normal_form " n:ident " : " ty:term " := " val:term : command => do
  liftIO <| recordAcceptanceMeasurement s!"start_normal_form_generation {n.getId}"
  let start ← IO.monoNanosNow
  let (type,original,result,proof) ← liftTermElabM do
    let type ← Term.elabType ty
    let original ← Term.elabTermEnsuringType val type
    Term.synthesizeSyntheticMVarsNoPostponing
    let original ← instantiateMVars original
    let r ← Lean.Meta.Tactic.Cbv.cbvEntry original
    let result := r.getResultExpr original
    let proof ← match r with
      | .rfl .. => mkEqRefl original
      | .step _ proof .. => pure proof
    return (← instantiateMVars type,original,result,proof)
  if type.hasSorry || original.hasSorry || result.hasSorry || proof.hasSorry then
    throwError "Normalization failed; refusing an admitted declaration"
  let generated ← IO.monoNanosNow
  let name := (← getCurrNamespace) ++ n.getId
  liftIO <| recordAcceptanceMeasurement s!"normal_form_generated {name}: generation_ns={generated-start}; result_tree_nodes={result.sizeWithoutSharing}"
  let decl := Declaration.defnDecl { name, levelParams := [], type, value := result, hints := .abbrev, safety := .safe }
  liftCoreM <| withOptions (Elab.async.set · false) <| addAndCompile decl
  let eqType ← liftTermElabM <| mkEq original (mkConst name)
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl <| .thmDecl
    { name := name.appendAfter "_eq", levelParams := [], type := eqType, value := proof }
  let checked ← IO.monoNanosNow
  liftIO <| recordAcceptanceMeasurement s!"normal_form {name}: generation_ns={generated-start}; checked_insertions_and_codegen_ns={checked-generated}; result_tree_nodes={result.sizeWithoutSharing}"

#audit_graph_module

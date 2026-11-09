import Lean

/-! Experimental timing command for #135. Generated proof terms are inserted
through Lean's checked addDecl, with no native acceptance oracle. -/
open Lean Elab Command Meta
elab "measured_theorem " n:ident " : " ty:term " := " val:term : command => do
  let start ← IO.monoNanosNow
  IO.println s!"start_generation {n.getId}"
  (← IO.getStdout).flush
  let (type,value) ← liftTermElabM do
    let type ← Term.elabType ty
    let value ← Term.elabTermEnsuringType val type
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars type, ← instantiateMVars value)
  if type.hasSorry || value.hasSorry then
    throwError "Proof generation failed; refusing an admitted declaration"
  let generated ← IO.monoNanosNow
  IO.println s!"generation_ns={generated-start}; expression_nodes={value.sizeWithoutSharing}"
  (← IO.getStdout).flush
  let name := (← getCurrNamespace) ++ n.getId
  let d := Declaration.thmDecl { name, levelParams := [], type, value }
  let checkStart ← IO.monoNanosNow
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl d
  let checked ← IO.monoNanosNow
  IO.println s!"kernel_declaration_ns={checked-checkStart}"
  (← IO.getStdout).flush
  let renderedStart ← IO.monoNanosNow
  let rendered ← liftTermElabM <| withOptions (fun o => o.set `pp.deepTerms.threshold (3 : Nat)) do
    return (← ppExpr type).pretty 80
  let renderedEnd ← IO.monoNanosNow
  IO.println s!"render_ns={renderedEnd-renderedStart}; rendered_chars={rendered.length}; proposition={rendered.take 1024}"
  (← IO.getStdout).flush

/-- Freeze a computed intermediate representation together with its checked
normalization equation. This is proof-producing cbv, not native evaluation. -/
elab "checked_normal_form " n:ident " : " ty:term " := " val:term : command => do
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
  let generated ← IO.monoNanosNow
  let name := (← getCurrNamespace) ++ n.getId
  let decl := Declaration.defnDecl { name, levelParams := [], type, value := result, hints := .abbrev, safety := .safe }
  liftCoreM <| withOptions (Elab.async.set · false) <| addAndCompile decl
  let eqType ← liftTermElabM <| mkEq original (mkConst name)
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl <| .thmDecl
    { name := name.appendAfter "_eq", levelParams := [], type := eqType, value := proof }
  let checked ← IO.monoNanosNow
  IO.println s!"normal_form {name}: generation_ns={generated-start}; checked_insertions_and_codegen_ns={checked-generated}; result_tree_nodes={result.sizeWithoutSharing}"

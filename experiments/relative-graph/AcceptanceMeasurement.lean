import Lean

/-! Experimental timing command for #135. Generated proof terms are inserted
through Lean's checked addDecl, with no native acceptance oracle. -/
open Lean Elab Command Meta
elab "measured_theorem " n:ident " : " ty:term " := " val:term : command => do
  let start ← IO.monoNanosNow
  let (type,value) ← liftTermElabM do
    let type ← Term.elabType ty
    let value ← Term.elabTermEnsuringType val type
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars type, ← instantiateMVars value)
  let generated ← IO.monoNanosNow
  logInfo m!"generation_ns={generated-start}; expression_nodes={value.sizeWithoutSharing}"
  let name := (← getCurrNamespace) ++ n.getId
  let d := Declaration.thmDecl { name, levelParams := [], type, value }
  let checkStart ← IO.monoNanosNow
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl d
  let checked ← IO.monoNanosNow
  logInfo m!"kernel_declaration_ns={checked-checkStart}"
  let renderedStart ← IO.monoNanosNow
  let rendered ← liftTermElabM <| withOptions (fun o => o.set `pp.deepTerms.threshold (3 : Nat)) do
    return (← ppExpr type).pretty 80
  let renderedEnd ← IO.monoNanosNow
  logInfo m!"render_ns={renderedEnd-renderedStart}; rendered_chars={rendered.length}; proposition={rendered.take 1024}"

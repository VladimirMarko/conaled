import Lean
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-! Checker commands for the finite interpretation-assistance experiment.
These commands inspect actual declarations; they add no transport axioms. -/
namespace InterpretationDiagnostics
open Lean Elab Command

elab "#transport_requirement " n:ident : command => do
  let info ← getConstInfo n.getId
  match info.value? with
  | some value => logInfo m!"REQUIREMENT {n.getId}: {value}"
  | none => throwError "Requirement must be a defined proposition"

/-- Audit every current-module logical declaration, including private/generated
helpers, and the named result's transitive dependencies. Imported unused
axioms are not roots; an imported axiom used by any local declaration is. -/
elab "#transport_audit " n:ident : command => do
  let env ← getEnv
  let _ ← getConstInfo n.getId
  let roots := env.constants.foldStage2 (fun acc name info =>
    if (env.getModuleIdxFor? name).isNone then acc.push (name, info) else acc) #[]
  let mut count : Nat := 0
  for (name, info) in roots do
    if info.isUnsafe then
      if (declRangeExt.find? env name).isSome then
        throwError "Unsafe source declaration {name}"
    else
      count := count + 1
      logInfo m!"TRANSPORT_ROOT {name}"
      for ax in (← Lean.collectAxioms name) do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
  for ax in (← Lean.collectAxioms n.getId) do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Forbidden axiom {ax} in result {n.getId}"
  if count == 0 then throwError "No local declarations audited"
  logInfo m!"TRANSPORT_AUDIT_OK {n.getId}; local roots: {count}"
end InterpretationDiagnostics

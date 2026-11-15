import Lean
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-! Experimental isolated closure audit for #135. The runner supplies exact module
origins. Every kernel-safe declaration, including unused and private declarations,
is a root. Unsafe upstream implementation declarations are reported separately;
unsafe source declarations in the local closure are rejected. See
[scope report](../../docs/research/relative-and-root-checkpoint.md). -/
open Lean Elab Command

elab "#audit_closure " "[" modules:ident,* "]" " local " "[" locals:ident,* "]" : command => do
  let env ← getEnv
  let required := modules.getElems.map Syntax.getId
  let localModules := locals.getElems.map Syntax.getId
  for name in required do
    unless env.header.moduleNames.contains name || env.mainModule == name do
      throwError "Audit module not imported: {name}"
  for name in localModules do
    unless required.contains name do
      throwError "Local audit module outside closure: {name}"
  let mut roots : Nat := 0
  let mut runtime : Nat := 0
  let mut union : NameSet := {}
  for (name, info) in env.constants do
    let origin := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if !required.contains origin then continue
    if info.isUnsafe then
      runtime := runtime + 1
      if (declRangeExt.find? env name).isSome then
        if localModules.contains origin then
          throwError "Unsafe local source declaration {name} in {origin}"
        logInfo m!"Upstream unsafe source excluded from logical roots: {name} in {origin}"
      continue
    roots := roots + 1
    for axiomName in (← liftCoreM (Lean.collectAxioms name)) do
      unless axiomName == ``propext || axiomName == ``Classical.choice || axiomName == ``Quot.sound do
        throwError "Forbidden axiom {axiomName} in {name} ({origin})"
      union := union.insert axiomName
  if roots == 0 then throwError "Empty logical audit closure"
  logInfo m!"Closure audit PASSED: {required.size} modules, {roots} kernel-safe roots, {runtime} unsafe runtime declarations; axioms {union.toList}"

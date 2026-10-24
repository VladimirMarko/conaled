import Lean

/-! Exhaustive current-module audit for isolated graph artifacts. -/
open Lean Elab Command
elab "#audit_graph_module" : command => do
  let env ← getEnv
  let candidates := env.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
  let mut roots : Array Name := #[]
  for (n, ci) in candidates do
    if (env.getModuleIdxFor? n).isSome then continue
    if ci.isUnsafe then
      if (declRangeExt.find? env n).isSome then
        throwError "Unsafe source declaration {n}"
    else
      roots := roots.push n
  let mut union : NameSet := {}
  for n in roots do
    for a in (← liftCoreM (Lean.collectAxioms n)) do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "Forbidden axiom {a} in {n}"
      union := union.insert a
  logInfo m!"Graph artifact audit: {roots.size} safe roots; axioms {union.toList}"

#audit_graph_module

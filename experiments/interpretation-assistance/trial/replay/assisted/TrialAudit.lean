import Lean
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-!
# Exhaustive project axiom audit

`#audit_project_axioms` enumerates every kernel-safe declaration whose defining module is
one of the foundation modules, or lies under `SquareKit`, `Applications`, or
`Examples`. Ownership comes from Lean's module-origin table, so private names,
generated auxiliaries, instances, constructors, and recursors are included.
Candidates come from project modules' constant and generated-name metadata plus
current-module kernel declarations, with duplicate names removed. This preserves
the module-origin boundary without scanning all dependency declarations.
Definitions are audited as well as theorem declarations. The only root exclusion
is Lean's `ConstantInfo.isUnsafe` flag: the compiler creates unsafe runtime
declarations containing erased proofs (`lcProof`) and unreachable-code markers.
These are not logical declarations and cannot occur in a kernel-safe proof.
Their count is reported separately. An unsafe declaration with a registered
source range is rejected, so a user-written `unsafe` declaration is not silently
classified as a compiler artifact. No declaration-name convention is used.

Every declaration is submitted to the public `Lean.collectAxioms` API. Lean
records transitive axiom dependencies when exporting checked modules and uses
those summaries for imported declarations; local declarations are traversed
in the checked kernel environment. Every project declaration remains an audit
root, including private and generated declarations. On failure, the same API
attributes forbidden axioms to declarations.
Any transitive axiom other than `propext`, `Classical.choice`, or `Quot.sound` is an error. This
includes `sorryAx`, `Lean.ofReduceBool`, and arbitrary user-declared axioms.

The import above is the project's complete public entrypoint. Audit coverage
is over its transitive imports; adding a new source module requires importing
it from that entrypoint. The command reports the imported project modules,
all logical declaration and theorem counts, and the union of encountered axioms.
Enable `trace.ProofAudit.roots` to inspect the exact logical root set.
-/

namespace ProofAudit

open Lean Elab Command

initialize registerTraceClass `ProofAudit.roots

private def foundationModules : Array Name :=
  #[`Squares, `Compiler, `SquareCompiler, `FirstOrder, `Dependent, `Verification, `TaskSetup462]

/-- Filter module origins, never the spelling of declaration names. -/
private def isProjectModule (moduleName : Name) : Bool :=
  foundationModules.contains moduleName ||
    (`SquareKit).isPrefixOf moduleName ||
    (`Applications).isPrefixOf moduleName ||
    (`Examples).isPrefixOf moduleName

private def permittedAxiom (axiomName : Name) : Bool :=
  axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound

private def declarationModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

private structure ModuleCount where
  moduleName : Name
  declarations : Nat := 0
  theorems : Nat := 0
  runtimeDeclarations : Nat := 0

/-- An executable verification command; it adds no mathematical assumptions. -/
def auditProject : CommandElabM Unit := do
  let env ← getEnv
  let mut owned : Array (Name × ConstantInfo × Name) := #[]
  let mut counts := (env.header.moduleNames.filter isProjectModule).map
    (fun n => { moduleName := n : ModuleCount })
  if isProjectModule env.mainModule then
    counts := counts.push { moduleName := env.mainModule }
  let mut runtimeCount : Nat := 0
  let mut unsafeSource : Array Name := #[]
  -- Restrict candidates by defining module before examining declarations.
  -- Include generated-name metadata and current-module kernel declarations.
  let imported := env.header.moduleNames.mapIdx fun i n =>
    if isProjectModule n then
      let data := env.header.moduleData[i]!
      let regular := data.constants.map fun ci => (ci.name, ci)
      regular ++ data.extraConstNames.filterMap (fun name =>
        (env.constants.find? name).map fun ci => (name, ci))
    else #[]
  let candidates := env.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) imported.flatten
  let mut visited : NameSet := {}
  for (declName, info) in candidates do
    if visited.contains declName then continue
    visited := visited.insert declName
    let moduleName := declarationModule env declName
    if isProjectModule moduleName then
      -- Lean's code generator adds unsafe proof-erased runtime declarations
      -- (including axioms) to the same constant table. The kernel prevents
      -- safe proofs from using them. This is a safety-metadata boundary, not
      -- a namespace or spelling-based exemption; dependencies are unfiltered.
      -- `scripts/check.py` also rejects user-written unsafe source constructs.
      if info.isUnsafe then
        runtimeCount := runtimeCount + 1
        if (declRangeExt.find? env declName).isSome then
          unsafeSource := unsafeSource.push declName
        if let some i := counts.findIdx? (fun c => c.moduleName == moduleName) then
          counts := counts.modify i (fun c => { c with
            runtimeDeclarations := c.runtimeDeclarations + 1 })
      else
        owned := owned.push (declName, info, moduleName)
  if owned.isEmpty then
    throwError "Proof audit found no project declarations; check the public entrypoint imports."
  owned := owned.qsort (fun a b => Name.lt a.1 b.1)
  let mut theoremCount : Nat := 0
  for (declName, info, moduleName) in owned do
    trace[ProofAudit.roots] "{declName}"
    if info.isTheorem then theoremCount := theoremCount + 1
    match counts.findIdx? (fun c => c.moduleName == moduleName) with
    | some i =>
      counts := counts.modify i (fun c => { c with
        declarations := c.declarations + 1
        theorems := c.theorems + if info.isTheorem then 1 else 0 })
    | none =>
      counts := counts.push ⟨moduleName, 1, if info.isTheorem then 1 else 0, 0⟩
  -- Use Lean's public API and its checked module summaries, without relying
  -- on the collector's private implementation. Every declaration is a root.
  let mut axiomSet : NameSet := {}
  for (declName, _, _) in owned do
    for axiomName in (← Lean.collectAxioms declName) do
      axiomSet := axiomSet.insert axiomName
  let allAxioms := axiomSet.toArray.qsort Name.lt
  let forbiddenUnion := allAxioms.filter (fun a => !permittedAxiom a)
  counts := counts.qsort (fun a b => Name.lt a.moduleName b.moduleName)
  logInfo m!"Proof audit: {owned.size} kernel-safe declarations, {theoremCount} theorem declarations, {counts.size} project modules."
  for c in counts do
    logInfo m!"  {c.moduleName}: {c.declarations} logical declarations; {c.theorems} theorem declarations; {c.runtimeDeclarations} unsafe runtime declarations"
  logInfo m!"Excluded from logical roots: {runtimeCount} kernel-unsafe runtime declarations."
  logInfo m!"Transitive axiom union: {allAxioms.toList}"
  if !unsafeSource.isEmpty then
    throwError "Proof audit FAILED: unsafe declarations with source ranges: {(unsafeSource.qsort Name.lt).toList}"
  if !forbiddenUnion.isEmpty then
    let mut rejectedCount : Nat := 0
    for (declName, _, _) in owned do
      let axioms ← Lean.collectAxioms declName
      let bad := axioms.filter (fun a => !permittedAxiom a)
      if !bad.isEmpty then
        rejectedCount := rejectedCount + 1
        logError m!"Forbidden transitive axioms in '{declName}': {(bad.qsort Name.lt).toList}"
    throwError "Proof audit FAILED: {rejectedCount} declarations depend on forbidden axioms."
  logInfo "Proof audit PASSED: every kernel-safe project declaration uses only the three permitted foundational axioms."

elab "#audit_project_axioms" : command => auditProject

end ProofAudit


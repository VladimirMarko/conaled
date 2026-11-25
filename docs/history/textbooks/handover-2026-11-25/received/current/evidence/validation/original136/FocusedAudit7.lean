import Applications.Resources.RotationCertificate.TreeParserMachine
import Examples.RotationCertificateTreeParserMachine
import Applications.Resources.BinaryCounter.FixedWidthMachine
import Applications.Resources.RotationCertificate.FuelDispatchMachine
import Examples.RotationCertificateFuelMachine
import Applications.Resources.RotationCertificate.BitPairFraming
import Examples.RotationCertificateBitPairFraming
import Examples.RotationCertificateParsing
import Examples.RotationCertificateVerification
import Examples.RotationCertificateBinary
import Applications.Resources.RotationCertificate.BitDecoderMachine
import Examples.RotationCertificateBitDecoderMachine
import Lean
import Lean.Util.CollectAxioms
import Lean.DeclarationRange

/-!
# Focused binary rotation-verifier import-closure axiom audit

This is a development audit of exactly the project modules imported above.
It retains the repository ProofAudit command logic, project inventory, module
origin ownership, every safe declaration root, generated/private declarations,
unsafe source-range rejection and the three-axiom allowlist. Only the public
import boundary, explanatory heading and success-label wording differ.
It does not check the complete public entrypoint and does not replace the
required exact-candidate integrated build, exhaustive whole-library audit,
verification record or final nonrepairing candidate verification.
-/

namespace ProofAudit

open Lean Elab Command

initialize registerTraceClass `ProofAudit.roots

/-- The same inventory implementation serves the wrapper and standalone audit.
Failure to acquire it is an error, never permission to narrow audit coverage. -/
private def projectModules : IO (Array Name) := do
  let result ← IO.Process.output {
    cmd := "python3", args := #["scripts/project_sources.py"] }
  if result.exitCode != 0 then
    throw <| IO.userError s!"Cannot obtain project source inventory: {result.stderr}"
  let names ← IO.ofExcept <| fromJson? (α := Array String)
    (← IO.ofExcept <| Json.parse result.stdout)
  if names.isEmpty then
    throw <| IO.userError "Project source inventory is empty; run the audit from the project root"
  return names.map String.toName

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
  let started ← IO.monoMsNow
  let env ← getEnv
  let modules ← projectModules
  let inventoried ← IO.monoMsNow
  let moduleSet := NameSet.ofArray modules
  let isProjectModule := moduleSet.contains
  let mut owned : Array (Name × ConstantInfo × Name) := #[]
  let mut counts := (env.header.moduleNames.filter isProjectModule).map
    (fun n => { moduleName := n : ModuleCount })
  if isProjectModule env.mainModule then
    counts := counts.push { moduleName := env.mainModule }
  let mut countIndices : NameMap Nat := {}
  for (count, i) in counts.zipIdx do
    countIndices := countIndices.insert count.moduleName i
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
        if let some i := countIndices.find? moduleName then
          counts := counts.modify i (fun c => { c with
            runtimeDeclarations := c.runtimeDeclarations + 1 })
      else
        owned := owned.push (declName, info, moduleName)
  if owned.isEmpty then
    throwError "Proof audit found no project declarations; check the public entrypoint imports."
  let enumerated ← IO.monoMsNow
  owned := owned.qsort (fun a b => Name.lt a.1 b.1)
  let mut theoremCount : Nat := 0
  for (declName, info, moduleName) in owned do
    trace[ProofAudit.roots] "{declName}"
    if info.isTheorem then theoremCount := theoremCount + 1
    match countIndices.find? moduleName with
    | some i =>
      counts := counts.modify i (fun c => { c with
        declarations := c.declarations + 1
        theorems := c.theorems + if info.isTheorem then 1 else 0 })
    | none =>
      countIndices := countIndices.insert moduleName counts.size
      counts := counts.push ⟨moduleName, 1, if info.isTheorem then 1 else 0, 0⟩
  let counted ← IO.monoMsNow
  -- Use Lean's public API and its checked module summaries, without relying
  -- on the collector's private implementation. Every declaration is a root.
  let mut axiomSet : NameSet := {}
  for (declName, _, _) in owned do
    for axiomName in (← Lean.collectAxioms declName) do
      axiomSet := axiomSet.insert axiomName
  let allAxioms := axiomSet.toArray.qsort Name.lt
  let forbiddenUnion := allAxioms.filter (fun a => !permittedAxiom a)
  let collected ← IO.monoMsNow
  counts := counts.qsort (fun a b => Name.lt a.moduleName b.moduleName)
  logInfo m!"Proof audit: {owned.size} kernel-safe declarations, {theoremCount} theorem declarations, {counts.size} project modules."
  for c in counts do
    logInfo m!"  {c.moduleName}: {c.declarations} logical declarations; {c.theorems} theorem declarations; {c.runtimeDeclarations} unsafe runtime declarations"
  logInfo m!"Excluded from logical roots: {runtimeCount} kernel-unsafe runtime declarations."
  logInfo m!"Transitive axiom union: {allAxioms.toList}"
  let reported ← IO.monoMsNow
  logInfo m!"Proof audit timings (ms): inventory={inventoried - started} roots={enumerated - inventoried} counting={counted - enumerated} axioms={collected - counted} reporting={reported - collected} total={reported - started}"
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
  logInfo "Focused proof audit PASSED: every kernel-safe declaration in the imported project closure uses only the three permitted foundational axioms."

elab "#audit_project_axioms" : command => auditProject

end ProofAudit

#audit_project_axioms

/-! Actual elaborated public contracts for statement review. -/
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#check @Resources.RotationCertificate.checkStreamRun
#check @Resources.RotationCertificate.checkStreamRun_iff
#check @Resources.RotationCertificate.checkStreamRun_cost_le
#check @Resources.RotationCertificate.certCode_length_le_of_applyMoves
#check @Resources.RotationCertificate.minimum_certificate_bound
#check @Resources.RotationCertificate.Yes
#check @Resources.RotationCertificate.yes_iff_trace
#check @Resources.RotationCertificate.yes_small_trace
#check @Resources.RotationCertificate.verifyRun
#check @Resources.RotationCertificate.verifyRun_accept_iff
#check @Resources.RotationCertificate.verifyRun_sound
#check @Resources.RotationCertificate.verifyRun_complete_small
#check @Resources.RotationCertificate.verifyRun_work_all
#check @Resources.RotationCertificate.verifyRun_emit_trace

/-! Additional fixed-bit and binary-verifier contracts. -/
#check @Resources.RotationCertificate.tagBits_value
#check @Resources.RotationCertificate.wordBits_length
#check @Resources.RotationCertificate.packWordRun_eq
#check @Resources.RotationCertificate.decodeTagRun_value
#check @Resources.RotationCertificate.unpackWordRun_prefix
#check @Resources.RotationCertificate.unpackWordRun_iff
#check @Resources.RotationCertificate.unpackWordRun_none_iff
#check @Resources.RotationCertificate.unpackWordRun_partial
#check @Resources.RotationCertificate.unpackWordRun_cost_le
#check @Resources.RotationCertificate.pack_unpack_eq
#check @Resources.RotationCertificate.packWordRun_of_unpacked
#check @Resources.RotationCertificate.emitPackedInputRun_eq
#check @Resources.RotationCertificate.emitPackedCertificateRun_eq
#check @Resources.RotationCertificate.verifyBitsRun
#check @Resources.RotationCertificate.verifyBitsRun_code_value
#check @Resources.RotationCertificate.verifyBitsRun_accept_iff
#check @Resources.RotationCertificate.verifyBitsRun_accept_iff_trace
#check @Resources.RotationCertificate.BinaryYes
#check @Resources.RotationCertificate.verifyBitsRun_sound
#check @Resources.RotationCertificate.verifyBitsRun_complete_small
#check @Resources.RotationCertificate.binaryYes_iff_exists_certificate
#check @Resources.RotationCertificate.verifyBitsRun_work_all
#check @Resources.RotationCertificate.verifyBitsRun_packed_value
#check @Resources.RotationCertificate.verifyBitsRun_emit_trace

/-!
Finite decoder component: print the actual finite control, callbacks, program,
result representation, time evidence and stack-cell potential. These declarations
concern the decoder component; they do not claim a complete verifier machine or
the remaining source-required NP correspondence. The audit logic above is
unchanged from FocusedAudit3, including every root and all rejection checks.
-/
#print Resources.RotationCertificate.BitDecoderMachine.StackId
#print Resources.RotationCertificate.BitDecoderMachine.Label
#print Resources.RotationCertificate.BitDecoderMachine.alphabet
#print Resources.RotationCertificate.BitDecoderMachine.alphabetFintype
#print Resources.RotationCertificate.BitDecoderMachine.Registers
#print Resources.RotationCertificate.BitDecoderMachine.zeroRegisters
#print Resources.RotationCertificate.BitDecoderMachine.resultCode
#print Resources.RotationCertificate.BitDecoderMachine.Statement
#print Resources.RotationCertificate.BitDecoderMachine.store0
#print Resources.RotationCertificate.BitDecoderMachine.store1
#print Resources.RotationCertificate.BitDecoderMachine.store2
#print Resources.RotationCertificate.BitDecoderMachine.store3
#print Resources.RotationCertificate.BitDecoderMachine.storeTag
#print Resources.RotationCertificate.BitDecoderMachine.nibble
#print Resources.RotationCertificate.BitDecoderMachine.jump
#print Resources.RotationCertificate.BitDecoderMachine.finish
#print Resources.RotationCertificate.BitDecoderMachine.program
#print Resources.RotationCertificate.BitDecoderMachine.machine
#print Resources.RotationCertificate.BitDecoderMachine.cfg
#print Resources.RotationCertificate.BitDecoderMachine.next
#print Resources.RotationCertificate.BitDecoderMachine.runSteps
#print Resources.RotationCertificate.BitDecoderMachine.outputsInTimeExact
#print Resources.RotationCertificate.BitDecoderMachine.outputsInTime
#print Resources.RotationCertificate.BitDecoderMachine.computableInPolyTime
#print Resources.RotationCertificate.BitDecoderMachine.stackCells
#print Resources.RotationCertificate.BitDecoderMachine.credit
#print Resources.RotationCertificate.BitDecoderMachine.potential

/-! Finite instances for every control and stack-alphabet carrier. -/
#synth Fintype Resources.RotationCertificate.BitDecoderMachine.StackId
#synth Fintype Resources.RotationCertificate.BitDecoderMachine.Label
#synth Fintype Resources.RotationCertificate.BitDecoderMachine.Registers
#synth Fintype (Resources.RotationCertificate.BitDecoderMachine.alphabet Resources.RotationCertificate.BitDecoderMachine.StackId.input)
#synth Fintype (Resources.RotationCertificate.BitDecoderMachine.alphabet Resources.RotationCertificate.BitDecoderMachine.StackId.reverse)
#synth Fintype (Resources.RotationCertificate.BitDecoderMachine.alphabet Resources.RotationCertificate.BitDecoderMachine.StackId.output)

/-! Finite alphabets and injective result encoding. -/
#check @Resources.RotationCertificate.BitDecoderMachine.alphabetFintype
#check @Resources.RotationCertificate.BitDecoderMachine.resultCode_injective

/-! Actual initialized, halted and arbitrary-state transition configurations. -/
#check @Resources.RotationCertificate.BitDecoderMachine.cfg_eta
#check @Resources.RotationCertificate.BitDecoderMachine.initList_eq
#check @Resources.RotationCertificate.BitDecoderMachine.haltList_eq
#check @Resources.RotationCertificate.BitDecoderMachine.scan_step_block
#check @Resources.RotationCertificate.BitDecoderMachine.scan_step_nil
#check @Resources.RotationCertificate.BitDecoderMachine.scan_step_one
#check @Resources.RotationCertificate.BitDecoderMachine.scan_step_two
#check @Resources.RotationCertificate.BitDecoderMachine.scan_step_three
#check @Resources.RotationCertificate.BitDecoderMachine.emit_step_cons
#check @Resources.RotationCertificate.BitDecoderMachine.emit_step_nil
#check @Resources.RotationCertificate.BitDecoderMachine.clear_step_cons
#check @Resources.RotationCertificate.BitDecoderMachine.clear_step_nil
#check @Resources.RotationCertificate.BitDecoderMachine.halt_step
#check @Resources.RotationCertificate.BitDecoderMachine.next_none
#check @Resources.RotationCertificate.BitDecoderMachine.next_some

/-! Generalized phase execution with arbitrary accumulators and output suffixes. -/
#check @Resources.RotationCertificate.BitDecoderMachine.emit_iterate
#check @Resources.RotationCertificate.BitDecoderMachine.clear_iterate
#check @Resources.RotationCertificate.BitDecoderMachine.scan_iterate

/-! Every-raw exact transition count, linear timing, polynomial record and cleanup. -/
#check @Resources.RotationCertificate.BitDecoderMachine.machine_run
#check @Resources.RotationCertificate.BitDecoderMachine.runSteps_le
#check @Resources.RotationCertificate.BitDecoderMachine.outputsInTimeExact
#check @Resources.RotationCertificate.BitDecoderMachine.outputsInTime
#check @Resources.RotationCertificate.BitDecoderMachine.computableInPolyTime
#check @Resources.RotationCertificate.BitDecoderMachine.machine_run_code
#check @Resources.RotationCertificate.BitDecoderMachine.machine_run_partial

/-! Actual-step and reached-configuration workspace. -/
#check @Resources.RotationCertificate.BitDecoderMachine.step_potential_le
#check @Resources.RotationCertificate.BitDecoderMachine.reaches_potential_le
#check @Resources.RotationCertificate.BitDecoderMachine.reachable_stackCells_le

/-!
All named connected decoder-machine clients. Besides literals, these preserve
arbitrary inputs, registers, accumulated tags, output suffixes and reached
configurations, and consume the actual timing and polynomial records.
-/
#check @Examples.RotationCertificateBitDecoderMachine.encoded_results_are_equal_exactly_when_results_are_equal
#check @Examples.RotationCertificateBitDecoderMachine.rejection_and_empty_success_have_distinct_codes
#check @Examples.RotationCertificateBitDecoderMachine.empty_input_halts_with_the_success_marker
#check @Examples.RotationCertificateBitDecoderMachine.every_short_input_halts_with_rejection
#check @Examples.RotationCertificateBitDecoderMachine.every_four_bit_block_reaches_its_payload
#check @Examples.RotationCertificateBitDecoderMachine.literal_endian_blocks
#check @Examples.RotationCertificateBitDecoderMachine.literal_zero_and_reserved_blocks
#check @Examples.RotationCertificateBitDecoderMachine.reserved_tags_survive_in_order
#check @Examples.RotationCertificateBitDecoderMachine.two_literal_blocks_keep_their_order
#check @Examples.RotationCertificateBitDecoderMachine.three_nonpalindromic_blocks_keep_their_order
#check @Examples.RotationCertificateBitDecoderMachine.a_zero_block_is_not_an_empty_word
#check @Examples.RotationCertificateBitDecoderMachine.high_zero_blocks_retain_their_width
#check @Examples.RotationCertificateBitDecoderMachine.two_zero_blocks_both_survive
#check @Examples.RotationCertificateBitDecoderMachine.every_partial_ending_clears_the_whole_prefix
#check @Examples.RotationCertificateBitDecoderMachine.one_and_two_completed_blocks_are_cleared
#check @Examples.RotationCertificateBitDecoderMachine.initialization_carries_no_precomputed_answer
#check @Examples.RotationCertificateBitDecoderMachine.one_tag_failure_has_four_visible_transitions
#check @Examples.RotationCertificateBitDecoderMachine.stale_registers_do_not_change_the_next_complete_block
#check @Examples.RotationCertificateBitDecoderMachine.already_accumulated_tags_precede_a_decoded_suffix
#check @Examples.RotationCertificateBitDecoderMachine.an_incomplete_suffix_clears_arbitrary_old_tags
#check @Examples.RotationCertificateBitDecoderMachine.emitting_preserves_an_arbitrary_output_suffix
#check @Examples.RotationCertificateBitDecoderMachine.clearing_preserves_an_arbitrary_output_suffix
#check @Examples.RotationCertificateBitDecoderMachine.every_machine_stack_has_a_finite_alphabet
#check @Examples.RotationCertificateBitDecoderMachine.each_reachable_stack_has_a_linear_bound
#check @Examples.RotationCertificateBitDecoderMachine.empty_success_requires_the_extra_workspace_cell
#check @Examples.RotationCertificateBitDecoderMachine.a_post_halt_step_discards_the_actual_result
#check @Examples.RotationCertificateBitDecoderMachine.empty_success_is_present_before_the_post_halt_step
#check @Examples.RotationCertificateBitDecoderMachine.identity_machine_reaches_outer_none
#check @Examples.RotationCertificateBitDecoderMachine.identity_outer_none_does_not_mean_empty_rejection
#check @Examples.RotationCertificateBitDecoderMachine.source_work_and_machine_steps_are_distinct
#check @Examples.RotationCertificateBitDecoderMachine.every_raw_input_has_an_actual_linear_run
#check @Examples.RotationCertificateBitDecoderMachine.every_raw_input_has_the_declared_transition_count
#check @Examples.RotationCertificateBitDecoderMachine.every_raw_input_uses_one_polynomial_machine
#check @Examples.RotationCertificateBitDecoderMachine.encoded_words_use_the_polynomial_machine

/-! Strict pair-framing contract inspection is appended below for the complete first attempted API.
This prepared audit is unrun; the existing decoder audit body and all prior checks remain unchanged. -/

/-! Strict framing actual definitions: parser, finite control, encodings, quantitative records and source client. -/
#print Resources.RotationCertificate.BitPairFraming.escapeBits
#print Resources.RotationCertificate.BitPairFraming.frame
#print Resources.RotationCertificate.BitPairFraming.unframe
#print Resources.RotationCertificate.BitPairFraming.resultCode
#print Resources.RotationCertificate.BitPairFraming.StackId
#print Resources.RotationCertificate.BitPairFraming.Label
#print Resources.RotationCertificate.BitPairFraming.Registers
#print Resources.RotationCertificate.BitPairFraming.zeroRegisters
#print Resources.RotationCertificate.BitPairFraming.alphabet
#print Resources.RotationCertificate.BitPairFraming.alphabetFintype
#print Resources.RotationCertificate.BitPairFraming.Statement
#print Resources.RotationCertificate.BitPairFraming.store
#print Resources.RotationCertificate.BitPairFraming.jump
#print Resources.RotationCertificate.BitPairFraming.finish
#print Resources.RotationCertificate.BitPairFraming.program
#print Resources.RotationCertificate.BitPairFraming.machine
#print Resources.RotationCertificate.BitPairFraming.cfg
#print Resources.RotationCertificate.BitPairFraming.next
#print Resources.RotationCertificate.BitPairFraming.runSteps
#print Resources.RotationCertificate.BitPairFraming.outputsInTimeExact
#print Resources.RotationCertificate.BitPairFraming.outputsInTime
#print Resources.RotationCertificate.BitPairFraming.computableInPolyTime
#print Resources.RotationCertificate.BitPairFraming.stackCells
#print Resources.RotationCertificate.BitPairFraming.credit
#print Resources.RotationCertificate.BitPairFraming.potential
#print Resources.RotationCertificate.BitPairFraming.verifyFramed
#print Resources.RotationCertificate.BitPairFraming.outputsInTime_small

/-! Every finite control and stack-alphabet carrier. -/
#synth Fintype Resources.RotationCertificate.BitPairFraming.StackId
#synth Fintype Resources.RotationCertificate.BitPairFraming.Label
#synth Fintype Resources.RotationCertificate.BitPairFraming.Registers
#synth Fintype (Resources.RotationCertificate.BitPairFraming.alphabet Resources.RotationCertificate.BitPairFraming.StackId.input)
#synth Fintype (Resources.RotationCertificate.BitPairFraming.alphabet Resources.RotationCertificate.BitPairFraming.StackId.firstReverse)
#synth Fintype (Resources.RotationCertificate.BitPairFraming.alphabet Resources.RotationCertificate.BitPairFraming.StackId.certReverse)
#synth Fintype (Resources.RotationCertificate.BitPairFraming.alphabet Resources.RotationCertificate.BitPairFraming.StackId.output)

/-! Actual elaborated framing contracts, including full raw domains and arbitrary suffix hypotheses. -/
#check @Resources.RotationCertificate.BitPairFraming.escapeBits_nil
#check @Resources.RotationCertificate.BitPairFraming.escapeBits_cons
#check @Resources.RotationCertificate.BitPairFraming.frame_nil
#check @Resources.RotationCertificate.BitPairFraming.frame_cons
#check @Resources.RotationCertificate.BitPairFraming.escapeBits_length
#check @Resources.RotationCertificate.BitPairFraming.escapeBits_append
#check @Resources.RotationCertificate.BitPairFraming.frame_length
#check @Resources.RotationCertificate.BitPairFraming.frame_append
#check @Resources.RotationCertificate.BitPairFraming.unframe_nil
#check @Resources.RotationCertificate.BitPairFraming.unframe_true
#check @Resources.RotationCertificate.BitPairFraming.unframe_false_nil
#check @Resources.RotationCertificate.BitPairFraming.unframe_false_cons
#check @Resources.RotationCertificate.BitPairFraming.unframe_escape_append
#check @Resources.RotationCertificate.BitPairFraming.unframe_frame
#check @Resources.RotationCertificate.BitPairFraming.unframe_iff
#check @Resources.RotationCertificate.BitPairFraming.unframe_missing_delimiter
#check @Resources.RotationCertificate.BitPairFraming.unframe_incomplete_guard
#check @Resources.RotationCertificate.BitPairFraming.unframe_none_iff
#check @Resources.RotationCertificate.BitPairFraming.frame_injective
#check @Resources.RotationCertificate.BitPairFraming.resultCode_injective
#check @Resources.RotationCertificate.BitPairFraming.resultCode_length
#check @Resources.RotationCertificate.BitPairFraming.cfg_eta
#check @Resources.RotationCertificate.BitPairFraming.initList_eq
#check @Resources.RotationCertificate.BitPairFraming.haltList_eq
#check @Resources.RotationCertificate.BitPairFraming.scanPrefix_step_nil
#check @Resources.RotationCertificate.BitPairFraming.scanPrefix_step_false_nil
#check @Resources.RotationCertificate.BitPairFraming.scanPrefix_step_false_cons
#check @Resources.RotationCertificate.BitPairFraming.scanPrefix_step_true
#check @Resources.RotationCertificate.BitPairFraming.copyCert_step_cons
#check @Resources.RotationCertificate.BitPairFraming.copyCert_step_nil
#check @Resources.RotationCertificate.BitPairFraming.emitCert_step_cons
#check @Resources.RotationCertificate.BitPairFraming.emitCert_step_nil
#check @Resources.RotationCertificate.BitPairFraming.emitFirst_step_cons
#check @Resources.RotationCertificate.BitPairFraming.emitFirst_step_nil
#check @Resources.RotationCertificate.BitPairFraming.clearFirst_step_cons
#check @Resources.RotationCertificate.BitPairFraming.clearFirst_step_nil
#check @Resources.RotationCertificate.BitPairFraming.halt_step
#check @Resources.RotationCertificate.BitPairFraming.next_none
#check @Resources.RotationCertificate.BitPairFraming.next_some
#check @Resources.RotationCertificate.BitPairFraming.emitFirst_iterate
#check @Resources.RotationCertificate.BitPairFraming.clearFirst_iterate
#check @Resources.RotationCertificate.BitPairFraming.emitCert_iterate
#check @Resources.RotationCertificate.BitPairFraming.copyCert_iterate
#check @Resources.RotationCertificate.BitPairFraming.scanPrefix_iterate
#check @Resources.RotationCertificate.BitPairFraming.runSteps_escape_append
#check @Resources.RotationCertificate.BitPairFraming.runSteps_frame
#check @Resources.RotationCertificate.BitPairFraming.runSteps_missing_delimiter
#check @Resources.RotationCertificate.BitPairFraming.runSteps_incomplete_guard
#check @Resources.RotationCertificate.BitPairFraming.runSteps_le
#check @Resources.RotationCertificate.BitPairFraming.machine_run
#check @Resources.RotationCertificate.BitPairFraming.machine_run_frame
#check @Resources.RotationCertificate.BitPairFraming.machine_run_missing_delimiter
#check @Resources.RotationCertificate.BitPairFraming.machine_run_incomplete_guard
#check @Resources.RotationCertificate.BitPairFraming.step_potential_le
#check @Resources.RotationCertificate.BitPairFraming.reaches_potential_le
#check @Resources.RotationCertificate.BitPairFraming.reachable_stackCells_le
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_frame
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_accept_iff
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_accept_iff_trace
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_sound
#check @Resources.RotationCertificate.BitPairFraming.binaryYes_iff_exists_framed_certificate
#check @Resources.RotationCertificate.BitPairFraming.frame_length_le_square
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_complete_small
#check @Resources.RotationCertificate.BitPairFraming.runSteps_frame_le_square
#check @Resources.RotationCertificate.BitPairFraming.reachable_framed_stackCells_le
#check @Resources.RotationCertificate.BitPairFraming.verifyFramed_emit_trace
#check @Resources.RotationCertificate.BitPairFraming.alphabetFintype
#check @Resources.RotationCertificate.BitPairFraming.outputsInTimeExact
#check @Resources.RotationCertificate.BitPairFraming.outputsInTime
#check @Resources.RotationCertificate.BitPairFraming.computableInPolyTime
#check @Resources.RotationCertificate.BitPairFraming.outputsInTime_small

/-! All connected strict pair-framing clients, including the single chosen witness and source-work separation. -/
#check @Examples.RotationCertificateBitPairFraming.frame_equality_recovers_both_coordinates
#check @Examples.RotationCertificateBitPairFraming.result_codes_recover_the_complete_result
#check @Examples.RotationCertificateBitPairFraming.failure_and_empty_pair_have_distinct_codes
#check @Examples.RotationCertificateBitPairFraming.the_output_separator_preserves_coordinate_order
#check @Examples.RotationCertificateBitPairFraming.raw_success_recovers_every_original_bit
#check @Examples.RotationCertificateBitPairFraming.every_malformed_prefix_is_rejected_and_cleared
#check @Examples.RotationCertificateBitPairFraming.arbitrary_raw_failure_has_a_missing_delimiter
#check @Examples.RotationCertificateBitPairFraming.an_escaped_prefix_cannot_repair_a_failed_suffix
#check @Examples.RotationCertificateBitPairFraming.eof_and_a_lone_false_guard_reject
#check @Examples.RotationCertificateBitPairFraming.a_guarded_payload_still_requires_its_delimiter
#check @Examples.RotationCertificateBitPairFraming.a_true_flag_retains_every_certificate_bit
#check @Examples.RotationCertificateBitPairFraming.opposite_coordinates_produce_opposite_outputs
#check @Examples.RotationCertificateBitPairFraming.nonpalindromic_coordinates_keep_their_order
#check @Examples.RotationCertificateBitPairFraming.appending_extends_exactly_the_certificate
#check @Examples.RotationCertificateBitPairFraming.valid_frames_can_be_strict_prefixes_of_other_valid_frames
#check @Examples.RotationCertificateBitPairFraming.zero_width_in_either_coordinate_is_observable
#check @Examples.RotationCertificateBitPairFraming.initialization_contains_no_precomputed_pair
#check @Examples.RotationCertificateBitPairFraming.stale_registers_cannot_supply_a_missing_flag_or_value
#check @Examples.RotationCertificateBitPairFraming.stale_registers_do_not_confuse_true_payload_and_delimiter
#check @Examples.RotationCertificateBitPairFraming.escaped_true_failure_has_four_visible_transitions
#check @Examples.RotationCertificateBitPairFraming.accumulated_first_bits_precede_the_new_pair
#check @Examples.RotationCertificateBitPairFraming.a_failed_suffix_clears_old_first_bits_and_preserves_old_output
#check @Examples.RotationCertificateBitPairFraming.emitting_first_bits_preserves_an_arbitrary_output_suffix
#check @Examples.RotationCertificateBitPairFraming.emitting_both_coordinates_preserves_an_arbitrary_output_suffix
#check @Examples.RotationCertificateBitPairFraming.copying_retains_old_certificate_bits_before_the_raw_suffix
#check @Examples.RotationCertificateBitPairFraming.clearing_preserves_an_arbitrary_output_suffix
#check @Examples.RotationCertificateBitPairFraming.clearing_does_not_erase_an_unrelated_certificate_stack
#check @Examples.RotationCertificateBitPairFraming.every_work_alphabet_is_finite
#check @Examples.RotationCertificateBitPairFraming.the_empty_pair_has_four_visible_transitions
#check @Examples.RotationCertificateBitPairFraming.the_empty_pair_requires_the_extra_workspace_cell
#check @Examples.RotationCertificateBitPairFraming.every_reachable_stack_obeys_the_uniform_space_bound
#check @Examples.RotationCertificateBitPairFraming.a_step_past_the_halted_result_returns_outer_none
#check @Examples.RotationCertificateBitPairFraming.failure_and_empty_success_are_present_before_outer_none
#check @Examples.RotationCertificateBitPairFraming.certificate_only_frames_attain_the_linear_transition_bound
#check @Examples.RotationCertificateBitPairFraming.every_raw_input_has_an_actual_linear_run
#check @Examples.RotationCertificateBitPairFraming.every_raw_input_uses_one_polynomial_machine
#check @Examples.RotationCertificateBitPairFraming.framed_pairs_use_the_constructed_polynomial_record
#check @Examples.RotationCertificateBitPairFraming.returned_fields_feed_the_existing_verifier
#check @Examples.RotationCertificateBitPairFraming.an_empty_first_coordinate_is_valid_framing_but_fails_verification
#check @Examples.RotationCertificateBitPairFraming.actual_packed_emitters_feed_framing_decoding_and_acceptance
#check @Examples.RotationCertificateBitPairFraming.one_rotation_emitter_values
#check @Examples.RotationCertificateBitPairFraming.one_rotation_coordinate_lengths
#check @Examples.RotationCertificateBitPairFraming.one_rotation_verifier_observation
#check @Examples.RotationCertificateBitPairFraming.one_rotation_framing_has_the_expected_size_time_and_output
#check @Examples.RotationCertificateBitPairFraming.an_appended_certificate_bit_remains_framed_but_fails_the_verifier
#check @Examples.RotationCertificateBitPairFraming.binary_source_work_is_bounded_by_the_framed_length
#check @Examples.RotationCertificateBitPairFraming.a_single_small_witness_has_acceptance_time_and_space
#check @Examples.RotationCertificateBitPairFraming.the_one_rotation_witness_client_is_nonvacuous

/-! Actual emitter-backed input, certificate, and constructed framing evidence. -/
#print Examples.RotationCertificateBitPairFraming.oneRotationInput
#print Examples.RotationCertificateBitPairFraming.oneRotationCertificate
#print Examples.RotationCertificateBitPairFraming.framed_pairs_use_the_constructed_polynomial_record


/-!
Round6 preparation: actual named public source contracts and finite component
bodies, selected from the three current first-attempt owners. This instrument
retains the entire Audit5 body above byte-for-byte. It is supplementary imported
closure inspection; the original full validation and review obligations remain.
The preparation metadata records selection identities. Execute only after
matching normal producer/client success and a frozen candidate/input binding.
-/

/-! All named public declarations from Applications/Resources/BinaryCounter/FixedWidthMachine.lean. -/
#check @Resources.BinaryCounter.FixedWidthMachine.Result
#check @Resources.BinaryCounter.FixedWidthMachine.PredSpec
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_first_true
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_replicate_false
#check @Resources.BinaryCounter.FixedWidthMachine.bitWord_cases
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_spec
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_iff
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_source
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_of_none
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_positive_iff
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_zero_iff
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_width
#check @Resources.BinaryCounter.FixedWidthMachine.predSpec_positive_value
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps_pos
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps_first_true
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps_replicate_false
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps_le
#check @Resources.BinaryCounter.FixedWidthMachine.runSteps_le_source_cost
#check @Resources.BinaryCounter.FixedWidthMachine.LocalStack
#check @Resources.BinaryCounter.FixedWidthMachine.Phase
#check @Resources.BinaryCounter.FixedWidthMachine.StackId
#check @Resources.BinaryCounter.FixedWidthMachine.External
#check @Resources.BinaryCounter.FixedWidthMachine.Label
#check @Resources.BinaryCounter.FixedWidthMachine.Registers
#check @Resources.BinaryCounter.FixedWidthMachine.alphabet
#check @Resources.BinaryCounter.FixedWidthMachine.alphabetFintype
#check @Resources.BinaryCounter.FixedWidthMachine.Statement
#check @Resources.BinaryCounter.FixedWidthMachine.Cfg
#check @Resources.BinaryCounter.FixedWidthMachine.phaseLabel
#check @Resources.BinaryCounter.FixedWidthMachine.resultLabel
#check @Resources.BinaryCounter.FixedWidthMachine.callerLabel
#check @Resources.BinaryCounter.FixedWidthMachine.reset
#check @Resources.BinaryCounter.FixedWidthMachine.storeBit
#check @Resources.BinaryCounter.FixedWidthMachine.storeBorrowed
#check @Resources.BinaryCounter.FixedWidthMachine.jump
#check @Resources.BinaryCounter.FixedWidthMachine.block
#check @Resources.BinaryCounter.FixedWidthMachine.program
#check @Resources.BinaryCounter.FixedWidthMachine.program_eq_of_agrees
#check @Resources.BinaryCounter.FixedWidthMachine.cfg
#check @Resources.BinaryCounter.FixedWidthMachine.cfg_ext
#check @Resources.BinaryCounter.FixedWidthMachine.cfg_eta
#check @Resources.BinaryCounter.FixedWidthMachine.step
#check @Resources.BinaryCounter.FixedWidthMachine.next
#check @Resources.BinaryCounter.FixedWidthMachine.next_none
#check @Resources.BinaryCounter.FixedWidthMachine.next_some
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_step_false
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_step_true
#check @Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil
#check @Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons
#check @Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil
#check @Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons
#check @Resources.BinaryCounter.FixedWidthMachine.iterate_step
#check @Resources.BinaryCounter.FixedWidthMachine.restoreTrue_iterate
#check @Resources.BinaryCounter.FixedWidthMachine.restoreFalse_iterate
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_first_true_iterate
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_zero_iterate
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_iterate
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_run
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_run_first_true
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_run_replicate_false
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_run_of_some
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_run_of_none
#check @Resources.BinaryCounter.FixedWidthMachine.borrowInTime
#check @Resources.BinaryCounter.FixedWidthMachine.borrowInLinearTime
#check @Resources.BinaryCounter.FixedWidthMachine.Owned
#check @Resources.BinaryCounter.FixedWidthMachine.phaseSteps
#check @Resources.BinaryCounter.FixedWidthMachine.remainingSteps
#check @Resources.BinaryCounter.FixedWidthMachine.remainingSteps_pos_iff
#check @Resources.BinaryCounter.FixedWidthMachine.owned_cases
#check @Resources.BinaryCounter.FixedWidthMachine.phase_step_data
#check @Resources.BinaryCounter.FixedWidthMachine.LocalStep
#check @Resources.BinaryCounter.FixedWidthMachine.local_step_data
#check @Resources.BinaryCounter.FixedWidthMachine.local_step_remaining
#check @Resources.BinaryCounter.FixedWidthMachine.local_progress
#check @Resources.BinaryCounter.FixedWidthMachine.step_caller_independent
#check @Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
#check @Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
#check @Resources.BinaryCounter.FixedWidthMachine.prefix_local_register
#check @Resources.BinaryCounter.FixedWidthMachine.phase_prefix
#check @Resources.BinaryCounter.FixedWidthMachine.phase_prefix_caller_independent
#check @Resources.BinaryCounter.FixedWidthMachine.stackCells
#check @Resources.BinaryCounter.FixedWidthMachine.local_step_preserves
#check @Resources.BinaryCounter.FixedWidthMachine.local_reaches_preserves
#check @Resources.BinaryCounter.FixedWidthMachine.FuelRepresents
#check @Resources.BinaryCounter.FixedWidthMachine.fuelRepresents_step
#check @Resources.BinaryCounter.FixedWidthMachine.fuelRepresents_reaches
#check @Resources.BinaryCounter.FixedWidthMachine.borrow_prefix_represents

/-! All named public declarations from Applications/Resources/RotationCertificate/FuelDispatchMachine.lean. -/
#check @Resources.RotationCertificate.FuelDispatchMachine.DispatchLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.Exit
#check @Resources.RotationCertificate.FuelDispatchMachine.Protected
#check @Resources.RotationCertificate.FuelDispatchMachine.ExtraLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.Label
#check @Resources.RotationCertificate.FuelDispatchMachine.Registers
#check @Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet
#check @Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabetFintype
#check @Resources.RotationCertificate.FuelDispatchMachine.Statement
#check @Resources.RotationCertificate.FuelDispatchMachine.Cfg
#check @Resources.RotationCertificate.FuelDispatchMachine.inspectLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.atEndLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.positiveLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.zeroLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.callerLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.exitLabel
#check @Resources.RotationCertificate.FuelDispatchMachine.exitOfResult
#check @Resources.RotationCertificate.FuelDispatchMachine.exitLabel_result
#check @Resources.RotationCertificate.FuelDispatchMachine.storePresence
#check @Resources.RotationCertificate.FuelDispatchMachine.inspectBlock
#check @Resources.RotationCertificate.FuelDispatchMachine.callerHandler
#check @Resources.RotationCertificate.FuelDispatchMachine.program
#check @Resources.RotationCertificate.FuelDispatchMachine.program_eq_of_agrees
#check @Resources.RotationCertificate.FuelDispatchMachine.stores
#check @Resources.RotationCertificate.FuelDispatchMachine.cfg
#check @Resources.RotationCertificate.FuelDispatchMachine.step
#check @Resources.RotationCertificate.FuelDispatchMachine.next
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_step_nil
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_step_cons
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchSpec
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchSteps
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_nil
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_cons
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_first_true
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_replicate_false
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_of_some
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_run_of_none
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchSteps_le
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchSteps_le_source_cost
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchInTime
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatchInLinearTime
#check @Resources.RotationCertificate.FuelDispatchMachine.checkStreamRun_of_fuel
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_zero_stream
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_positive_stream
#check @Resources.RotationCertificate.FuelDispatchMachine.cfg_eta
#check @Resources.RotationCertificate.FuelDispatchMachine.Owned
#check @Resources.RotationCertificate.FuelDispatchMachine.LocalStep
#check @Resources.RotationCertificate.FuelDispatchMachine.remainingSteps
#check @Resources.RotationCertificate.FuelDispatchMachine.remainingSteps_core
#check @Resources.RotationCertificate.FuelDispatchMachine.remainingSteps_pos_iff
#check @Resources.RotationCertificate.FuelDispatchMachine.core_owned_not_inspect
#check @Resources.RotationCertificate.FuelDispatchMachine.core_step_not_inspect
#check @Resources.RotationCertificate.FuelDispatchMachine.inspection_cases
#check @Resources.RotationCertificate.FuelDispatchMachine.local_step_remaining
#check @Resources.RotationCertificate.FuelDispatchMachine.local_step_register
#check @Resources.RotationCertificate.FuelDispatchMachine.local_progress
#check @Resources.RotationCertificate.FuelDispatchMachine.step_caller_independent
#check @Resources.RotationCertificate.FuelDispatchMachine.stackCells
#check @Resources.RotationCertificate.FuelDispatchMachine.local_step_preserves
#check @Resources.RotationCertificate.FuelDispatchMachine.local_reaches_preserves
#check @Resources.RotationCertificate.FuelDispatchMachine.prefix_local_register
#check @Resources.RotationCertificate.FuelDispatchMachine.remainingSteps_inspect
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_prefix
#check @Resources.RotationCertificate.FuelDispatchMachine.dispatch_prefix_caller_independent

/-! All named public declarations from Examples/RotationCertificateFuelMachine.lean. -/
#check @Examples.RotationCertificateFuelMachine.Core.first_true_preserves_arbitrary_higher_bits
#check @Examples.RotationCertificateFuelMachine.Core.zero_restores_its_supplied_width
#check @Examples.RotationCertificateFuelMachine.Core.literal_zero_widths_remain_distinct
#check @Examples.RotationCertificateFuelMachine.Core.one_and_high_zero_one_keep_different_widths
#check @Examples.RotationCertificateFuelMachine.Core.two_and_four_borrow_before_the_first_true
#check @Examples.RotationCertificateFuelMachine.Core.twenty_to_nineteen_preserves_nonpalindromic_high_bits
#check @Examples.RotationCertificateFuelMachine.Core.later_failure_observes_the_retained_high_zeros
#check @Examples.RotationCertificateFuelMachine.Core.actual_returned_word_has_the_source_width_and_value
#check @Examples.RotationCertificateFuelMachine.Core.restore_true_prepends_to_arbitrary_existing_fuel
#check @Examples.RotationCertificateFuelMachine.Core.restore_false_prepends_to_arbitrary_existing_fuel
#check @Examples.RotationCertificateFuelMachine.Core.arbitrary_scratch_records_the_logical_low_zero_prefix
#check @Examples.RotationCertificateFuelMachine.Core.existing_tokens_count_only_the_remaining_restore_work
#check @Examples.RotationCertificateFuelMachine.Core.one_pending_token_cannot_be_ignored
#check @Examples.RotationCertificateFuelMachine.Core.eof_and_scratch_eof_ignore_stale_local_registers
#check @Examples.RotationCertificateFuelMachine.Core.restored_failure_has_actual_intermediate_cells
#check @Examples.RotationCertificateFuelMachine.Core.primitive_time_is_bounded_without_decoding_a_natural
#check @Examples.RotationCertificateFuelMachine.Core.actual_uniform_borrow_time
#check @Examples.RotationCertificateFuelMachine.Core.successful_borrow_keeps_the_old_high_suffix_at_each_stage
#check @Examples.RotationCertificateFuelMachine.Core.independently_presented_programs_use_the_same_owned_blocks
#check @Examples.RotationCertificateFuelMachine.Core.every_actual_prefix_preserves_context_through_the_first_exit
#check @Examples.RotationCertificateFuelMachine.Core.arbitrary_callers_have_identical_pre_handoff_runs
#check @Examples.RotationCertificateFuelMachine.Core.every_actual_borrow_prefix_represents_the_same_original_word
#check @Examples.RotationCertificateFuelMachine.Core.twelve_to_eleven_has_an_actual_two_token_restore_state
#check @Examples.RotationCertificateFuelMachine.Core.compose_with_actual_caller_time
#check @Examples.RotationCertificateFuelMachine.Core.concrete_control_and_stack_families_are_finite
#check @Examples.RotationCertificateFuelMachine.Core.sentinelCaller
#check @Examples.RotationCertificateFuelMachine.Core.sentinelStart
#check @Examples.RotationCertificateFuelMachine.Core.sentinelHandoff
#check @Examples.RotationCertificateFuelMachine.Core.sentinelAfterCaller
#check @Examples.RotationCertificateFuelMachine.Core.sentinel_handoff_keeps_old_caller_data
#check @Examples.RotationCertificateFuelMachine.Core.sentinel_body_is_an_additional_actual_transition
#check @Examples.RotationCertificateFuelMachine.Core.sentinelHandoffInTime
#check @Examples.RotationCertificateFuelMachine.Core.sentinelCallerInTime
#check @Examples.RotationCertificateFuelMachine.Core.sentinelCompositionInTime
#check @Examples.RotationCertificateFuelMachine.Core.a_live_handoff_then_caller_then_outer_none
#check @Examples.RotationCertificateFuelMachine.Core.caller_push_is_a_counterexample_to_unrestricted_workspace_preservation
#check @Examples.RotationCertificateFuelMachine.Dispatch.eof_preserves_arbitrary_fuel_and_scratch
#check @Examples.RotationCertificateFuelMachine.Dispatch.every_nonempty_certificate_is_preserved_before_borrow
#check @Examples.RotationCertificateFuelMachine.Dispatch.positive_fuel_hands_to_the_parser_without_consuming_a_tag
#check @Examples.RotationCertificateFuelMachine.Dispatch.zero_fuel_hands_to_rejection_with_the_whole_certificate
#check @Examples.RotationCertificateFuelMachine.Dispatch.empty_fuel_distinguishes_eof_from_one_raw_symbol
#check @Examples.RotationCertificateFuelMachine.Dispatch.high_zero_fuel_does_not_slow_eof
#check @Examples.RotationCertificateFuelMachine.Dispatch.first_dispatch_keeps_high_zeros_and_later_rejection_observes_them
#check @Examples.RotationCertificateFuelMachine.Dispatch.one_pending_token_retains_its_dispatch_meaning
#check @Examples.RotationCertificateFuelMachine.Dispatch.zero_restoration_and_source_rejection_are_connected
#check @Examples.RotationCertificateFuelMachine.Dispatch.reserved_heads_wait_for_the_parser_after_positive_fuel
#check @Examples.RotationCertificateFuelMachine.Dispatch.missing_move_delimiter_is_a_later_source_failure
#check @Examples.RotationCertificateFuelMachine.Dispatch.eof_handoff_itself_does_not_decide_tree_equality
#check @Examples.RotationCertificateFuelMachine.Dispatch.all_raw_words_have_a_linear_entry_bound
#check @Examples.RotationCertificateFuelMachine.Dispatch.actual_uniform_dispatch_time
#check @Examples.RotationCertificateFuelMachine.Dispatch.the_same_returned_fuel_enters_the_actual_source_continuation
#check @Examples.RotationCertificateFuelMachine.Dispatch.an_ambient_verifier_needs_only_owned_body_agreement
#check @Examples.RotationCertificateFuelMachine.Dispatch.every_actual_dispatch_prefix_preserves_all_represented_data
#check @Examples.RotationCertificateFuelMachine.Dispatch.arbitrary_stream_callers_agree_until_the_handoff
#check @Examples.RotationCertificateFuelMachine.Dispatch.representedTrees
#check @Examples.RotationCertificateFuelMachine.Dispatch.an_actual_emitted_rotation_reaches_the_parser_in_three_steps
#check @Examples.RotationCertificateFuelMachine.Dispatch.a_longer_borrow_has_distinct_machine_and_source_counts
#check @Examples.RotationCertificateFuelMachine.Dispatch.equal_initial_trees_do_not_skip_a_nonempty_certificate
#check @Examples.RotationCertificateFuelMachine.SourceLayers.actual_emitted_root_rotation_has_source_work_twenty_two
#check @Examples.RotationCertificateFuelMachine.SourceLayers.eager_binary_decoding_precedes_zero_fuel
#check @Examples.RotationCertificateFuelMachine.SourceLayers.only_the_completely_decoded_certificate_reaches_the_five_step_gate

/-! Actual finite control, program callbacks, representation/rank/workspace and
constructed timing/caller-composition data. Proof theorems are checked above. -/
#print Resources.BinaryCounter.FixedWidthMachine.Result
#print Resources.BinaryCounter.FixedWidthMachine.PredSpec
#print Resources.BinaryCounter.FixedWidthMachine.predSpec
#print Resources.BinaryCounter.FixedWidthMachine.runSteps
#print Resources.BinaryCounter.FixedWidthMachine.LocalStack
#print Resources.BinaryCounter.FixedWidthMachine.Phase
#print Resources.BinaryCounter.FixedWidthMachine.StackId
#print Resources.BinaryCounter.FixedWidthMachine.External
#print Resources.BinaryCounter.FixedWidthMachine.Label
#print Resources.BinaryCounter.FixedWidthMachine.Registers
#print Resources.BinaryCounter.FixedWidthMachine.alphabet
#print Resources.BinaryCounter.FixedWidthMachine.alphabetFintype
#print Resources.BinaryCounter.FixedWidthMachine.Statement
#print Resources.BinaryCounter.FixedWidthMachine.Cfg
#print Resources.BinaryCounter.FixedWidthMachine.phaseLabel
#print Resources.BinaryCounter.FixedWidthMachine.resultLabel
#print Resources.BinaryCounter.FixedWidthMachine.callerLabel
#print Resources.BinaryCounter.FixedWidthMachine.reset
#print Resources.BinaryCounter.FixedWidthMachine.storeBit
#print Resources.BinaryCounter.FixedWidthMachine.storeBorrowed
#print Resources.BinaryCounter.FixedWidthMachine.jump
#print Resources.BinaryCounter.FixedWidthMachine.block
#print Resources.BinaryCounter.FixedWidthMachine.program
#print Resources.BinaryCounter.FixedWidthMachine.cfg
#print Resources.BinaryCounter.FixedWidthMachine.step
#print Resources.BinaryCounter.FixedWidthMachine.next
#print Resources.BinaryCounter.FixedWidthMachine.borrowInTime
#print Resources.BinaryCounter.FixedWidthMachine.borrowInLinearTime
#print Resources.BinaryCounter.FixedWidthMachine.Owned
#print Resources.BinaryCounter.FixedWidthMachine.phaseSteps
#print Resources.BinaryCounter.FixedWidthMachine.remainingSteps
#print Resources.BinaryCounter.FixedWidthMachine.LocalStep
#print Resources.BinaryCounter.FixedWidthMachine.stackCells
#print Resources.BinaryCounter.FixedWidthMachine.FuelRepresents
#print Resources.RotationCertificate.FuelDispatchMachine.DispatchLabel
#print Resources.RotationCertificate.FuelDispatchMachine.Exit
#print Resources.RotationCertificate.FuelDispatchMachine.Protected
#print Resources.RotationCertificate.FuelDispatchMachine.ExtraLabel
#print Resources.RotationCertificate.FuelDispatchMachine.Label
#print Resources.RotationCertificate.FuelDispatchMachine.Registers
#print Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet
#print Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabetFintype
#print Resources.RotationCertificate.FuelDispatchMachine.Statement
#print Resources.RotationCertificate.FuelDispatchMachine.Cfg
#print Resources.RotationCertificate.FuelDispatchMachine.inspectLabel
#print Resources.RotationCertificate.FuelDispatchMachine.atEndLabel
#print Resources.RotationCertificate.FuelDispatchMachine.positiveLabel
#print Resources.RotationCertificate.FuelDispatchMachine.zeroLabel
#print Resources.RotationCertificate.FuelDispatchMachine.callerLabel
#print Resources.RotationCertificate.FuelDispatchMachine.exitLabel
#print Resources.RotationCertificate.FuelDispatchMachine.exitOfResult
#print Resources.RotationCertificate.FuelDispatchMachine.storePresence
#print Resources.RotationCertificate.FuelDispatchMachine.inspectBlock
#print Resources.RotationCertificate.FuelDispatchMachine.callerHandler
#print Resources.RotationCertificate.FuelDispatchMachine.program
#print Resources.RotationCertificate.FuelDispatchMachine.stores
#print Resources.RotationCertificate.FuelDispatchMachine.cfg
#print Resources.RotationCertificate.FuelDispatchMachine.step
#print Resources.RotationCertificate.FuelDispatchMachine.next
#print Resources.RotationCertificate.FuelDispatchMachine.dispatchSpec
#print Resources.RotationCertificate.FuelDispatchMachine.dispatchSteps
#print Resources.RotationCertificate.FuelDispatchMachine.dispatchInTime
#print Resources.RotationCertificate.FuelDispatchMachine.dispatchInLinearTime
#print Resources.RotationCertificate.FuelDispatchMachine.Owned
#print Resources.RotationCertificate.FuelDispatchMachine.LocalStep
#print Resources.RotationCertificate.FuelDispatchMachine.remainingSteps
#print Resources.RotationCertificate.FuelDispatchMachine.stackCells
#print Examples.RotationCertificateFuelMachine.Core.actual_uniform_borrow_time
#print Examples.RotationCertificateFuelMachine.Core.compose_with_actual_caller_time
#print Examples.RotationCertificateFuelMachine.Core.sentinelCaller
#print Examples.RotationCertificateFuelMachine.Core.sentinelStart
#print Examples.RotationCertificateFuelMachine.Core.sentinelHandoff
#print Examples.RotationCertificateFuelMachine.Core.sentinelAfterCaller
#print Examples.RotationCertificateFuelMachine.Core.sentinelHandoffInTime
#print Examples.RotationCertificateFuelMachine.Core.sentinelCallerInTime
#print Examples.RotationCertificateFuelMachine.Core.sentinelCompositionInTime
#print Examples.RotationCertificateFuelMachine.Dispatch.actual_uniform_dispatch_time
#print Examples.RotationCertificateFuelMachine.Dispatch.representedTrees

/-! Concrete finite instances for all local and composed index, alphabet,
register and label families; generic alphabet instances are also checked. -/
#synth Fintype Resources.BinaryCounter.FixedWidthMachine.Result
#synth Fintype Resources.BinaryCounter.FixedWidthMachine.LocalStack
#synth Fintype Resources.BinaryCounter.FixedWidthMachine.Phase
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.StackId Unit)
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.External Unit)
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.Label Unit)
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.Registers Bool)
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (fun _ : Unit => Bool) (Sum.inl Resources.BinaryCounter.FixedWidthMachine.LocalStack.fuel))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (fun _ : Unit => Bool) (Sum.inl Resources.BinaryCounter.FixedWidthMachine.LocalStack.borrowed))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (fun _ : Unit => Bool) (Sum.inr ()))
#synth DecidableEq (Resources.BinaryCounter.FixedWidthMachine.StackId Unit)
#synth DecidableEq (Resources.BinaryCounter.FixedWidthMachine.Label Unit)
#synth Fintype Resources.RotationCertificate.FuelDispatchMachine.DispatchLabel
#synth Fintype Resources.RotationCertificate.FuelDispatchMachine.Exit
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.Protected Unit)
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.ExtraLabel Unit)
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.Label Unit)
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.Registers Bool)
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool) (Sum.inl ()))
#synth Fintype (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool) (Sum.inr ()))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.StackId (Resources.RotationCertificate.FuelDispatchMachine.Protected Unit))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool)) (Sum.inl Resources.BinaryCounter.FixedWidthMachine.LocalStack.fuel))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool)) (Sum.inl Resources.BinaryCounter.FixedWidthMachine.LocalStack.borrowed))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool)) (Sum.inr (Sum.inl ())))
#synth Fintype (Resources.BinaryCounter.FixedWidthMachine.alphabet (Resources.RotationCertificate.FuelDispatchMachine.protectedAlphabet (fun _ : Unit => Bool)) (Sum.inr (Sum.inr ())))
#synth DecidableEq (Resources.RotationCertificate.FuelDispatchMachine.Protected Unit)
#synth DecidableEq (Resources.RotationCertificate.FuelDispatchMachine.Label Unit)

/-! All maintained new public tree-machine and connected-client contracts. -/
#check @Resources.RotationCertificate.TreeParserMachine.LocalStack
#check @Resources.RotationCertificate.TreeParserMachine.Phase
#check @Resources.RotationCertificate.TreeParserMachine.Result
#check @Resources.RotationCertificate.TreeParserMachine.StackId
#check @Resources.RotationCertificate.TreeParserMachine.External
#check @Resources.RotationCertificate.TreeParserMachine.Label
#check @Resources.RotationCertificate.TreeParserMachine.Temporaries
#check @Resources.RotationCertificate.TreeParserMachine.Registers
#check @Resources.RotationCertificate.TreeParserMachine.alphabet
#check @Resources.RotationCertificate.TreeParserMachine.alphabetFintype
#check @Resources.RotationCertificate.TreeParserMachine.Statement
#check @Resources.RotationCertificate.TreeParserMachine.Cfg
#check @Resources.RotationCertificate.TreeParserMachine.phaseLabel
#check @Resources.RotationCertificate.TreeParserMachine.resultLabel
#check @Resources.RotationCertificate.TreeParserMachine.callerLabel
#check @Resources.RotationCertificate.TreeParserMachine.reset
#check @Resources.RotationCertificate.TreeParserMachine.reset_reset
#check @Resources.RotationCertificate.TreeParserMachine.storeTag
#check @Resources.RotationCertificate.TreeParserMachine.storePending
#check @Resources.RotationCertificate.TreeParserMachine.jump
#check @Resources.RotationCertificate.TreeParserMachine.block
#check @Resources.RotationCertificate.TreeParserMachine.program
#check @Resources.RotationCertificate.TreeParserMachine.program_eq_of_agrees
#check @Resources.RotationCertificate.TreeParserMachine.cfg
#check @Resources.RotationCertificate.TreeParserMachine.cfg_ext
#check @Resources.RotationCertificate.TreeParserMachine.cfg_eta
#check @Resources.RotationCertificate.TreeParserMachine.step
#check @Resources.RotationCertificate.TreeParserMachine.next
#check @Resources.RotationCertificate.TreeParserMachine.next_none
#check @Resources.RotationCertificate.TreeParserMachine.next_some
#check @Resources.RotationCertificate.TreeParserMachine.init_step
#check @Resources.RotationCertificate.TreeParserMachine.scan_step_node
#check @Resources.RotationCertificate.TreeParserMachine.scan_step_empty
#check @Resources.RotationCertificate.TreeParserMachine.scan_step_nil
#check @Resources.RotationCertificate.TreeParserMachine.scan_step_foreign
#check @Resources.RotationCertificate.TreeParserMachine.emit_step_cons
#check @Resources.RotationCertificate.TreeParserMachine.emit_step_nil
#check @Resources.RotationCertificate.TreeParserMachine.undo_step_cons
#check @Resources.RotationCertificate.TreeParserMachine.undo_step_nil
#check @Resources.RotationCertificate.TreeParserMachine.dropPending_step_cons
#check @Resources.RotationCertificate.TreeParserMachine.dropPending_step_nil
#check @Resources.RotationCertificate.TreeParserMachine.iterate_step
#check @Resources.RotationCertificate.TreeParserMachine.emit_iterate
#check @Resources.RotationCertificate.TreeParserMachine.undo_iterate
#check @Resources.RotationCertificate.TreeParserMachine.dropPending_iterate
#check @Resources.RotationCertificate.TreeParserMachine.undo_drop_iterate
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_nil
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_node
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_empty
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_foreign
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_pos
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_le
#check @Resources.RotationCertificate.TreeParserMachine.runSteps
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_pos
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_le
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_code
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_code
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_code_nodes
#check @Resources.RotationCertificate.TreeParserMachine.phaseSteps
#check @Resources.RotationCertificate.TreeParserMachine.Owned
#check @Resources.RotationCertificate.TreeParserMachine.remainingSteps
#check @Resources.RotationCertificate.TreeParserMachine.remainingSteps_pos_iff
#check @Resources.RotationCertificate.TreeParserMachine.owned_cases
#check @Resources.RotationCertificate.TreeParserMachine.leftSlots
#check @Resources.RotationCertificate.TreeParserMachine.resumeTreeRun_slots
#check @Resources.RotationCertificate.TreeParserMachine.parseTreeLoop_empty_value
#check @Resources.RotationCertificate.TreeParserMachine.resumeTreeValue
#check @Resources.RotationCertificate.TreeParserMachine.parseTreeLoop_code_value
#check @Resources.RotationCertificate.TreeParserMachine.resultCfg
#check @Resources.RotationCertificate.TreeParserMachine.resultCfg_reset
#check @Resources.RotationCertificate.TreeParserMachine.scan_nil_iterate
#check @Resources.RotationCertificate.TreeParserMachine.scan_foreign_iterate
#check @Resources.RotationCertificate.TreeParserMachine.scan_source
#check @Resources.RotationCertificate.TreeParserMachine.run_source
#check @Resources.RotationCertificate.TreeParserMachine.run_of_some
#check @Resources.RotationCertificate.TreeParserMachine.run_of_none
#check @Resources.RotationCertificate.TreeParserMachine.run_code
#check @Resources.RotationCertificate.TreeParserMachine.runInTime
#check @Resources.RotationCertificate.TreeParserMachine.runInLinearTime
#check @Resources.RotationCertificate.TreeParserMachine.destination
#check @Resources.RotationCertificate.TreeParserMachine.phase_step_data
#check @Resources.RotationCertificate.TreeParserMachine.LocalStep
#check @Resources.RotationCertificate.TreeParserMachine.local_step_data
#check @Resources.RotationCertificate.TreeParserMachine.local_progress
#check @Resources.RotationCertificate.TreeParserMachine.step_caller_independent
#check @Resources.RotationCertificate.TreeParserMachine.prefix_local_register
#check @Resources.RotationCertificate.TreeParserMachine.phase_prefix
#check @Resources.RotationCertificate.TreeParserMachine.run_prefix
#check @Resources.RotationCertificate.TreeParserMachine.phase_prefix_caller_independent
#check @Resources.RotationCertificate.TreeParserMachine.local_reaches_preserves
#check @Resources.RotationCertificate.TreeParserMachine.prefix_preserves
#check @Resources.RotationCertificate.TreeParserMachine.emit_prefix
#check @Resources.RotationCertificate.TreeParserMachine.undo_prefix
#check @Resources.RotationCertificate.TreeParserMachine.dropPending_prefix
#check @Resources.RotationCertificate.TreeParserMachine.OpenPrefix
#check @Resources.RotationCertificate.TreeParserMachine.openPrefix_bounds
#check @Resources.RotationCertificate.TreeParserMachine.openPrefix_frames
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_openPrefix
#check @Resources.RotationCertificate.TreeParserMachine.Blocked
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_openPrefix
#check @Resources.RotationCertificate.TreeParserMachine.parseTreeRun_none_of_openPrefix
#check @Resources.RotationCertificate.TreeParserMachine.parseTreeLoop_none_openPrefix
#check @Resources.RotationCertificate.TreeParserMachine.parseTreeRun_none_iff_openPrefix
#check @Resources.RotationCertificate.TreeParserMachine.run_openPrefix_failure
#check @Resources.RotationCertificate.TreeParserMachine.outputCells
#check @Resources.RotationCertificate.TreeParserMachine.contextCells
#check @Resources.RotationCertificate.TreeParserMachine.outputCells_update_cons
#check @Resources.RotationCertificate.TreeParserMachine.stackCells
#check @Resources.RotationCertificate.TreeParserMachine.credit
#check @Resources.RotationCertificate.TreeParserMachine.potential
#check @Resources.RotationCertificate.TreeParserMachine.step_potential_le
#check @Resources.RotationCertificate.TreeParserMachine.local_reaches_potential_le
#check @Resources.RotationCertificate.TreeParserMachine.prefix_stackCells_le
#check @Resources.RotationCertificate.TreeParserMachine.scanSteps_nodes
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_nodes
#check @Resources.RotationCertificate.TreeParserMachine.runSteps_nodes_foreign
#check @Resources.RotationCertificate.TreeParserMachine.scan_nodes_iterate
#check @Resources.RotationCertificate.TreeParserMachine.nodes_prefix
#check @Resources.RotationCertificate.TreeParserMachine.nodes_prefix_sharp
#check @Resources.RotationCertificate.TreeParserMachine.FirstSuccess
#check @Resources.RotationCertificate.TreeParserMachine.firstSuccess_iff
#check @Resources.RotationCertificate.TreeParserMachine.firstSuccess_code_iff
#check @Resources.RotationCertificate.TreeParserMachine.machine
#check @Resources.RotationCertificate.TreeParserMachine.machine_step_eq
#check @Resources.RotationCertificate.TreeParserMachine.initList_eq
#check @Examples.RotationCertificateTreeParserMachine.SmallAlphabet
#check @Examples.RotationCertificateTreeParserMachine.smallAlphabetFintype
#check @Examples.RotationCertificateTreeParserMachine.smallContext
#check @Examples.RotationCertificateTreeParserMachine.oldOutputs
#check @Examples.RotationCertificateTreeParserMachine.staleRegisters
#check @Examples.RotationCertificateTreeParserMachine.haltCaller
#check @Examples.RotationCertificateTreeParserMachine.concrete_control_is_finite
#check @Examples.RotationCertificateTreeParserMachine.nil_leaves_the_arbitrary_suffix
#check @Examples.RotationCertificateTreeParserMachine.empty_input_fails_in_five
#check @Examples.RotationCertificateTreeParserMachine.foreign_head_restores_its_whole_word
#check @Examples.RotationCertificateTreeParserMachine.nonpalindromic_emit_retains_old_output
#check @Examples.RotationCertificateTreeParserMachine.nonpalindromic_undo_retains_the_blocked_tail
#check @Examples.RotationCertificateTreeParserMachine.emit_preserves_nonempty_pending
#check @Examples.RotationCertificateTreeParserMachine.pending_cleanup_counts_each_token_and_empty_probe
#check @Examples.RotationCertificateTreeParserMachine.literal_codes_keep_their_shape_and_tail
#check @Examples.RotationCertificateTreeParserMachine.incomplete_codes_restore_all_consumed_material
#check @Examples.RotationCertificateTreeParserMachine.nonpalindromic_rejected_prefix_keeps_the_blocker
#check @Examples.RotationCertificateTreeParserMachine.needLeft_scan_completes_the_parent
#check @Examples.RotationCertificateTreeParserMachine.needLeft_scan_failure_restores_its_ghost_prefix
#check @Examples.RotationCertificateTreeParserMachine.needRight_scan_moves_the_entire_left_prefix
#check @Examples.RotationCertificateTreeParserMachine.mixed_ghost_frames_keep_outer_first_order
#check @Examples.RotationCertificateTreeParserMachine.emitted_tree_enters_the_actual_machine
#check @Examples.RotationCertificateTreeParserMachine.actual_uniform_tree_time
#check @Examples.RotationCertificateTreeParserMachine.nonempty_reverse_changes_an_otherwise_valid_tree
#check @Examples.RotationCertificateTreeParserMachine.nonempty_reverse_changes_failure_restoration
#check @Examples.RotationCertificateTreeParserMachine.nonempty_pending_rejects_a_valid_nil_word
#check @Examples.RotationCertificateTreeParserMachine.nonempty_pending_consumes_two_nil_words
#check @Examples.RotationCertificateTreeParserMachine.reinitializing_a_ghost_scan_rejects_its_completion
#check @Examples.RotationCertificateTreeParserMachine.zero_pending_scan_can_emit_an_incomplete_code
#check @Examples.RotationCertificateTreeParserMachine.actual_prefix_keeps_context_and_bounds_all_cells
#check @Examples.RotationCertificateTreeParserMachine.different_callers_share_every_owned_prefix
#check @Examples.RotationCertificateTreeParserMachine.all_node_words_attain_the_workspace_bound
#check @Examples.RotationCertificateTreeParserMachine.actual_first_success_recognizes_exactly_one_prefix
#check @Examples.RotationCertificateTreeParserMachine.needRight_foreign_failure_keeps_its_large_prefix
#check @Examples.RotationCertificateTreeParserMachine.needRight_source_and_machine_work_are_distinct
#check @Examples.RotationCertificateTreeParserMachine.needRight_completes_with_an_arbitrary_right_tree
#check @Examples.RotationCertificateTreeParserMachine.needLeft_completes_with_two_arbitrary_children
#check @Examples.RotationCertificateTreeParserMachine.all_nodes_restore_after_their_exact_failure_time
#check @Examples.RotationCertificateTreeParserMachine.all_nodes_before_a_foreign_tag_restore_without_reading_its_tail
#check @Examples.RotationCertificateTreeParserMachine.actual_tree_time_composes_with_a_continuation
#check @Examples.RotationCertificateTreeParserMachine.arbitrary_emit_and_rollback_have_their_literal_endpoints
#check @Examples.RotationCertificateTreeParserMachine.actual_input_emitter_enters_only_the_first_tree_call
#check @Examples.RotationCertificateTreeParserMachine.emitted_rotation_separates_tree_machine_from_full_source_parser
#check @Examples.RotationCertificateTreeParserMachine.nil_source_work_is_smaller_than_its_actual_machine_time
#check @Examples.RotationCertificateTreeParserMachine.mixed_frame_source_and_machine_clocks
#check @Examples.RotationCertificateTreeParserMachine.partial_transfers_preserve_the_unread_material
#check @Examples.RotationCertificateTreeParserMachine.every_actual_source_failure_has_its_exact_cleanup_decomposition
#check @Examples.RotationCertificateTreeParserMachine.concrete_left_two_preserves_both_distinct_old_outputs
#check @Examples.RotationCertificateTreeParserMachine.old_output_is_distinct_from_corrupt_pending
#check @Examples.RotationCertificateTreeParserMachine.actual_finite_machine_uniform_time
#check @Examples.RotationCertificateTreeParserMachine.sentinelCaller
#check @Examples.RotationCertificateTreeParserMachine.sentinelStart
#check @Examples.RotationCertificateTreeParserMachine.sentinelHandoff
#check @Examples.RotationCertificateTreeParserMachine.sentinelAfterCaller
#check @Examples.RotationCertificateTreeParserMachine.sentinel_handoff_precedes_the_actual_push
#check @Examples.RotationCertificateTreeParserMachine.sentinel_push_is_one_additional_actual_step
#check @Examples.RotationCertificateTreeParserMachine.sentinelHandoffInTime
#check @Examples.RotationCertificateTreeParserMachine.sentinelCallerInTime
#check @Examples.RotationCertificateTreeParserMachine.sentinelCompositionInTime
#check @Examples.RotationCertificateTreeParserMachine.live_return_halt_and_outer_none_are_three_distinct_stages
#check @Examples.RotationCertificateTreeParserMachine.allocatingCaller
#check @Examples.RotationCertificateTreeParserMachine.emptyStart
#check @Examples.RotationCertificateTreeParserMachine.allocatingState
#check @Examples.RotationCertificateTreeParserMachine.allocating_caller_step
#check @Examples.RotationCertificateTreeParserMachine.allocating_caller_runs_after_the_first_failure
#check @Examples.RotationCertificateTreeParserMachine.a_post_return_loop_exceeds_the_component_workspace_bound
#check @Examples.RotationCertificateTreeParserMachine.misleadingCaller
#check @Examples.RotationCertificateTreeParserMachine.misleadingSuccess
#check @Examples.RotationCertificateTreeParserMachine.misleadingReentry
#check @Examples.RotationCertificateTreeParserMachine.misleading_success_is_created_by_one_caller_step
#check @Examples.RotationCertificateTreeParserMachine.misleading_success_can_reenter_the_component
#check @Examples.RotationCertificateTreeParserMachine.later_success_is_not_the_parser_first_success
#check @Examples.RotationCertificateTreeParserMachine.twoStageCaller
#check @Examples.RotationCertificateTreeParserMachine.twoStageStart
#check @Examples.RotationCertificateTreeParserMachine.twoStageFirstReturn
#check @Examples.RotationCertificateTreeParserMachine.twoStageSecondEntry
#check @Examples.RotationCertificateTreeParserMachine.twoStageFinalReturn
#check @Examples.RotationCertificateTreeParserMachine.the_second_entry_is_the_actual_caller_successor
#check @Examples.RotationCertificateTreeParserMachine.firstTreeInTime
#check @Examples.RotationCertificateTreeParserMachine.interveningJumpInTime
#check @Examples.RotationCertificateTreeParserMachine.secondTreeInTime
#check @Examples.RotationCertificateTreeParserMachine.twoTreeCompositionInTime
#check @Examples.RotationCertificateTreeParserMachine.two_tree_calls_include_the_real_intervening_jump
#check @Examples.RotationCertificateTreeParserMachine.left_two_then_nil_takes_seventeen_actual_steps
#check @Examples.RotationCertificateTreeParserMachine.two_tree_calls_keep_the_original_bound_through_every_prefix

/-! Actual finite runtime/specification and timed-data bodies. -/
#print Resources.RotationCertificate.TreeParserMachine.LocalStack
#print Resources.RotationCertificate.TreeParserMachine.Phase
#print Resources.RotationCertificate.TreeParserMachine.Result
#print Resources.RotationCertificate.TreeParserMachine.StackId
#print Resources.RotationCertificate.TreeParserMachine.External
#print Resources.RotationCertificate.TreeParserMachine.Label
#print Resources.RotationCertificate.TreeParserMachine.Temporaries
#print Resources.RotationCertificate.TreeParserMachine.Registers
#print Resources.RotationCertificate.TreeParserMachine.alphabet
#print Resources.RotationCertificate.TreeParserMachine.alphabetFintype
#print Resources.RotationCertificate.TreeParserMachine.Statement
#print Resources.RotationCertificate.TreeParserMachine.Cfg
#print Resources.RotationCertificate.TreeParserMachine.phaseLabel
#print Resources.RotationCertificate.TreeParserMachine.resultLabel
#print Resources.RotationCertificate.TreeParserMachine.callerLabel
#print Resources.RotationCertificate.TreeParserMachine.reset
#print Resources.RotationCertificate.TreeParserMachine.storeTag
#print Resources.RotationCertificate.TreeParserMachine.storePending
#print Resources.RotationCertificate.TreeParserMachine.jump
#print Resources.RotationCertificate.TreeParserMachine.block
#print Resources.RotationCertificate.TreeParserMachine.program
#print Resources.RotationCertificate.TreeParserMachine.cfg
#print Resources.RotationCertificate.TreeParserMachine.step
#print Resources.RotationCertificate.TreeParserMachine.next
#print Resources.RotationCertificate.TreeParserMachine.scanSteps
#print Resources.RotationCertificate.TreeParserMachine.runSteps
#print Resources.RotationCertificate.TreeParserMachine.phaseSteps
#print Resources.RotationCertificate.TreeParserMachine.Owned
#print Resources.RotationCertificate.TreeParserMachine.remainingSteps
#print Resources.RotationCertificate.TreeParserMachine.leftSlots
#print Resources.RotationCertificate.TreeParserMachine.resumeTreeValue
#print Resources.RotationCertificate.TreeParserMachine.resultCfg
#print Resources.RotationCertificate.TreeParserMachine.runInTime
#print Resources.RotationCertificate.TreeParserMachine.runInLinearTime
#print Resources.RotationCertificate.TreeParserMachine.destination
#print Resources.RotationCertificate.TreeParserMachine.LocalStep
#print Resources.RotationCertificate.TreeParserMachine.OpenPrefix
#print Resources.RotationCertificate.TreeParserMachine.Blocked
#print Resources.RotationCertificate.TreeParserMachine.outputCells
#print Resources.RotationCertificate.TreeParserMachine.contextCells
#print Resources.RotationCertificate.TreeParserMachine.stackCells
#print Resources.RotationCertificate.TreeParserMachine.credit
#print Resources.RotationCertificate.TreeParserMachine.potential
#print Resources.RotationCertificate.TreeParserMachine.FirstSuccess
#print Resources.RotationCertificate.TreeParserMachine.machine
#print Examples.RotationCertificateTreeParserMachine.SmallAlphabet
#print Examples.RotationCertificateTreeParserMachine.smallAlphabetFintype
#print Examples.RotationCertificateTreeParserMachine.smallContext
#print Examples.RotationCertificateTreeParserMachine.oldOutputs
#print Examples.RotationCertificateTreeParserMachine.staleRegisters
#print Examples.RotationCertificateTreeParserMachine.haltCaller
#print Examples.RotationCertificateTreeParserMachine.actual_uniform_tree_time
#print Examples.RotationCertificateTreeParserMachine.actual_tree_time_composes_with_a_continuation
#print Examples.RotationCertificateTreeParserMachine.actual_finite_machine_uniform_time
#print Examples.RotationCertificateTreeParserMachine.sentinelCaller
#print Examples.RotationCertificateTreeParserMachine.sentinelStart
#print Examples.RotationCertificateTreeParserMachine.sentinelHandoff
#print Examples.RotationCertificateTreeParserMachine.sentinelAfterCaller
#print Examples.RotationCertificateTreeParserMachine.sentinelHandoffInTime
#print Examples.RotationCertificateTreeParserMachine.sentinelCallerInTime
#print Examples.RotationCertificateTreeParserMachine.sentinelCompositionInTime
#print Examples.RotationCertificateTreeParserMachine.allocatingCaller
#print Examples.RotationCertificateTreeParserMachine.emptyStart
#print Examples.RotationCertificateTreeParserMachine.allocatingState
#print Examples.RotationCertificateTreeParserMachine.misleadingCaller
#print Examples.RotationCertificateTreeParserMachine.misleadingSuccess
#print Examples.RotationCertificateTreeParserMachine.misleadingReentry
#print Examples.RotationCertificateTreeParserMachine.twoStageCaller
#print Examples.RotationCertificateTreeParserMachine.twoStageStart
#print Examples.RotationCertificateTreeParserMachine.twoStageFirstReturn
#print Examples.RotationCertificateTreeParserMachine.twoStageSecondEntry
#print Examples.RotationCertificateTreeParserMachine.twoStageFinalReturn
#print Examples.RotationCertificateTreeParserMachine.firstTreeInTime
#print Examples.RotationCertificateTreeParserMachine.interveningJumpInTime
#print Examples.RotationCertificateTreeParserMachine.secondTreeInTime
#print Examples.RotationCertificateTreeParserMachine.twoTreeCompositionInTime

/-! Actual finite instances, including every concrete alphabet slot. -/
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.LocalStack Bool)
#synth Fintype Resources.RotationCertificate.TreeParserMachine.Phase
#synth Fintype Resources.RotationCertificate.TreeParserMachine.Result
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.StackId Bool Bool)
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.External Bool Unit)
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.Label Bool Unit)
#synth Fintype Resources.RotationCertificate.TreeParserMachine.Temporaries
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.Registers Bool)
#synth DecidableEq (Resources.RotationCertificate.TreeParserMachine.StackId Bool Bool)
#synth DecidableEq (Resources.RotationCertificate.TreeParserMachine.Label Bool Unit)
#synth DecidableEq (Resources.RotationCertificate.TreeParserMachine.Registers Bool)
#synth Fintype (Examples.RotationCertificateTreeParserMachine.SmallAlphabet false)
#synth Fintype (Examples.RotationCertificateTreeParserMachine.SmallAlphabet true)
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inl Resources.RotationCertificate.TreeParserMachine.LocalStack.raw))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inl Resources.RotationCertificate.TreeParserMachine.LocalStack.reverse))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inl Resources.RotationCertificate.TreeParserMachine.LocalStack.pending))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inl (Resources.RotationCertificate.TreeParserMachine.LocalStack.output false)))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inl (Resources.RotationCertificate.TreeParserMachine.LocalStack.output true)))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inr false))
#synth Fintype (Resources.RotationCertificate.TreeParserMachine.alphabet Bool Examples.RotationCertificateTreeParserMachine.SmallAlphabet (Sum.inr true))

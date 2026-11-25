import Applications.Resources.RotationCertificate.MoveApplyMachine.Principal

/-!
# MoveApplyMachine: PrincipalSpace
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ### Principal physical bounds keep all seven stores -/

section PrincipalSpace
variable [Fintype K]

def principalCells (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (ctx : ∀ k, List (Γ k)) : Nat :=
  raw.length + path.length + source.length + saved.length + scratch.length + pending.length +
    contextCells ctx

def parsedCellsBound (move : RotationMove) (rest : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (ctx : ∀ k, List (Γ k)) : Nat :=
  rest.length + move.position.length + path.length + 2 * source.length + saved.length +
    scratch.length + pending.length + contextCells ctx

omit [DecidableEq K] in
theorem initial_stackCells (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (entry (Λ := Λ) regs raw path source saved scratch pending ctx) =
      principalCells raw path source saved scratch pending ctx := by
  rw [entry, stackCells_cfg]
  rfl

omit [DecidableEq K] in
theorem entry_potential (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (entry (Λ := Λ) regs raw path source saved scratch pending ctx) =
      principalCells raw path source saved scratch pending ctx + source.length := by
  change potential (cfg (some (phaseLabel (movePhase .start))) regs
    (entryData raw path source saved scratch pending) ctx) = _
  rw [potential_phase_cfg]
  simp only [localCells, entryData, phaseDebt, movePhase, MoveParserMachine.phaseDebt,
    phaseCredit, principalCells, List.length_nil]
  omega

omit [DecidableEq K] in
theorem parsed_entry_potential (move : RotationMove) (rest : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionLabel (Λ := Λ) (.seek move.direction))) regs
      (parsedData move rest D) ctx) =
      parsedCellsBound move rest D.path D.source D.saved D.scratch D.pending ctx := by
  change potential (cfg (some (phaseLabel (positionPhase (.seek move.direction)))) regs
    (parsedData move rest D) ctx) = _
  rw [potential_phase_cfg]
  simp only [parsedCellsBound, localCells, parsedData, phaseDebt, positionPhase, phaseCredit,
    PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit, positionData,
    List.length_append, List.length_nil]
  omega

theorem prefix_stackCells_le (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx + source.length := by
  have cells := prefix_stackCells_le_dirty caller
    (entry regs raw path source saved scratch pending ctx) n bound reached executed
  simpa only [entry_potential] using cells

theorem prefix_stackCells_le_after_localRun {start middle : Cfg Γ Λ R} {first : Nat}
    (segment : LocalRun caller first start middle) (n : Nat)
    (bound : n ≤ remainingSteps start) (after : first ≤ n)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential middle := by
  have suffixBound : n - first ≤ remainingSteps middle := by
    have rank := LocalRun.remaining caller segment
    omega
  exact prefix_stackCells_le_dirty caller middle (n - first) suffixBound reached
    (prefix_iterate_after_localRun caller segment n after reached executed)

/-- The parser segment has no tree credit charge: its full physical cell bound is the initial sum. -/
theorem parser_prefix_stackCells_le (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ MoveParserMachine.fullSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx := by
  let D := entryData raw path source saved scratch pending
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let localStart : MoveCfg Γ Λ R :=
    MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx)
  have startEq : moveCfg localStart = entry regs raw path source saved scratch pending ctx := by
    change moveCfg (moveView (some (MoveParserMachine.phaseLabel .start))
      (moveRegisterEquiv.symm regs) D ctx) = _
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
    rfl
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.run_prefix localCaller raw path (moveRegisterEquiv.symm regs) (moveContext D ctx) n bound
  have earlier := (MoveParserMachine.run_first_return localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  have transported := move_prefix_transport caller localCaller n localStart
    (fun j strict => earlier j (by omega))
  change (next caller)^[n] (some (moveCfg localStart)) =
    ((MoveParserMachine.next localCaller)^[n]
      (some (MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx)))).map moveCfg
      at transported
  rw [localRun, Option.map_some, startEq] at transported
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_moveCfg]
  have cells := MoveParserMachine.prefix_stackCells_le localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx) n bound localReached localRun
  rw [moveContext_cells] at cells
  simpa only [D, entryData, principalCells, Nat.add_assoc] using cells

theorem prefix_stackCells_le_of_none (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) (n : Nat)
    (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx := by
  by_cases before : n ≤ MoveParserMachine.fullSteps raw
  · exact parser_prefix_stackCells_le caller raw path source saved scratch pending regs ctx n before reached executed
  · rw [runSteps_of_none raw path source saved scratch pending failed] at bound
    have count : n = MoveParserMachine.fullSteps raw + 1 := by omega
    have endpoint := run_of_none caller raw path source saved scratch pending regs ctx failed
    rw [← count, executed] at endpoint
    have same := Option.some.inj endpoint
    rw [same, stackCells_cfg]
    exact Nat.le_refl _

theorem prefix_stackCells_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) (n : Nat)
    (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) := by
  by_cases before : n ≤ MoveParserMachine.fullSteps raw
  · exact (parser_prefix_stackCells_le caller raw path source saved scratch pending regs ctx
      n before reached executed).trans (Nat.le_max_left _ _)
  · have after : MoveParserMachine.fullSteps raw + 1 ≤ n := by omega
    have segment := paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed
    have cells := prefix_stackCells_le_after_localRun caller segment n bound after reached executed
    rw [parsed_entry_potential] at cells
    exact cells.trans (Nat.le_max_right _ _)

end PrincipalSpace

/-! ### Actual malformed-family runs, drops and ranks -/

theorem left_nodes_drop (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 6)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.left_nodes_drop localCaller n (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest [] (List.replicate n nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData]; omega

theorem right_nodes_drop (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 8)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.right_nodes_drop localCaller m (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData]; omega

theorem left_nodes_run (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 8)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)
      (cfg (some (resultLabel rotationFailure)) (reset regs) { certificate := certificateRest, source := List.replicate n nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.left_nodes_run localCaller n (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest [] (List.replicate n nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData, rotationFailure]; omega

theorem right_nodes_run (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 11)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (resultLabel rotationFailure)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.right_nodes_run localCaller m (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData, rotationFailure]; omega

include caller in
theorem left_nodes_exact_clock (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] = 3 * n + 8 :=
  (LocalRun.phase_endpoint caller (q := movePhase .start) (left_nodes_run caller certificateRest n regs ctx)).1

include caller in
theorem right_nodes_exact_clock (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] = 3 * m + 11 :=
  (LocalRun.phase_endpoint caller (q := movePhase .start) (right_nodes_run caller certificateRest m regs ctx)).1

include caller in
theorem left_nodes_drop_rank (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (positionLabel .dropPending)) (reset regs)
      { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) = n + 2 := by
  have rank := LocalRun.remaining caller (left_nodes_drop caller certificateRest n regs ctx)
  change runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] = _ at rank
  rw [left_nodes_exact_clock caller certificateRest n regs ctx] at rank
  omega

include caller in
theorem right_nodes_drop_rank (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (positionLabel .dropPending)) (reset regs)
      { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 3 := by
  have rank := LocalRun.remaining caller (right_nodes_drop caller certificateRest m regs ctx)
  change runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] = _ at rank
  rw [right_nodes_exact_clock caller certificateRest m regs ctx] at rank
  omega

/-- Five real activations reach right-root setup; no caller result is crossed. -/
theorem right_nodes_start (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 5
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel (.start .right))) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.phase_step_localRun localCaller
    (PositionedRotationMachine.seek_step_path_nil localCaller .right
      { source := List.replicate (m + 2) nodeTag } (reset regs) (positionContext { certificate := certificateRest } ctx))
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append, List.append_nil,
    setPositionData, Option.map_some, positionLabelEquiv_phase, position_reset_reset] using
      LocalRun.trans caller paid transported

/-- The sixth activation gives the sharper right-family potential at the actual scanner. -/
theorem right_nodes_scan (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 6
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel (.scanScratch .right))) (reset regs)
        { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.phase_step_localRun localCaller
    (PositionedRotationMachine.start_right_step_nodes localCaller (List.replicate m nodeTag)
      ({} : PositionedRotationMachine.LocalData) (reset regs) (positionContext { certificate := certificateRest } ctx))
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have start := right_nodes_start caller certificateRest m regs ctx
  have joined := LocalRun.trans caller start transported
  simpa only [List.replicate_succ, setPositionData, Option.map_some,
    positionLabelEquiv_phase, position_reset_reset] using joined

theorem parser_eof_run (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * k + 4)
      (entry regs (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending ctx)
      (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending) ctx) := by
  have failed := congrArg Prod.fst (MoveParserMachine.parseMoveRun_sharpRaw (k + 1))
  have run := run_of_none_localRun caller (MoveParserMachine.sharpRaw (k + 1)) path
    source saved scratch pending regs ctx failed
  rw [MoveParserMachine.fullSteps_sharpRaw, MoveParserMachine.sharpRaw_eq] at run
  convert run using 1

include caller in
theorem parser_eof_exact_clock (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending =
      2 * k + 4 :=
  (LocalRun.phase_endpoint caller (q := movePhase .start) (parser_eof_run caller k path source saved scratch pending regs ctx)).1

section SharpPhysicalSpace
variable [Fintype K]

omit [DecidableEq K] in
theorem left_nodes_drop_cells (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (positionLabel .dropPending)) regs
      { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) =
      2 * n + certificateRest.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [localCells, List.length_nil, List.length_replicate]
  omega

omit [DecidableEq K] in
theorem right_nodes_drop_cells (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (positionLabel .dropPending)) regs
      { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [localCells, List.length_nil, List.length_replicate]
  omega

theorem left_nodes_prefix_cells (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (j : Nat) (bound : j ≤ 3 * n + 8) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached) :
    stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + contextCells ctx := by
  have parsed : (parseMoveRun (moveCode ⟨.left, []⟩ ++ certificateRest)).1 = some (⟨.left, []⟩, certificateRest) := by
    exact congrArg Prod.fst (parseMoveRun_code ⟨.left, []⟩ certificateRest)
  have bound' : j ≤ runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] := by
    rw [left_nodes_exact_clock caller certificateRest n regs ctx]
    exact bound
  have cells := prefix_stackCells_le_of_some caller (moveCode ⟨.left, []⟩ ++ certificateRest) ⟨.left, []⟩ certificateRest []
    (List.replicate n nodeTag) [] [] [] regs ctx parsed j bound' reached executed
  simp only [principalCells, parsedCellsBound, List.length_append, moveCode_length, List.length_nil,
    List.length_replicate, Nat.zero_add, Nat.add_zero] at cells
  omega

omit [DecidableEq K] in
theorem right_nodes_scan_potential (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionLabel (.scanScratch .right))) regs
      { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + contextCells ctx := by
  change potential (cfg (some (phaseLabel (positionPhase (.scanScratch .right)))) regs
    { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx) = _
  rw [potential_phase_cfg]
  simp only [localCells, phaseDebt, positionPhase, phaseCredit, positionData,
    PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit,
    List.length_replicate, List.length_nil, List.length_cons]
  omega

/-- The upper bound applies to every actual prefix; the sixth configuration supplies its sharp potential. -/
theorem right_nodes_prefix_cells (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (j : Nat) (bound : j ≤ 3 * m + 11) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached) :
    stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx := by
  have parserClock : MoveParserMachine.fullSteps (moveCode ⟨.right, []⟩ ++ certificateRest) = 3 := by
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      MoveParserMachine.fullSteps_code ⟨.right, []⟩ certificateRest
  by_cases parser : j ≤ 3
  · have cells := parser_prefix_stackCells_le caller (moveCode ⟨.right, []⟩ ++ certificateRest) []
      (List.replicate (m + 2) nodeTag) [] [] [] regs ctx j (by omega) reached executed
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero] at cells
    omega
  · by_cases four : j = 4
    · subst j
      have actual := LocalRun.iterate caller (paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
        (List.replicate (m + 2) nodeTag) [] [] [] regs ctx)
      change (next caller)^[4]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) =
          some (cfg (some (positionLabel (.seek .right))) (reset regs)
            { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) at actual
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg]
      simp only [localCells, List.length_nil, List.length_replicate]
      omega
    · by_cases five : j = 5
      · subst j
        have actual := LocalRun.iterate caller (right_nodes_start caller certificateRest m regs ctx)
        have same := Option.some.inj (executed.symm.trans actual)
        rw [same, stackCells_cfg]
        simp only [localCells, List.length_nil, List.length_replicate]
        omega
      · have bound' : j ≤ runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) []
            (List.replicate (m + 2) nodeTag) [] [] [] := by
          rw [right_nodes_exact_clock caller certificateRest m regs ctx]
          exact bound
        have cells := prefix_stackCells_le_after_localRun caller (right_nodes_scan caller certificateRest m regs ctx)
          j bound' (by omega) reached executed
        rw [right_nodes_scan_potential] at cells
        omega

/-- The left-family maximum includes both the retained certificate at entry and the attained drop state. -/
theorem left_nodes_peak (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * n + 8 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached →
      stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * n + 8 ∧
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached ∧
      stackCells reached = max (n + 2) (2 * n) + certificateRest.length + contextCells ctx := by
  refine ⟨left_nodes_prefix_cells caller certificateRest n regs ctx, ?_⟩
  by_cases initial : 2 * n ≤ n + 2
  · refine ⟨0, entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx,
      by omega, rfl, ?_⟩
    rw [initial_stackCells, Nat.max_eq_left initial]
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero]
    omega
  · refine ⟨2 * n + 6,
      cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx,
      by omega, LocalRun.iterate caller (left_nodes_drop caller certificateRest n regs ctx), ?_⟩
    rw [left_nodes_drop_cells, Nat.max_eq_right (by omega)]

/-- The right-family maximum includes its small-input entry maximum and its actual later peak. -/
theorem right_nodes_peak (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * m + 11 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached →
      stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * m + 11 ∧
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached ∧
      stackCells reached = max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx := by
  refine ⟨right_nodes_prefix_cells caller certificateRest m regs ctx, ?_⟩
  by_cases initial : 2 * m + 3 ≤ m + 4
  · refine ⟨0, entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx,
      by omega, rfl, ?_⟩
    rw [initial_stackCells, Nat.max_eq_left initial]
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero]
    omega
  · refine ⟨2 * m + 8,
      cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx,
      by omega, LocalRun.iterate caller (right_nodes_drop caller certificateRest m regs ctx), ?_⟩
    rw [right_nodes_drop_cells, Nat.max_eq_right (by omega)]

theorem parser_eof_peak (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 2 * k + 4 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
          path source saved scratch pending ctx)) = some reached →
      stackCells reached ≤ k + 1 + path.length + source.length + saved.length +
        scratch.length + pending.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 2 * k + 4 ∧
      (next caller)^[j]
        (some (entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
          path source saved scratch pending ctx)) = some reached ∧
      stackCells reached = k + 1 + path.length + source.length + saved.length +
        scratch.length + pending.length + contextCells ctx := by
  constructor
  · intro j bound reached executed
    have failed : (parseMoveRun (rotateLeftTag :: List.replicate k pathLeftTag)).1 = none := by
      have actual := congrArg Prod.fst (MoveParserMachine.parseMoveRun_sharpRaw (k + 1))
      simpa only [MoveParserMachine.sharpRaw_eq] using actual
    have bound' : j ≤ runSteps (rotateLeftTag :: List.replicate k pathLeftTag)
        path source saved scratch pending := by
      rw [parser_eof_exact_clock caller k path source saved scratch pending regs ctx]
      exact bound
    have cells := prefix_stackCells_le_of_none caller
      (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending regs ctx
      failed j bound' reached executed
    simpa only [principalCells, List.length_cons, List.length_replicate] using cells
  · refine ⟨0, entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
      path source saved scratch pending ctx, by omega, rfl, ?_⟩
    rw [initial_stackCells]
    simp only [principalCells, List.length_cons, List.length_replicate]

end SharpPhysicalSpace


end Resources.RotationCertificate.MoveApplyMachine

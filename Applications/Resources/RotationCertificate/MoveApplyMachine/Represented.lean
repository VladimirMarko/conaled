import Applications.Resources.RotationCertificate.MoveApplyMachine.Space

/-!
# MoveApplyMachine: Represented
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem dispatch_failure_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel .failure)) regs D ctx) =
      some (cfg (some (resultLabel parseFailure)) (reset regs) D ctx) :=
  dispatch_step caller .failure D regs ctx

theorem dispatch_left_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel (.success .left))) regs D ctx) =
      some (cfg (some (positionLabel (.seek .left))) (reset regs) D ctx) :=
  dispatch_step caller (.success .left) D regs ctx

theorem dispatch_right_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel (.success .right))) regs D ctx) =
      some (cfg (some (positionLabel (.seek .right))) (reset regs) D ctx) :=
  dispatch_step caller (.success .right) D regs ctx

omit [DecidableEq K] in
theorem phaseSteps_move (q : MoveParserMachine.Phase) (D : LocalData) :
    phaseSteps (movePhase q) D = MoveParserMachine.phaseSteps q D.certificate D.moveReverse +
      phaseSteps (dispatchPhase (moveFinish q D).result) (moveFinish q D).data := rfl

omit [DecidableEq K] in
theorem phaseSteps_dispatch_failure (D : LocalData) : phaseSteps (dispatchPhase .failure) D = 1 := rfl

omit [DecidableEq K] in
theorem phaseSteps_dispatch_success (d : RotationDirection) (D : LocalData) :
    phaseSteps (dispatchPhase (.success d)) D =
      1 + PositionedRotationMachine.phaseSteps (.seek d) (positionData D) := rfl

omit [DecidableEq K] in
theorem phaseSteps_position (q : PositionedRotationMachine.Phase) (D : LocalData) :
    phaseSteps (positionPhase q) D = PositionedRotationMachine.phaseSteps q (positionData D) := rfl

omit [DecidableEq K] in
theorem phaseResult_move (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (movePhase q) regs D ctx =
      phaseResult (dispatchPhase (moveFinish q D).result) (resetMove regs) (moveFinish q D).data ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_dispatch_failure (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (dispatchPhase .failure) regs D ctx =
      cfg (some (resultLabel parseFailure)) (reset regs) D ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_dispatch_success (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (dispatchPhase (.success d)) regs D ctx =
      phaseResult (positionPhase (.seek d)) (reset regs) D ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_position (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (positionPhase q) regs D ctx =
      cfg (some (resultLabel (.inr (PositionedRotationMachine.evaluate (.inl q) (positionData D)).result)))
        (reset regs) (setPositionData D (PositionedRotationMachine.evaluate (.inl q) (positionData D)).data) ctx := rfl

theorem move_owned_prefix_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (start : MoveCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveParserMachine.remainingSteps start) :
    (next caller)^[n] (some (moveCfg start)) =
      ((MoveParserMachine.next localCaller)^[n] (some start)).map moveCfg := by
  apply move_prefix_transport caller localCaller n start
  intro j strict
  obtain ⟨reached, executed, _, _, owned, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start j (by omega)
  exact ⟨reached, executed, owned.mp (by omega)⟩

theorem position_owned_prefix_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (start : PositionCfg Γ Λ R) (n : Nat) (bound : n ≤ PositionedRotationMachine.remainingSteps start) :
    (next caller)^[n] (some (positionCfg start)) =
      ((PositionedRotationMachine.next localCaller)^[n] (some start)).map positionCfg := by
  apply position_prefix_transport caller localCaller n start
  intro j strict
  obtain ⟨reached, executed, _, _, owned⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start j (by omega)
  exact ⟨reached, executed, owned.mp (by omega)⟩

/-- Every inclusive parser prefix frames all four complementary tree stores. -/
theorem move_phase_prefix_frame (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (executed : (next caller)^[n] (some (cfg (some (moveLabel q)) regs D ctx)) = some reached) :
    reached.var = (if n = 0 then regs else resetMove regs) ∧
      reached.var.2 = regs.2 ∧
      reached.stk (.inl .source) = D.source ∧ reached.stk (.inl .saved) = D.saved ∧
      reached.stk (.inl .scratch) = D.scratch ∧ reached.stk (.inl .pending) = D.pending ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  have canonical := move_prefix_reset caller q D regs ctx n reached bound executed
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let start : MoveCfg Γ Λ R :=
    moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start n bound
  have actual := move_owned_prefix_transport caller localCaller start n bound
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans actual)
  have frame := (MoveParserMachine.prefix_preserves localCaller start localReached n bound localRun).2.1
  refine ⟨canonical, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonical]
    split <;> rfl
  · rw [same, moveCfg_source]
    exact frame (.inl .source)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .saved))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .saved)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .scratch))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .scratch)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .pending))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .pending)
  · intro k
    rw [same, moveCfg_context]
    exact frame (.inr k)

/-- Every inclusive Position prefix frames the certificate and reverse-path stores. -/
theorem position_phase_prefix_frame (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (executed : (next caller)^[n] (some (cfg (some (positionLabel q)) regs D ctx)) = some reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .certificate) = D.certificate ∧
      reached.stk (.inl .moveReverse) = D.moveReverse ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  have canonical := position_prefix_reset caller q D regs ctx n reached bound executed
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
  have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
    rw [positionCfg_view]
    rfl
  obtain ⟨localReached, localRun, _, _, _⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start n bound
  have actual := position_owned_prefix_transport caller localCaller start n bound
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = positionCfg localReached := Option.some.inj (executed.symm.trans actual)
  have frame := (PositionedRotationMachine.prefix_frame localCaller start localReached n bound localRun).2
  refine ⟨canonical, ?_, ?_, ?_, ?_⟩
  · rw [canonical]
    split <;> rfl
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
      localReached.stk (positionStackEquiv (.inr (.inl .certificate))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .certificate)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
      localReached.stk (positionStackEquiv (.inr (.inl .moveReverse))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .moveReverse)
  · intro k
    rw [same, positionCfg_context]
    exact frame (.inr k)


/-!
## Actual source observations and the physical parsed position

Scratch implementation suffix, released after the recorded scope42 baseline.
The initial source-observation prefix passed its separately recorded helper
check. The evolving complete suffix still requires its actual core-dependent
endpoint/timing/sharp-family check; no complete check is claimed by this
comment. None of these definitions is installed in a runtime callback.
-/

/-- The old physical path follows the newly parsed path without a runtime copy. -/
def physicalMove (move : RotationMove) (oldPath : List Branch) : RotationMove :=
  ⟨move.direction, move.position ++ oldPath⟩

@[simp] theorem physicalMove_direction (move : RotationMove) (oldPath : List Branch) :
    (physicalMove move oldPath).direction = move.direction := rfl

@[simp] theorem physicalMove_position (move : RotationMove) (oldPath : List Branch) :
    (physicalMove move oldPath).position = move.position ++ oldPath := rfl

@[simp] theorem physicalMove_nil (move : RotationMove) : physicalMove move [] = move := by
  cases move
  simp [physicalMove]

/-- The actual measured source result on the full physically installed position. -/
def representedValue (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit) :
    Option (BinaryTree Unit) := (applyMoveRun (physicalMove move oldPath) s).1

/-- Literal restoration of old saved data around the represented source result. -/
def representedSource (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved suffix : Word) : Word :=
  saved.reverse ++ treeCode ((representedValue move oldPath s).getD s) ++ suffix

/-- Parser activations, one paid dispatch, actual Position time and old saved pops. -/
def representedSteps (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved : Word) : Nat :=
  2 * move.position.length + 4 +
    PositionedRotationMachine.representedClock move.direction (move.position ++ oldPath) s +
      saved.length

/-- Two existing source observations; this does not introduce a new runtime tariff. -/
def sourceObservationCost (raw : Word) (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) : Nat :=
  (parseMoveRun raw).2 + (applyMoveRun (physicalMove move oldPath) s).2

theorem representedValue_eq_applyMove (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedValue move oldPath s = Trees.Rotations.applyMove? (physicalMove move oldPath) s :=
  applyMoveRun_value (physicalMove move oldPath) s

theorem representedValue_numNodes (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    t.numNodes = s.numNodes :=
  applyMoveRun_numNodes (physicalMove move oldPath) s t returned

theorem representedSource_length (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word) :
    (representedSource move oldPath s saved suffix).length =
      saved.length + 2 * s.numNodes + 1 + suffix.length := by
  unfold representedSource
  cases actual : representedValue move oldPath s with
  | none =>
      simp only [Option.getD_none, List.length_append, List.length_reverse,
        treeCode_length, Nat.add_assoc]
  | some t =>
      simp only [Option.getD_some, List.length_append, List.length_reverse,
        treeCode_length, representedValue_numNodes move oldPath s t actual, Nat.add_assoc]

theorem representedSource_of_none (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word)
    (failed : representedValue move oldPath s = none) :
    representedSource move oldPath s saved suffix = saved.reverse ++ treeCode s ++ suffix := by
  simp only [representedSource, failed, Option.getD_none]

theorem representedSource_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix : Word)
    (returned : representedValue move oldPath s = some t) :
    representedSource move oldPath s saved suffix = saved.reverse ++ treeCode t ++ suffix := by
  simp only [representedSource, returned, Option.getD_some]

/-- Old saved data is cancelled before the uniquely decoded tree and suffix are compared. -/
theorem representedSource_success_injective (move : RotationMove) (oldPath : List Branch)
    (s t other : BinaryTree Unit) (saved suffix otherSuffix : Word)
    (returned : representedValue move oldPath s = some t)
    (output : representedSource move oldPath s saved suffix =
      saved.reverse ++ treeCode other ++ otherSuffix) :
    t = other ∧ suffix = otherSuffix := by
  rw [representedSource_of_some move oldPath s t saved suffix returned] at output
  have prefixed : saved.reverse ++ (treeCode t ++ suffix) =
      saved.reverse ++ (treeCode other ++ otherSuffix) := by
    simpa only [List.append_assoc] using output
  exact parseTreeRun_prefix_injective t other suffix otherSuffix
    (List.append_cancel_left prefixed)

theorem source_application_cost_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    (applyMoveRun (physicalMove move oldPath) s).2 =
      3 * (move.position ++ oldPath).length + 5 :=
  applyMoveRun_cost_of_some (physicalMove move oldPath) s t returned

/-- The failure tariff follows the actual stopped source cursor, separately from the physical path tail. -/
theorem source_application_cost_eq_stopped (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    (applyMoveRun (physicalMove move oldPath) s).2 =
      if (representedValue move oldPath s).isSome then
        3 * PositionedRotationMachine.descentCount (move.position ++ oldPath) s + 5
      else 2 * PositionedRotationMachine.descentCount (move.position ++ oldPath) s +
        if PositionedRotationMachine.stoppedPath (move.position ++ oldPath) s = [] then 3 else 2 :=
  PositionedRotationMachine.source_cost_eq_stopped move.direction (move.position ++ oldPath) s

theorem sourceObservationCost_of_parse (raw : Word) (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    sourceObservationCost raw move oldPath s =
      3 * move.position.length + 4 + (applyMoveRun (physicalMove move oldPath) s).2 := by
  unfold sourceObservationCost
  rw [parseMoveRun_cost_of_some raw move rest parsed]

/-- The certificate itself, rather than a consumed final path, fixes the parsed move and remainder. -/
theorem parsed_prefix_unique (raw : Word) (move other : RotationMove) (rest otherRest : Word)
    (first : (parseMoveRun raw).1 = some (move, rest))
    (second : (parseMoveRun raw).1 = some (other, otherRest)) :
    move = other ∧ rest = otherRest := by
  have left := (parseMoveRun_iff raw move rest).mp first
  have right := (parseMoveRun_iff raw other otherRest).mp second
  exact parseMoveRun_prefix_injective move other rest otherRest (left.symm.trans right)

theorem sourceObservationCost_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest))
    (returned : representedValue move oldPath s = some t) :
    sourceObservationCost raw move oldPath s =
      3 * move.position.length + 3 * (move.position ++ oldPath).length + 9 := by
  unfold sourceObservationCost
  rw [parseMoveRun_cost_of_some raw move rest parsed,
    source_application_cost_of_some move oldPath s t returned]
  omega

theorem sourceObservationCost_code (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit)
    (returned : representedValue move oldPath s = some t) :
    sourceObservationCost (moveCode move ++ rest) move oldPath s =
      3 * move.position.length + 3 * (move.position ++ oldPath).length + 9 := by
  apply sourceObservationCost_of_some _ move rest oldPath s t
  · exact congrArg Prod.fst (parseMoveRun_code move rest)
  · exact returned

theorem sourceObservationCost_clean (raw : Word) (move : RotationMove) (rest : Word)
    (s t : BinaryTree Unit) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (returned : representedValue move [] s = some t) :
    sourceObservationCost raw move [] s = 6 * move.position.length + 9 := by
  rw [sourceObservationCost_of_some raw move rest [] s t parsed returned, List.append_nil]
  omega

theorem parser_failure_source_cost (raw : Word) (failed : (parseMoveRun raw).1 = none) :
    (parseMoveRun raw).2 = MoveParserMachine.fullSteps raw + 1 :=
  MoveParserMachine.parseMoveRun_failure_cost raw failed

theorem representedSteps_clean (move : RotationMove) (s : BinaryTree Unit) (saved : Word) :
    representedSteps move [] s saved =
      2 * move.position.length + 4 +
        PositionedRotationMachine.representedClock move.direction move.position s + saved.length := by
  simp only [representedSteps, List.append_nil]

theorem representedSteps_saved_append (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (left right : Word) :
    representedSteps move oldPath s (left ++ right) =
      representedSteps move oldPath s left + right.length := by
  simp only [representedSteps, List.length_append]
  omega


end Resources.RotationCertificate.MoveApplyMachine

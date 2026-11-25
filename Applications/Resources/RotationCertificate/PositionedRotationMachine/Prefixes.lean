import Applications.Resources.RotationCertificate.PositionedRotationMachine.Represented

/-!
# PositionedRotationMachine: Prefixes
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.PositionedRotationMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Inclusive prefixes, first return, frame and timed data -/

section PrefixBoundary

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  rfl

/-- One actual reached configuration, including the first live handoff. -/
theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) := by
  exact BinaryCounter.FixedWidthMachine.ranked_prefix_eq (step caller) (step other) remainingSteps
    (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

theorem ambient_prefix_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = block q)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) =
      (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact prefix_caller_independent caller (fun external => ambient (.inr external)) start n bound

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, frame⟩ := local_step_data caller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2 k)⟩
      rw [registers]
      exact ih.1

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

/-- At zero the entire original register survives; positive owned prefixes reset it. -/
theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = if n = 0 then start.var else reset start.var := by
  induction n generalizing start reached with
  | zero =>
      have equal : start = reached := Option.some.inj executed
      subst reached
      rfl
  | succ n ih =>
      have positive : 0 < remainingSteps start := by omega
      obtain ⟨middle, first, decreased⟩ := local_progress caller start positive
      have owned := (remainingSteps_pos_iff start).mp positive
      have registers := (local_step_data caller ⟨owned, first⟩).2.1
      rw [Function.iterate_succ_apply, next_some, first] at executed
      simp only [Nat.succ_ne_zero, ite_false]
      simpa only [registers, reset_reset, ite_self] using
        ih middle reached (by omega) executed

theorem prefix_reset_of_pos (start reached : Cfg Γ Λ R) (n : Nat)
    (positive : 0 < n) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = reset start.var := by
  simpa only [Nat.ne_of_gt positive, ite_false] using prefix_reset caller start reached n bound executed

/-- The reset and protected frame refer to the same inclusive-prefix witness. -/
theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = (if n = 0 then start.var else reset start.var) ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, ownership⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, ownership, ?_,
    prefix_reset caller start reached n bound executed,
    (prefix_frame caller start reached n bound executed).2⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l := by
  simp [phaseResult, cfg, resultLabel, Owned]

/-- An owned entry ends at its specified live result before its caller runs. -/
theorem phase_first_return (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D]
        (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) ∧
      ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l ∧
      ∀ n, n < phaseSteps q D → ∃ reached,
        (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached ∧
          Owned reached.l := by
  refine ⟨phase_iterate caller q D regs ctx, phaseResult_not_owned q regs D ctx, ?_⟩
  intro n strict
  have bound : n ≤ remainingSteps (cfg (some (phaseLabel q)) regs D ctx : Cfg Γ Λ R) := by
    change n ≤ phaseSteps q D
    omega
  obtain ⟨reached, executed, _, _, ownership⟩ :=
    owned_prefix caller (cfg (some (phaseLabel q)) regs D ctx) n bound
  exact ⟨reached, executed, ownership.mp strict⟩

theorem first_return_exact (start : Cfg Γ Λ R) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (external : ¬ Owned reached.l) : n = remainingSteps start := by
  obtain ⟨actual, run, _, _, ownership⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  by_contra different
  have strict : n < remainingSteps start := by omega
  exact external (ownership.mp strict)

/-- Strict earlier ownership excludes a later caller-created or reentered result. -/
theorem first_return_unique (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (external : ¬ Owned reached.l)
    (earlier : ∀ k, k < n → ∃ before,
      (next caller)^[k] (some (cfg (some (phaseLabel q)) regs D ctx)) = some before ∧
        Owned before.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  have bound : n ≤ phaseSteps q D := by
    by_contra bad
    have strict : phaseSteps q D < n := by omega
    obtain ⟨before, arrived, owned⟩ := earlier (phaseSteps q D) strict
    have same : before = phaseResult q regs D ctx :=
      Option.some.inj (arrived.symm.trans (phase_iterate caller q D regs ctx))
    rw [same] at owned
    exact phaseResult_not_owned q regs D ctx owned
  have exactCount : n = phaseSteps q D :=
    first_return_exact caller (cfg (some (phaseLabel q)) regs D ctx) n reached bound executed external
  refine ⟨exactCount, ?_⟩
  rw [exactCount] at executed
  exact Option.some.inj (executed.symm.trans (phase_iterate caller q D regs ctx))

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def runInTimeExact (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (3 * raw.length + path.length + 5) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := runSteps_le d raw path

def runInConservativeTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (4 * raw.length + path.length + 12) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := runSteps_le_conservative d raw path

end PrefixBoundary

/-! ## All-raw provenance, cleanup and literal rollback -/

/-- Literal provenance is retained until failure has restored the original word.
Successful rewriting keeps its cleanup conditions and uses tag conservation. -/
def RawOrigin (original : Word) : Control → LocalData → Prop
  | .inl (.seek _), D =>
      D.scratch = [] ∧ D.pending = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.scanPrefix _), D =>
      D.scratch = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.start _), D =>
      D.scratch = [] ∧ D.pending = [] ∧ D.path = [] ∧
        original = D.saved.reverse ++ D.source
  | .inl (.scanScratch d), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ markerWord (scratchFailure d) ++ D.scratch.reverse ++ D.source
  | .inl .checkRight, D =>
      D.pending = [] ∧ D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .failureLeft), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .failureRight), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag, nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .successLeft), D
  | .inl (.restoreScratch .successRight), D => D.pending = [] ∧ D.path = []
  | .inl .dropPending, D =>
      D.scratch = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.restorePrefix .failure), D =>
      D.scratch = [] ∧ D.pending = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.restorePrefix .success), D =>
      D.scratch = [] ∧ D.pending = [] ∧ D.path = []
  | .inr .failure, D =>
      D.saved = [] ∧ D.scratch = [] ∧ D.pending = [] ∧ D.source = original
  | .inr .success, D =>
      D.saved = [] ∧ D.scratch = [] ∧ D.pending = [] ∧ D.path = []

theorem advance_rawOrigin (original : Word) (q : Phase) (D : LocalData)
    (origin : RawOrigin original (.inl q) D) :
    RawOrigin original (advance q D).1 (advance q D).2 := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q
  case' seek d =>
    cases path
    case' cons b path =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' pos => cases b
  case' scanPrefix d =>
    cases raw
    case' cons tag raw =>
      by_cases node : tag = nodeTag
      case' neg =>
        by_cases empty : tag = emptyTag
        case' pos => by_cases finished : pending.tail = []
  case' start d =>
    cases d
    case' left =>
      cases raw
      case' cons tag raw => by_cases node : tag = nodeTag
    case' right =>
      cases raw
      case' cons first raw =>
        cases raw
        case' cons second raw =>
          by_cases firstNode : first = nodeTag <;> by_cases secondNode : second = nodeTag
  case' scanScratch d =>
    cases d
    case' left =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' neg =>
          by_cases empty : tag = emptyTag
          case' pos => by_cases finished : pending.tail = []
    case' right =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' neg =>
          by_cases empty : tag = emptyTag
          case' pos => by_cases finished : pending.tail = []
  case' checkRight =>
    cases raw
    case' cons tag raw => by_cases node : tag = nodeTag
  case' restoreScratch mode => cases mode <;> cases scratch
  case' dropPending => cases pending
  case' restorePrefix r => cases r <;> cases saved
  all_goals simp_all [RawOrigin, advance, markerWord, modeResult, scratchFailure,
    List.reverse_cons, List.append_assoc]

/-- A local activation only removes path heads. This holds in arbitrary dirty data. -/
theorem advance_path_suffix (q : Phase) (D : LocalData) :
    ∃ consumed, D.path = consumed ++ (advance q D).2.path := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => exact ⟨[], rfl⟩
      | cons b path =>
          refine ⟨[b], ?_⟩
          cases raw with
          | nil => rfl
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> simp [advance, node]
              · simp [advance, node]
  | scanPrefix d =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, node]
          · by_cases empty : tag = emptyTag <;> simp [advance, node, empty]
  | start d =>
      refine ⟨[], ?_⟩
      cases d with
      | left =>
          cases raw with
          | nil => rfl
          | cons tag raw => by_cases node : tag = nodeTag <;> simp [advance, node]
      | right =>
          cases raw with
          | nil => rfl
          | cons first raw =>
              cases raw with
              | nil => rfl
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;> simp [advance, nodes]
  | scanScratch d =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, node]
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> simp [advance, empty, finished]
              · simp [advance, empty, finished]
            · simp [advance, node, empty]
  | checkRight =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw => by_cases node : tag = nodeTag <;> simp [advance, node]
  | restoreScratch mode =>
      refine ⟨[], ?_⟩
      cases scratch <;> rfl
  | dropPending =>
      refine ⟨[], ?_⟩
      cases pending <;> rfl
  | restorePrefix r =>
      refine ⟨[], ?_⟩
      cases saved <;> rfl

def RawInvariant (original : Word) (c : Cfg Γ Λ R) : Prop :=
  match c.l with
  | some (.inl q) => RawOrigin original (.inl q) (dataOfCfg c)
  | some (.inr (.inl r)) => RawOrigin original (.inr r) (dataOfCfg c)
  | _ => False

omit [DecidableEq K] in
@[simp] theorem rawInvariant_control_cfg (original : Word) (control : Control)
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    RawInvariant original (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) ↔
      RawOrigin original control D := by
  cases control <;> rfl

theorem local_step_rawInvariant (original : Word) {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) (origin : RawInvariant original before) :
    RawInvariant original after := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  rw [rawInvariant_control_cfg]
  exact advance_rawOrigin original q D origin

theorem local_reaches_rawInvariant (original : Word) {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached)
    (origin : RawInvariant original start) : RawInvariant original reached := by
  induction path with
  | refl => exact origin
  | @tail before after _ transition ih => exact local_step_rawInvariant caller original transition ih

theorem local_step_path_suffix {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    ∃ consumed, before.stk (.inl .path) = consumed ++ after.stk (.inl .path) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  exact advance_path_suffix q D

theorem local_reaches_path_suffix {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    ∃ consumed, start.stk (.inl .path) = consumed ++ reached.stk (.inl .path) := by
  induction path with
  | refl => exact ⟨[], rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨first, hfirst⟩ := ih
      obtain ⟨last, hlast⟩ := local_step_path_suffix caller transition
      exact ⟨first ++ last, by rw [hfirst, hlast, List.append_assoc]⟩

/-- The clean all-raw result has no saved, scratch or pending residue. -/
theorem run_raw_clean (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    let finish : Cfg Γ Λ R := phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx
    finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  change RawOrigin raw (.inr (evaluate (.inl (.seek d))
    { source := raw, path := path }).result)
    (evaluate (.inl (.seek d)) { source := raw, path := path }).data at origin
  cases result : (evaluate (.inl (.seek d)) { source := raw, path := path }).result <;>
    simp only [result, RawOrigin] at origin <;>
    exact ⟨origin.1, origin.2.1, origin.2.2.1⟩

theorem run_raw_failure (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failure : (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).l =
      some (resultLabel .failure)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .source) = raw := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  simp only [RawInvariant, failure, resultLabel, RawOrigin] at origin
  exact origin.2.2.2

theorem run_raw_success (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (success : (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).l =
      some (resultLabel .success)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .path) = [] := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  simp only [RawInvariant, success, resultLabel, RawOrigin] at origin
  exact origin.2.2.2

theorem run_raw_path_suffix (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ consumed, path = consumed ++
      (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .path) :=
  local_reaches_path_suffix caller (LocalRun.reaches caller
    (phase_localRun caller (.seek d) { source := raw, path := path } regs ctx))

theorem run_raw_length (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .source)).length =
      raw.length := by
  have conserved := local_reaches_tag_debt caller (LocalRun.reaches caller
    (phase_localRun caller (.seek d) { source := raw, path := path } regs ctx))
  have clean := run_raw_clean caller d raw path regs ctx
  change ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .source)).length +
      ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .saved)).length +
      ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .scratch)).length + 0 =
      raw.length + 0 + 0 + 0 at conserved
  simpa only [clean.1, clean.2.1, List.length_nil, Nat.add_zero] using conserved

/-- Actual first-result execution for every raw word and every path. -/
theorem run_raw (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      LocalRun caller (runSteps d raw path) (entry d regs raw path ctx)
        (cfg (some (resultLabel result)) (reset regs) { source := output, path := rest } ctx) ∧
      output.length = raw.length ∧ (∃ consumed, path = consumed ++ rest) ∧
      (result = .failure → output = raw) ∧ (result = .success → rest = []) := by
  let E := evaluate (.inl (.seek d)) { source := raw, path := path }
  have cleaned := run_raw_clean caller d raw path regs ctx
  change E.data.saved = [] ∧ E.data.scratch = [] ∧ E.data.pending = [] at cleaned
  have data_eq : E.data = { source := E.data.source, path := E.data.path } := by
    cases data : E.data
    simp_all only
  refine ⟨E.result, E.data.source, E.data.path, ?_, run_raw_length caller d raw path regs ctx,
    run_raw_path_suffix caller d raw path regs ctx, ?_, ?_⟩
  · have run := phase_localRun caller (.seek d) { source := raw, path := path } regs ctx
    change LocalRun caller (runSteps d raw path) (entry d regs raw path ctx)
      (cfg (some (resultLabel E.result)) (reset regs) E.data ctx) at run
    rw [data_eq] at run
    exact run
  · intro failed
    apply run_raw_failure caller d raw path regs ctx
    exact congrArg (fun r => some (resultLabel r)) failed
  · intro succeeded
    apply run_raw_success caller d raw path regs ctx
    exact congrArg (fun r => some (resultLabel r)) succeeded



end Resources.RotationCertificate.PositionedRotationMachine

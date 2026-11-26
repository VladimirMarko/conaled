import Applications.Resources.RotationCertificate.MoveApplyMachine.Basic

/-!
# MoveApplyMachine: Execution
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl
@[simp] theorem next_none : next caller none = none := rfl

theorem dispatch_step (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel r)) regs D ctx) =
      some (cfg (some (dispatchTarget r)) (reset regs) D ctx) := rfl

theorem iterate_step (n : Nat) (before after : Cfg Γ Λ R)
    (transition : step caller before = some after) :
    (next caller)^[n + 1] (some before) = (next caller)^[n] (some after) := by
  rw [Function.iterate_succ_apply, next_some, transition]

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

inductive LocalRun : Nat → Cfg Γ Λ R → Cfg Γ Λ R → Prop
  | refl (c) : LocalRun 0 c c
  | cons {n before middle after} (head : LocalStep caller before middle)
      (tail : LocalRun n middle after) : LocalRun (n + 1) before after

theorem LocalRun.single {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : LocalRun caller 1 before after :=
  .cons transition (.refl after)

theorem phase_step_localRun {q : Phase} {D : LocalData} {regs : Registers R}
    {ctx : ∀ k, List (Γ k)} {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (phaseLabel q)) regs D ctx) = some after) :
    LocalRun caller 1 (cfg (some (phaseLabel q)) regs D ctx) after :=
  LocalRun.single caller ⟨owned_phase q, executed⟩

theorem LocalRun.head {n : Nat} {a b : Cfg Γ Λ R}
    (run : LocalRun caller n a b) (positive : 0 < n) :
    ∃ middle, LocalStep caller a middle := by
  cases run with
  | refl => omega
  | cons first tail => exact ⟨_, first⟩

theorem LocalRun.trans {m n : Nat} {a b c : Cfg Γ Λ R}
    (first : LocalRun caller m a b) (second : LocalRun caller n b c) :
    LocalRun caller (m + n) a c := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | @cons k before middle after head tail ih =>
      simpa only [show k + 1 + n = k + n + 1 by omega] using
        LocalRun.cons head (ih second)

theorem LocalRun.iterate {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    (next caller)^[n] (some a) = some b := by
  induction run with
  | refl => rfl
  | @cons n before middle after head tail ih =>
      rw [iterate_step caller n before middle head.2]
      exact ih

theorem LocalRun.reaches {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    Relation.ReflTransGen (LocalStep caller) a b := by
  induction run with
  | refl => exact .refl
  | cons head tail ih => exact (Relation.ReflTransGen.single head).trans ih

theorem LocalRun.owned_prefix {n : Nat} {a b : Cfg Γ Λ R}
    (run : LocalRun caller n a b) (j : Nat) (strict : j < n) :
    ∃ reached, (next caller)^[j] (some a) = some reached ∧ Owned reached.l := by
  induction run generalizing j with
  | refl => omega
  | @cons n before middle after head tail ih =>
      cases j with
      | zero => exact ⟨before, rfl, head.1⟩
      | succ j =>
          obtain ⟨reached, executed, owned⟩ := ih j (by omega)
          exact ⟨reached, (iterate_step caller j before middle head.2).trans executed, owned⟩

theorem LocalRun.of_iterate {n : Nat} {a b : Cfg Γ Λ R}
    (executed : (next caller)^[n] (some a) = some b)
    (earlier : ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some a) = some reached ∧ Owned reached.l) :
    LocalRun caller n a b := by
  induction n generalizing b with
  | zero =>
      have same : a = b := Option.some.inj executed
      subst b
      exact .refl a
  | succ n ih =>
      obtain ⟨middle, arrived, owned⟩ := earlier n (by omega)
      have first := ih arrived (fun j strict => earlier j (by omega))
      have last : step caller middle = some b := by
        simpa only [Function.iterate_succ_apply', arrived, next_some] using executed
      exact LocalRun.trans caller first (LocalRun.single caller ⟨owned, last⟩)

/-- Determinism and strict ownership fix the first live handoff independently of any rank. -/
theorem LocalRun.first_unique {n m : Nat} {a b c : Cfg Γ Λ R}
    (first : LocalRun caller n a b) (second : LocalRun caller m a c)
    (bReturn : ¬ Owned b.l) (cReturn : ¬ Owned c.l) : n = m ∧ b = c := by
  induction first generalizing m c with
  | refl a =>
      cases second with
      | refl => exact ⟨rfl, rfl⟩
      | cons head tail => exact False.elim (bReturn head.1)
  | @cons n before middle after head tail ih =>
      cases second with
      | refl => exact False.elim (cReturn head.1)
      | @cons m _ other finish otherHead otherTail =>
          have same : middle = other := Option.some.inj (head.2.symm.trans otherHead.2)
          subst other
          obtain ⟨count, endpoint⟩ := ih otherTail bReturn cReturn
          exact ⟨congrArg (fun k => k + 1) count, endpoint⟩

omit [DecidableEq K] in
def toMoveCfg (c : Cfg Γ Λ R) : MoveCfg Γ Λ R :=
  moveView (c.l.map moveLabelEquiv.symm) (moveRegisterEquiv.symm c.var)
    (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
def toPositionCfg (c : Cfg Γ Λ R) : PositionCfg Γ Λ R :=
  positionView (c.l.map positionLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
theorem moveCfg_toMoveCfg (c : Cfg Γ Λ R) : moveCfg (toMoveCfg c) = c := by
  unfold toMoveCfg
  rw [moveCfg_view, Equiv.apply_symm_apply]
  have labelEq : (c.l.map moveLabelEquiv.symm).map moveLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

omit [DecidableEq K] in
theorem positionCfg_toPositionCfg (c : Cfg Γ Λ R) : positionCfg (toPositionCfg c) = c := by
  unfold toPositionCfg
  rw [positionCfg_view]
  have labelEq : (c.l.map positionLabelEquiv.symm).map positionLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

omit [DecidableEq K] in
theorem owned_moveCfg (c : MoveCfg Γ Λ R) (owned : MoveParserMachine.Owned c.l) :
    Owned (moveCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, MoveParserMachine.Owned] at owned
  | some label =>
      cases label with
      | inl q => change Owned (c.l.map moveLabelEquiv); rw [labelEq]; trivial
      | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned

omit [DecidableEq K] in
theorem owned_positionCfg (c : PositionCfg Γ Λ R) (owned : PositionedRotationMachine.Owned c.l) :
    Owned (positionCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, PositionedRotationMachine.Owned] at owned
  | some label =>
      cases label with
      | inl q => change Owned (c.l.map positionLabelEquiv); rw [labelEq]; trivial
      | inr external => simp only [labelEq, PositionedRotationMachine.Owned] at owned

theorem move_step_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (c : MoveCfg Γ Λ R) (owned : MoveParserMachine.Owned c.l) :
    step caller (moveCfg c) = (MoveParserMachine.step localCaller c).map moveCfg := by
  exact FrontEndMachine.Transport.step_owned moveStackEquiv moveSymbolEquiv moveRegisterEquiv
    moveLabelEquiv (MoveParserMachine.program localCaller) (program caller) MoveParserMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) c owned

theorem position_step_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (c : PositionCfg Γ Λ R) (owned : PositionedRotationMachine.Owned c.l) :
    step caller (positionCfg c) = (PositionedRotationMachine.step localCaller c).map positionCfg := by
  exact FrontEndMachine.Transport.step_owned positionStackEquiv positionSymbolEquiv (Equiv.refl _)
    positionLabelEquiv (PositionedRotationMachine.program localCaller) (program caller)
    PositionedRotationMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) c owned

theorem move_prefix_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (n : Nat) (start : MoveCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (MoveParserMachine.next localCaller)^[j] (some start) = some reached ∧
        MoveParserMachine.Owned reached.l) :
    (next caller)^[n] (some (moveCfg start)) =
      ((MoveParserMachine.next localCaller)^[n] (some start)).map moveCfg := by
  exact FrontEndMachine.Transport.iterate_owned moveStackEquiv moveSymbolEquiv moveRegisterEquiv
    moveLabelEquiv (MoveParserMachine.program localCaller) (program caller) MoveParserMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) n start earlier

theorem position_prefix_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (n : Nat) (start : PositionCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (PositionedRotationMachine.next localCaller)^[j] (some start) = some reached ∧
        PositionedRotationMachine.Owned reached.l) :
    (next caller)^[n] (some (positionCfg start)) =
      ((PositionedRotationMachine.next localCaller)^[n] (some start)).map positionCfg := by
  exact FrontEndMachine.Transport.iterate_owned positionStackEquiv positionSymbolEquiv (Equiv.refl _)
    positionLabelEquiv (PositionedRotationMachine.program localCaller) (program caller)
    PositionedRotationMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) n start earlier

/-- Every partial Position segment transports literally, including scans and restores. -/
theorem position_localRun_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    {n : Nat} {a b : PositionCfg Γ Λ R} (run : PositionedRotationMachine.LocalRun localCaller n a b) :
    LocalRun caller n (positionCfg a) (positionCfg b) := by
  induction run with
  | refl => exact .refl _
  | @cons n before middle after head tail ih =>
      refine .cons ⟨owned_positionCfg before head.1, ?_⟩ ih
      rw [position_step_transport caller localCaller before head.1, head.2]
      rfl

theorem move_phase_transport (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
      (cfg (some (moveLabel q)) regs D ctx)
      (moveCfg (MoveParserMachine.phaseResult q (moveRegisterEquiv.symm regs)
        D.certificate D.moveReverse D.path (moveContext D ctx))) := by
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
    fun _ => .halt
  let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  have strictPrefix := (MoveParserMachine.phase_first_return localCaller q D.certificate
    D.moveReverse D.path (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  apply LocalRun.of_iterate caller
  · rw [← startEq, move_prefix_transport caller localCaller _ start strictPrefix]
    have whole : (MoveParserMachine.next localCaller)^[MoveParserMachine.phaseSteps q D.certificate D.moveReverse]
        (some start) = some (MoveParserMachine.phaseResult q (moveRegisterEquiv.symm regs)
          D.certificate D.moveReverse D.path (moveContext D ctx)) :=
      MoveParserMachine.phase_iterate localCaller q D.certificate D.moveReverse D.path
        (moveRegisterEquiv.symm regs) (moveContext D ctx)
    rw [whole]
    rfl
  · intro j strict
    obtain ⟨reached, executed, owned⟩ := strictPrefix j strict
    refine ⟨moveCfg reached, ?_, owned_moveCfg reached owned⟩
    change (MoveParserMachine.next localCaller)^[j] (some start) = some reached at executed
    rw [← startEq, move_prefix_transport caller localCaller j start
      (fun k bound => strictPrefix k (by omega)), executed]
    rfl

theorem position_phase_transport (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (PositionedRotationMachine.phaseSteps q (positionData D))
      (cfg (some (positionLabel q)) regs D ctx)
      (positionCfg (PositionedRotationMachine.phaseResult q regs (positionData D)
        (positionContext D ctx))) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R :=
    fun _ => .halt
  have run := position_localRun_transport caller localCaller
    (PositionedRotationMachine.phase_localRun localCaller q (positionData D) regs (positionContext D ctx))
  change LocalRun caller _ (positionCfg (positionView _ regs D ctx)) _ at run
  rw [positionCfg_view] at run
  simpa only [Option.map_some, positionLabelEquiv_phase] using run

theorem dispatch_localRun (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (dispatchLabel r)) regs D ctx)
      (cfg (some (dispatchTarget r)) (reset regs) D ctx) :=
  LocalRun.single caller ⟨True.intro, dispatch_step caller r D regs ctx⟩

structure MoveFinish where
  result : MoveParserMachine.Result
  data : LocalData
  deriving DecidableEq

/-- Proof-side complete parser endpoint, retaining all protected tree stores. -/
def moveScanFinish (d : RotationDirection) (D : LocalData) :
    Option (List Branch × Word) → MoveFinish
  | none => ⟨.failure, { D with
      certificate := directionTag d :: (pathTags D.moveReverse.reverse ++ D.certificate)
      moveReverse := [] }⟩
  | some (p, rest) => ⟨.success d, { D with
      certificate := rest
      moveReverse := []
      path := D.moveReverse.reverse ++ p ++ D.path }⟩

def moveFinish (q : MoveParserMachine.Phase) (D : LocalData) : MoveFinish :=
  match q with
  | .start => match D.certificate with
      | [] => ⟨.failure, D⟩
      | tag :: raw =>
          if tag = rotateLeftTag then
            moveScanFinish .left { D with certificate := raw } (parsePathRun raw).1
          else if tag = rotateRightTag then
            moveScanFinish .right { D with certificate := raw } (parsePathRun raw).1
          else ⟨.failure, D⟩
  | .scan d => moveScanFinish d D (parsePathRun D.certificate).1
  | .emit d => ⟨.success d, { D with moveReverse := [], path := D.moveReverse.reverse ++ D.path }⟩
  | .undo d => ⟨.failure, { D with
      certificate := directionTag d :: (pathTags D.moveReverse.reverse ++ D.certificate)
      moveReverse := [] }⟩

omit [DecidableEq K] in
theorem moveScanFinish_transport (d : RotationDirection) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (parsed : Option (List Branch × Word)) :
    moveCfg (Λ := Λ) (MoveParserMachine.scanResult d regs D.certificate D.moveReverse D.path
      (moveContext D ctx) parsed) =
      cfg (some (dispatchLabel (moveScanFinish d D parsed).result))
        (resetMove (moveRegisterEquiv regs)) (moveScanFinish d D parsed).data ctx := by
  cases parsed with
  | none =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
        (MoveParserMachine.reset regs) (moveScanFinish d D none).data ctx) = _
      rw [moveCfg_view]
      rfl
  | some pair =>
      rcases pair with ⟨p, rest⟩
      change moveCfg (moveView (some (MoveParserMachine.resultLabel (.success d)))
        (MoveParserMachine.reset regs) (moveScanFinish d D (some (p, rest))).data ctx) = _
      rw [moveCfg_view]
      rfl

omit [DecidableEq K] in
theorem moveFinish_transport (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k)) :
    moveCfg (Λ := Λ) (MoveParserMachine.phaseResult q regs D.certificate D.moveReverse D.path
      (moveContext D ctx)) =
      cfg (some (dispatchLabel (moveFinish q D).result))
        (resetMove (moveRegisterEquiv regs)) (moveFinish q D).data ctx := by
  cases q with
  | start =>
      rcases D with ⟨raw, rev, path, source, saved, scratch, pending⟩
      cases raw with
      | nil =>
          change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
            (MoveParserMachine.reset regs) ⟨[], rev, path, source, saved, scratch, pending⟩ ctx) = _
          rw [moveCfg_view]
          rfl
      | cons tag raw =>
          by_cases left : tag = rotateLeftTag
          · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
              left, ite_true]
            exact moveScanFinish_transport .left ⟨raw, rev, path, source, saved, scratch, pending⟩ regs ctx _
          · by_cases right : tag = rotateRightTag
            · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
                right, ite_true]
              exact moveScanFinish_transport .right ⟨raw, rev, path, source, saved, scratch, pending⟩ regs ctx _
            · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
                left, ite_false, right]
              change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
                (MoveParserMachine.reset regs) ⟨tag :: raw, rev, path, source, saved, scratch, pending⟩ ctx) = _
              rw [moveCfg_view]
              rfl
  | scan d => exact moveScanFinish_transport d D regs ctx _
  | emit d =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel (.success d)))
        (MoveParserMachine.reset regs) (moveFinish (.emit d) D).data ctx) = _
      rw [moveCfg_view]
      rfl
  | undo d =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
        (MoveParserMachine.reset regs) (moveFinish (.undo d) D).data ctx) = _
      rw [moveCfg_view]
      rfl

theorem move_phase_localRun (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
      (cfg (some (moveLabel q)) regs D ctx)
      (cfg (some (dispatchLabel (moveFinish q D).result)) (resetMove regs)
        (moveFinish q D).data ctx) := by
  have run := move_phase_transport caller q D regs ctx
  rw [moveFinish_transport, Equiv.apply_symm_apply] at run
  exact run

structure Evaluation where
  result : FinalResult
  data : LocalData
  steps : Nat
  deriving DecidableEq

/-- Proof-side Position result with the complementary physical stores retained. -/
def evaluatePosition (q : PositionedRotationMachine.Phase) (D : LocalData) : Evaluation :=
  let actual := PositionedRotationMachine.evaluate (.inl q) (positionData D)
  ⟨.inr actual.result, setPositionData D actual.data, actual.steps⟩

/-- The extra activation is the literal dispatch block, not a free handoff. -/
def evaluateDispatch (r : MoveParserMachine.Result) (D : LocalData) : Evaluation :=
  match r with
  | .failure => ⟨parseFailure, D, 1⟩
  | .success d =>
      let tail := evaluatePosition (.seek d) D
      ⟨tail.result, tail.data, 1 + tail.steps⟩

/-- A finite proof-side composition of the actual total component endpoints. -/
def evaluate (q : Phase) (D : LocalData) : Evaluation :=
  match q with
  | .inl q =>
      let parsed := moveFinish q D
      let tail := evaluateDispatch parsed.result parsed.data
      ⟨tail.result, tail.data,
        MoveParserMachine.phaseSteps q D.certificate D.moveReverse + tail.steps⟩
  | .inr (.inl r) => evaluateDispatch r D
  | .inr (.inr q) => evaluatePosition q D

def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate q D).steps

def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel (evaluate q D).result)) (reset regs) (evaluate q D).data ctx

omit [DecidableEq K] in
@[simp] theorem phaseResult_reset (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : phaseResult q (reset regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

omit [DecidableEq K] in
@[simp] theorem phaseResult_resetMove (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : phaseResult q (resetMove regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

omit [DecidableEq K] in
theorem position_finish_transport (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    positionCfg (Λ := Λ) (PositionedRotationMachine.phaseResult q regs (positionData D) (positionContext D ctx)) =
      phaseResult (positionPhase q) regs D ctx := by
  change positionCfg (positionView
    (some (PositionedRotationMachine.resultLabel
      (PositionedRotationMachine.evaluate (.inl q) (positionData D)).result))
    (reset regs) (setPositionData D
      (PositionedRotationMachine.evaluate (.inl q) (positionData D)).data) ctx) = _
  rw [positionCfg_view]
  rfl

theorem position_phase_localRun (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (PositionedRotationMachine.phaseSteps q (positionData D))
      (cfg (some (positionLabel q)) regs D ctx)
      (phaseResult (positionPhase q) regs D ctx) := by
  rw [← position_finish_transport]
  exact position_phase_transport caller q D regs ctx

theorem dispatch_phase_localRun (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps (dispatchPhase r) D)
      (cfg (some (dispatchLabel r)) regs D ctx)
      (phaseResult (dispatchPhase r) regs D ctx) := by
  cases r with
  | failure => exact dispatch_localRun caller .failure D regs ctx
  | success d =>
      have run := LocalRun.trans caller (dispatch_localRun caller (.success d) D regs ctx)
        (position_phase_localRun caller (.seek d) D (reset regs) ctx)
      simpa only [phaseSteps, phaseResult, evaluate, evaluateDispatch, evaluatePosition,
        dispatchPhase, positionPhase, PositionedRotationMachine.phaseSteps, reset_reset] using run

theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseResult q regs D ctx) := by
  cases q with
  | inl q =>
      have run := LocalRun.trans caller (move_phase_localRun caller q D regs ctx)
        (dispatch_phase_localRun caller (moveFinish q D).result (moveFinish q D).data (resetMove regs) ctx)
      simpa only [phaseSteps, phaseResult, phaseLabel, evaluate, dispatchPhase,
        reset_resetMove] using run
  | inr q =>
      cases q with
      | inl r => exact dispatch_phase_localRun caller r D regs ctx
      | inr q => exact position_phase_localRun caller q D regs ctx

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) :=
  LocalRun.iterate caller (phase_localRun caller q D regs ctx)

omit [DecidableEq K] in
theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  have dispatchPositive (r : MoveParserMachine.Result) (D : LocalData) :
      0 < (evaluateDispatch r D).steps := by
    cases r <;> simp only [evaluateDispatch] <;> omega
  cases q with
  | inl q =>
      have positive := dispatchPositive (moveFinish q D).result (moveFinish q D).data
      change 0 < MoveParserMachine.phaseSteps q D.certificate D.moveReverse +
        (evaluateDispatch (moveFinish q D).result (moveFinish q D).data).steps
      omega
  | inr q =>
      cases q with
      | inl r => exact dispatchPositive r D
      | inr q => exact PositionedRotationMachine.phaseSteps_pos q (positionData D)

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l :=
  not_owned_result _

theorem phase_first_return (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l ∧
      ∀ n, n < phaseSteps q D → ∃ reached,
        (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached ∧ Owned reached.l :=
  ⟨phaseResult_not_owned q regs D ctx, LocalRun.owned_prefix caller (phase_localRun caller q D regs ctx)⟩

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps (movePhase q) (dataOfCfg c)
  | some (.inr (.inl r)) => phaseSteps (dispatchPhase r) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseSteps (positionPhase q) (dataOfCfg c)
  | _ => 0

def finalCfg (c : Cfg Γ Λ R) : Cfg Γ Λ R :=
  match c.l with
  | some (.inl q) => phaseResult (movePhase q) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl r)) => phaseResult (dispatchPhase r) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseResult (positionPhase q) c.var (dataOfCfg c) (contextOfCfg c)
  | _ => c

omit [DecidableEq K] in
@[simp] theorem remainingSteps_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseSteps q D := by
  cases D
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
@[simp] theorem finalCfg_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseResult q regs D ctx := by
  cases D
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]
  | some label =>
      rcases label with q | (r | (q | external))
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ q regs D ctx, c = cfg (some (phaseLabel q)) regs D ctx := by
  cases labelEq : c.l with
  | none => simp only [labelEq, Owned] at owned
  | some label =>
      rcases label with q | (r | (q | external))
      · refine ⟨movePhase q, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, movePhase, moveLabel] using (cfg_eta c).symm
      · refine ⟨dispatchPhase r, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, dispatchPhase, dispatchLabel] using (cfg_eta c).symm
      · refine ⟨positionPhase q, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, positionPhase, positionLabel] using (cfg_eta c).symm
      · simp only [labelEq, Owned] at owned

omit [DecidableEq K] in
theorem nonowned_remaining (c : Cfg Γ Λ R) (returned : ¬ Owned c.l) : remainingSteps c = 0 := by
  have notPositive : ¬ 0 < remainingSteps c := fun h => returned ((remainingSteps_pos_iff c).mp h)
  omega

omit [DecidableEq K] in
theorem nonowned_finalCfg (c : Cfg Γ Λ R) (returned : ¬ Owned c.l) : finalCfg c = c := by
  cases labelEq : c.l with
  | none => simp only [finalCfg, labelEq]
  | some label =>
      rcases label with q | (r | (q | external))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · simp only [finalCfg, labelEq]

theorem cfg_localRun (c : Cfg Γ Λ R) : LocalRun caller (remainingSteps c) c (finalCfg c) := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [remainingSteps_phase_cfg, finalCfg_phase_cfg]
    exact phase_localRun caller q D regs ctx
  · rw [nonowned_remaining c owned, nonowned_finalCfg c owned]
    exact .refl c

omit [DecidableEq K] in
theorem finalCfg_not_owned (c : Cfg Γ Λ R) : ¬ Owned (finalCfg c).l := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [finalCfg_phase_cfg]
    exact phaseResult_not_owned q regs D ctx
  · rw [nonowned_finalCfg c owned]
    exact owned

theorem cfg_iterate (c : Cfg Γ Λ R) :
    (next caller)^[remainingSteps c] (some c) = some (finalCfg c) :=
  LocalRun.iterate caller (cfg_localRun caller c)

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := by
  have composed := LocalRun.cons transition (cfg_localRun caller after)
  exact (LocalRun.first_unique caller (cfg_localRun caller before) composed
    (finalCfg_not_owned before) (finalCfg_not_owned after)).1

theorem finalCfg_step {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    finalCfg before = finalCfg after := by
  exact (LocalRun.first_unique caller (cfg_localRun caller before)
    (LocalRun.cons transition (cfg_localRun caller after))
    (finalCfg_not_owned before) (finalCfg_not_owned after)).2

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨after, transition⟩ := LocalRun.head caller (cfg_localRun caller before) positive
  exact ⟨after, transition.2, local_step_remaining caller transition⟩

theorem LocalRun.remaining {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    remainingSteps a = n + remainingSteps b := by
  induction run with
  | refl => omega
  | cons head tail ih => have first := local_step_remaining caller head; omega

theorem LocalRun.finalCfg_eq {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    finalCfg a = finalCfg b := by
  induction run with
  | refl => rfl
  | cons head tail ih => exact (finalCfg_step caller head).trans ih

theorem LocalRun.phase_endpoint {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : FinalResult}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  exact LocalRun.first_unique caller (phase_localRun caller q D regs ctx) run
    (phaseResult_not_owned q regs D ctx) (not_owned_result r)

theorem first_return_unique (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (returned : ¬ Owned reached.l)
    (earlier : ∀ j, j < n → ∃ prior,
      (next caller)^[j] (some (cfg (some (phaseLabel q)) regs D ctx)) = some prior ∧ Owned prior.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  exact LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
    (phase_localRun caller q D regs ctx) returned (phaseResult_not_owned q regs D ctx)

theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

omit [DecidableEq K] in
theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q)) :
    ambient = program (fun external => ambient (.inr (.inr (.inr external)))) := by
  funext label
  rcases label with q | (r | (q | external))
  · exact agrees (movePhase q)
  · exact agrees (dispatchPhase r)
  · exact agrees (positionPhase q)
  · rfl

theorem ambient_prefix_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact prefix_caller_independent _ caller start n bound

theorem first_return_exact (start : Cfg Γ Λ R) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (returned : ¬ Owned reached.l) : n = remainingSteps start := by
  obtain ⟨actual, run, rank, path, ownership⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  have notStrict : ¬ n < remainingSteps start := fun h => returned (ownership.mp h)
  omega

theorem iterate_trans {start middle finish : Cfg Γ Λ R} {first second : Nat}
    (before : (next caller)^[first] (some start) = some middle)
    (after : (next caller)^[second] (some middle) = some finish) :
    (next caller)^[first + second] (some start) = some finish := by
  rw [Nat.add_comm first second, Function.iterate_add_apply, before, after]

omit [DecidableEq K] in
theorem moveCfg_context (c : MoveCfg Γ Λ R) (k : K) :
    (moveCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
    c.stk (moveStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem positionCfg_context (c : PositionCfg Γ Λ R) (k : K) :
    (positionCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
    c.stk (positionStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

theorem local_step_frame {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧ ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  cases q with
  | inl q =>
      let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
        fun _ => .halt
      let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
      have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
        rw [moveCfg_view]
        simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
      obtain ⟨middle, localStep, _⟩ := MoveParserMachine.local_progress localCaller start
        ((MoveParserMachine.remainingSteps_pos_iff start).mpr True.intro)
      have moved := move_step_transport caller localCaller start True.intro
      rw [localStep, Option.map_some, startEq] at moved
      have same : after = moveCfg middle := Option.some.inj (transition.2.symm.trans moved)
      obtain ⟨_, canonical, frame, _⟩ :=
        MoveParserMachine.local_step_data localCaller (before := start) ⟨True.intro, localStep⟩
      rw [same]
      refine ⟨?_, ?_⟩
      · change (moveRegisterEquiv middle.var).2 = regs.2
        rw [canonical]
        rfl
      · intro k
        rw [moveCfg_context]
        exact frame (.inr k)
  | inr q => cases q with
    | inl r =>
        have same : after = cfg (some (dispatchTarget r)) (reset regs) D ctx :=
          Option.some.inj (transition.2.symm.trans (dispatch_step caller r D regs ctx))
        rw [same]
        exact ⟨rfl, fun _ => rfl⟩
    | inr q =>
        let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
            PositionStatement Γ Λ R := fun _ => .halt
        let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
        have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
          rw [positionCfg_view]
          rfl
        obtain ⟨middle, localStep, _⟩ := PositionedRotationMachine.local_progress localCaller start
          ((PositionedRotationMachine.remainingSteps_pos_iff start).mpr True.intro)
        have moved := position_step_transport caller localCaller start True.intro
        rw [localStep, Option.map_some, startEq] at moved
        have same : after = positionCfg middle := Option.some.inj (transition.2.symm.trans moved)
        obtain ⟨_, canonical, frame⟩ :=
          PositionedRotationMachine.local_step_data localCaller (before := start) ⟨True.intro, localStep⟩
        rw [same]
        refine ⟨?_, ?_⟩
        · change middle.var.2 = regs.2
          rw [canonical]
          rfl
        · intro k
          rw [positionCfg_context]
          exact frame (.inr k)

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := local_step_frame caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

/-- The paid dispatch is the precise boundary between Tag-only and full reset. -/
def registersAt (start : Cfg Γ Λ R) (n : Nat) : Registers R :=
  if n = 0 then start.var else
    match start.l with
    | some (.inl q) =>
        if n ≤ MoveParserMachine.phaseSteps q (dataOfCfg start).certificate (dataOfCfg start).moveReverse
        then resetMove start.var else reset start.var
    | _ => reset start.var

theorem position_prefix_reset (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (executed : (next caller)^[n] (some (cfg (some (positionLabel q)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else reset regs := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
  have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
    rw [positionCfg_view]
    rfl
  have strictPrefix := (PositionedRotationMachine.phase_first_return localCaller q
    (positionData D) regs (positionContext D ctx)).2.2
  obtain ⟨localReached, localRun, _, _, _⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start n bound
  have actual := position_prefix_transport caller localCaller n start
    (fun j strict => strictPrefix j (by omega))
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = positionCfg localReached := Option.some.inj (executed.symm.trans actual)
  rw [same]
  exact PositionedRotationMachine.prefix_reset localCaller start localReached n bound localRun

theorem move_prefix_reset (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (executed : (next caller)^[n] (some (cfg (some (moveLabel q)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else resetMove regs := by
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  have strictPrefix := (MoveParserMachine.phase_first_return localCaller q D.certificate
    D.moveReverse D.path (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start n bound
  have actual := move_prefix_transport caller localCaller n start
    (fun j strict => strictPrefix j (by omega))
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans actual)
  have canonical := (MoveParserMachine.prefix_preserves localCaller start localReached n bound localRun).1
  rw [same]
  change moveRegisterEquiv localReached.var = _
  rw [canonical]
  change moveRegisterEquiv (if n = 0 then moveRegisterEquiv.symm regs
    else MoveParserMachine.reset (moveRegisterEquiv.symm regs)) = _
  by_cases zero : n = 0
  · simp only [zero, ite_true, Equiv.apply_symm_apply]
  · simp only [zero, ite_false, moveRegisterEquiv_reset, Equiv.apply_symm_apply]

theorem dispatch_prefix_reset (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps (dispatchPhase r) D)
    (executed : (next caller)^[n] (some (cfg (some (dispatchLabel r)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else reset regs := by
  cases n with
  | zero =>
      have same : cfg (some (dispatchLabel r)) regs D ctx = reached := Option.some.inj executed
      rw [← same]
      rfl
  | succ n =>
      rw [iterate_step caller n _ _ (dispatch_step caller r D regs ctx)] at executed
      simp only [Nat.succ_ne_zero, ite_false]
      cases r with
      | failure =>
          change n + 1 ≤ 1 at bound
          have zero : n = 0 := by omega
          subst n
          exact congrArg Turing.TM2.Cfg.var (Option.some.inj executed).symm
      | success d =>
          have small : n ≤ PositionedRotationMachine.phaseSteps (.seek d) (positionData D) := by
            change n + 1 ≤ 1 + PositionedRotationMachine.phaseSteps (.seek d) (positionData D) at bound
            omega
          simpa only [reset_reset, ite_self] using
            position_prefix_reset caller (.seek d) D (reset regs) ctx n reached small executed

theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = registersAt start n := by
  by_cases zero : n = 0
  · subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    rfl
  · by_cases owned : Owned start.l
    · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
      cases q with
      | inl q =>
          change reached.var = if n = 0 then regs else
            if n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse then resetMove regs else reset regs
          rw [ite_eq_right zero]
          by_cases early : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse
          · rw [ite_eq_left early]
            simpa only [zero, ite_false] using move_prefix_reset caller q D regs ctx n reached early executed
          · rw [ite_eq_right early]
            let m := MoveParserMachine.phaseSteps q D.certificate D.moveReverse
            have afterMove := LocalRun.iterate caller (move_phase_localRun caller q D regs ctx)
            change (next caller)^[m] (some (cfg (some (phaseLabel (.inl q))) regs D ctx)) = _ at afterMove
            have count : m + (n - m) = n := by omega
            have suffix : (next caller)^[n - m]
                (some (cfg (some (dispatchLabel (moveFinish q D).result))
                  (resetMove regs) (moveFinish q D).data ctx)) = some reached := by
              rw [← count, Nat.add_comm m, Function.iterate_add_apply, afterMove] at executed
              exact executed
            have small : n - m ≤ phaseSteps (dispatchPhase (moveFinish q D).result)
                (moveFinish q D).data := by
              change n ≤ m + phaseSteps (dispatchPhase (moveFinish q D).result)
                (moveFinish q D).data at bound
              omega
            have canonical := dispatch_prefix_reset caller (moveFinish q D).result (moveFinish q D).data
              (resetMove regs) ctx (n - m) reached small suffix
            have positive : n - m ≠ 0 := by omega
            simpa only [positive, ite_false, reset_resetMove] using canonical
      | inr q => cases q with
        | inl r =>
            simpa only [registersAt, cfg, phaseLabel, dispatchLabel, zero, ite_false] using
              dispatch_prefix_reset caller r D regs ctx n reached bound executed
        | inr q =>
            simpa only [registersAt, cfg, phaseLabel, positionLabel, zero, ite_false] using
              position_prefix_reset caller q D regs ctx n reached bound executed
    · have empty := nonowned_remaining start owned
      omega

theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, ownership⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, ownership, ?_,
    prefix_reset caller start reached n bound executed, (prefix_frame caller start reached n bound executed).2⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

omit [DecidableEq K] in
def positionControlLabel : PositionedRotationMachine.Control → Label Λ
  | .inl q => positionLabel q
  | .inr r => resultLabel (.inr r)

omit [DecidableEq K] in
theorem positionCfg_partial (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    positionCfg (PositionedRotationMachine.cfg label regs E (positionContext D ctx)) =
      cfg (label.map positionLabelEquiv) regs (setPositionData D E) ctx := by
  change positionCfg (positionView label regs (setPositionData D E) ctx) = _
  exact positionCfg_view label regs (setPositionData D E) ctx

theorem position_advance_step (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (positionLabel q)) regs D ctx) =
      some (cfg (some (positionControlLabel (PositionedRotationMachine.advance q (positionData D)).1))
        (reset regs) (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have actual := position_step_transport caller localCaller
    (positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx) True.intro
  rw [positionCfg_view] at actual
  change step caller (cfg (some (positionLabel q)) regs D ctx) = _ at actual
  simp only [positionView] at actual
  rw [PositionedRotationMachine.advance_step, Option.map_some, positionCfg_partial] at actual
  convert actual using 1
  cases (PositionedRotationMachine.advance q (positionData D)).1 <;> rfl

omit [DecidableEq K] in
theorem moveCfg_label (c : MoveCfg Γ Λ R) : (moveCfg c).l = c.l := by
  change c.l.map moveLabelEquiv = c.l
  cases c.l <;> rfl

omit [DecidableEq K] in
theorem moveCfg_source (c : MoveCfg Γ Λ R) :
    (moveCfg c).stk (.inl .source) = c.stk (.inr (.inl .source)) := by
  change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
    c.stk (moveStackEquiv (.inr (.inl .source))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

/-- Component states through its result boundary, excluding arbitrary later caller labels. -/
def MoveBoundary (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ))) : Prop :=
  MoveParserMachine.Owned label ∨ ∃ r, label = some (MoveParserMachine.resultLabel r)

theorem move_step_boundary
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (after : MoveCfg Γ Λ R)
    (executed : MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = some after) :
    MoveBoundary after.l := by
  by_cases owned : MoveParserMachine.Owned after.l
  · exact .inl owned
  · have decreased := (MoveParserMachine.local_step_data localCaller
      (before := moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) ⟨True.intro, executed⟩).1
    have zero : MoveParserMachine.remainingSteps after = 0 := by
      have notPositive : ¬ 0 < MoveParserMachine.remainingSteps after :=
        fun h => owned ((MoveParserMachine.remainingSteps_pos_iff after).mp h)
      omega
    have one : MoveParserMachine.phaseSteps q D.certificate D.moveReverse = 1 := by
      change MoveParserMachine.phaseSteps q D.certificate D.moveReverse =
        MoveParserMachine.remainingSteps after + 1 at decreased
      omega
    have complete := MoveParserMachine.phase_iterate localCaller q D.certificate
      D.moveReverse D.path regs (moveContext D ctx)
    rw [one, Function.iterate_one] at complete
    change MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = _ at complete
    rw [executed] at complete
    have same : after = MoveParserMachine.phaseResult q regs D.certificate D.moveReverse D.path
        (moveContext D ctx) := Option.some.inj complete
    have labelEq := congrArg Turing.TM2.Cfg.l (moveFinish_transport (Λ := Λ) q D regs ctx)
    rw [moveCfg_label] at labelEq
    refine .inr ⟨(moveFinish q D).result, ?_⟩
    rw [same]
    exact labelEq

def localCells (D : LocalData) : Nat := D.certificate.length + D.moveReverse.length + D.path.length +
  D.source.length + D.saved.length + D.scratch.length + D.pending.length

def phaseDebt : Phase → Nat
  | .inl q => MoveParserMachine.phaseDebt q
  | .inr (.inl (.success _)) => 2
  | .inr (.inl .failure) => 0
  | .inr (.inr q) => PositionedRotationMachine.phaseDebt q

def phaseCredit : Phase → LocalData → Nat
  | .inl _, D | .inr (.inl _), D => D.source.length
  | .inr (.inr q), D => PositionedRotationMachine.phaseCredit q (positionData D)

def debt : Option (Label Λ) → Nat
  | some (.inl q) => phaseDebt (movePhase q)
  | some (.inr (.inl r)) => phaseDebt (dispatchPhase r)
  | some (.inr (.inr (.inl q))) => phaseDebt (positionPhase q)
  | _ => 0

def credit (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseCredit (movePhase q) (dataOfCfg c)
  | some (.inr (.inl r)) => phaseCredit (dispatchPhase r) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseCredit (positionPhase q) (dataOfCfg c)
  | _ => 0


end Resources.RotationCertificate.MoveApplyMachine

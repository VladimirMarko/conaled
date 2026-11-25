import Applications.Resources.RotationCertificate.PositionedRotationMachine.Basic

/-!
# PositionedRotationMachine: Execution
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.PositionedRotationMachine
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
  LocalRun.single caller ⟨True.intro, executed⟩

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

theorem seek_step_path_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs { D with path := [] } ctx) =
      some (cfg (some (phaseLabel (.start d))) (reset regs) { D with path := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_node_left (d : RotationDirection) (raw : Word) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := nodeTag :: raw, path := .left :: p } ctx) =
      some (cfg (some (phaseLabel (.seek d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_node_right (d : RotationDirection) (raw : Word) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := nodeTag :: raw, path := .right :: p } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_source_nil (d : RotationDirection) (b : Branch) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := [], path := b :: p } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := [], path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_source_nonnode (d : RotationDirection) (b : Branch) (p : List Branch)
    (tag : Tag) (raw : Word) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := tag :: raw, path := b :: p } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := tag :: raw, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeBranch, storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem scanPrefix_step_node (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_empty_continue (d : RotationDirection) (raw : Word) (h : List Unit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := emptyTag :: raw, pending := () :: () :: h } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := emptyTag :: D.saved, pending := () :: h } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_empty_finish (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.seek d))) (reset regs)
        { D with source := raw, saved := emptyTag :: D.saved, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_foreign (d : RotationDirection) (tag : Tag) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, notEmpty, Function.update]

theorem start_left_step_node (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .left))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch .left))) (reset regs)
        { D with source := raw, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_left_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .left))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_left_step_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .left))) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem start_right_step_nodes (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs
      { D with source := nodeTag :: nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch .right))) (reset regs)
        { D with source := raw, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_first_nil (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_first_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem start_right_step_second_nil (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := [nodeTag] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [nodeTag] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_second_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .right))) regs
      { D with source := nodeTag :: tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := nodeTag :: tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem scanScratch_step_node (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { D with source := raw, scratch := nodeTag :: D.scratch, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_empty_continue (d : RotationDirection) (raw : Word) (h : List Unit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := emptyTag :: raw, pending := () :: () :: h } ctx) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { D with source := raw, scratch := emptyTag :: D.scratch, pending := () :: h } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_left_step_finish (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanScratch .left))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel .checkRight)) (reset regs)
        { D with source := raw, scratch := emptyTag :: D.scratch, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_right_step_finish (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanScratch .right))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
        { D with source := nodeTag :: raw, scratch := emptyTag :: D.scratch, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs)
        { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_foreign (d : RotationDirection) (tag : Tag) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, notEmpty, Function.update]

theorem checkRight_step_node (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .successLeft))) (reset regs)
        { D with source := raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem checkRight_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs)
        { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem checkRight_step_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem restoreScratch_step_cons (mode : RestoreMode) (tag : Tag) (rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restoreScratch mode))) regs
      { D with scratch := tag :: rest } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch mode))) (reset regs)
        { D with source := tag :: D.source, scratch := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreScratch_step_nil (mode : RestoreMode) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := [] } ctx) =
      some (cfg (some (phaseLabel (if modeResult mode = .success then
        .restorePrefix .success else .dropPending))) (reset regs)
        { D with source := markerWord mode ++ D.source, scratch := [] } ctx) := by
  cases mode <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_cons (rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .dropPending)) regs { D with pending := () :: rest } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with pending := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .dropPending)) regs { D with pending := [] } ctx) =
      some (cfg (some (phaseLabel (.restorePrefix .failure))) (reset regs)
        { D with pending := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restorePrefix_step_cons (r : Result) (tag : Tag) (rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := tag :: rest } ctx) =
      some (cfg (some (phaseLabel (.restorePrefix r))) (reset regs)
        { D with source := tag :: D.source, saved := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restorePrefix_step_nil (r : Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := [] } ctx) =
      some (cfg (some (resultLabel r)) (reset regs) { D with saved := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

@[simp] theorem emptyTag_ne_nodeTag : emptyTag ≠ nodeTag := by decide

/-- A proof-only complete local successor; it is absent from every callback. -/
def advance : Phase → LocalData → Control × LocalData
  | .seek d, D =>
      match D.path with
      | [] => (.inl (.start d), D)
      | b :: p =>
          match D.source with
          | [] => (.inl .dropPending, { D with path := p })
          | tag :: raw =>
              if tag = nodeTag then
                match b with
                | .left => (.inl (.seek d),
                    { D with source := raw, saved := nodeTag :: D.saved, path := p })
                | .right => (.inl (.scanPrefix d),
                    { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending, path := p })
              else (.inl .dropPending, { D with path := p })
  | .scanPrefix d, D =>
      match D.source with
      | [] => (.inl .dropPending, D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanPrefix d),
              { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending })
          else if tag = emptyTag then
            (.inl (if D.pending.tail = [] then .seek d else .scanPrefix d),
              { D with source := raw, saved := emptyTag :: D.saved, pending := D.pending.tail })
          else (.inl .dropPending, D)
  | .start .left, D =>
      match D.source with
      | [] => (.inl .dropPending, D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanScratch .left), { D with source := raw, pending := () :: D.pending })
          else (.inl .dropPending, D)
  | .start .right, D =>
      match D.source with
      | first :: second :: raw =>
          if first = nodeTag ∧ second = nodeTag then
            (.inl (.scanScratch .right), { D with source := raw, pending := () :: D.pending })
          else (.inl .dropPending, D)
      | _ => (.inl .dropPending, D)
  | .scanScratch d, D =>
      match D.source with
      | [] => (.inl (.restoreScratch (scratchFailure d)), D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanScratch d),
              { D with source := raw, scratch := nodeTag :: D.scratch, pending := () :: D.pending })
          else if tag = emptyTag then
            if D.pending.tail = [] then
              match d with
              | .left => (.inl .checkRight,
                  { D with source := raw, scratch := emptyTag :: D.scratch, pending := [] })
              | .right => (.inl (.restoreScratch .successRight),
                  { D with source := nodeTag :: raw, scratch := emptyTag :: D.scratch, pending := [] })
            else (.inl (.scanScratch d),
              { D with source := raw, scratch := emptyTag :: D.scratch, pending := D.pending.tail })
          else (.inl (.restoreScratch (scratchFailure d)), D)
  | .checkRight, D =>
      match D.source with
      | [] => (.inl (.restoreScratch .failureLeft), D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.restoreScratch .successLeft), { D with source := raw })
          else (.inl (.restoreScratch .failureLeft), D)
  | .restoreScratch mode, D =>
      match D.scratch with
      | [] => (.inl (if modeResult mode = .success then .restorePrefix .success else .dropPending),
          { D with source := markerWord mode ++ D.source })
      | tag :: rest => (.inl (.restoreScratch mode),
          { D with source := tag :: D.source, scratch := rest })
  | .dropPending, D =>
      match D.pending with
      | [] => (.inl (.restorePrefix .failure), D)
      | _ :: rest => (.inl .dropPending, { D with pending := rest })
  | .restorePrefix r, D =>
      match D.saved with
      | [] => (.inr r, D)
      | tag :: rest => (.inl (.restorePrefix r), { D with source := tag :: D.source, saved := rest })

def countdown : Control → LocalData → Nat
  | .inl (.seek _), D | .inl (.scanPrefix _), D | .inl (.scanScratch _), D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 5
  | .inl (.start _), D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 4
  | .inl .checkRight, D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 6
  | .inl (.restoreScratch .successLeft), D | .inl (.restoreScratch .successRight), D =>
      D.scratch.length + D.saved.length + 2
  | .inl (.restoreScratch .failureLeft), D | .inl (.restoreScratch .failureRight), D =>
      D.scratch.length + D.pending.length + D.saved.length + 3
  | .inl .dropPending, D => D.pending.length + D.saved.length + 2
  | .inl (.restorePrefix _), D => D.saved.length + 1
  | .inr _, _ => 0

theorem advance_step (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => exact seek_step_path_nil caller d ⟨raw, saved, scratch, pending, []⟩ regs ctx
      | cons b path =>
          cases raw with
          | nil => exact seek_step_source_nil caller d b path ⟨[], saved, scratch, pending, []⟩ regs ctx
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · subst tag
                cases b with
                | left => simpa [advance, controlLabel] using
                    seek_step_node_left caller d raw path ⟨[], saved, scratch, pending, []⟩ regs ctx
                | right => simpa [advance, controlLabel] using
                    seek_step_node_right caller d raw path ⟨[], saved, scratch, pending, []⟩ regs ctx
              · simpa [advance, controlLabel, node] using
                  seek_step_source_nonnode caller d b path tag raw
                    ⟨[], saved, scratch, pending, []⟩ regs ctx node
  | scanPrefix d =>
      cases raw with
      | nil => exact scanPrefix_step_nil caller d ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using
              scanPrefix_step_node caller d raw ⟨[], saved, scratch, pending, path⟩ regs ctx
          · by_cases empty : tag = emptyTag
            · subst tag
              cases pending with
              | nil => exact scanPrefix_step_empty_finish caller d raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
              | cons token pending =>
                  cases token
                  cases pending with
                  | nil => exact scanPrefix_step_empty_finish caller d raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                  | cons token pending =>
                      cases token
                      simpa [advance, controlLabel] using scanPrefix_step_empty_continue caller d raw pending
                        ⟨[], saved, scratch, [], path⟩ regs ctx
            · simpa [advance, controlLabel, node, empty] using scanPrefix_step_foreign caller d tag raw
                ⟨[], saved, scratch, pending, path⟩ regs ctx node empty
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => exact start_left_step_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · subst tag
                simpa [advance, controlLabel] using start_left_step_node caller raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx
              · simpa [advance, controlLabel, node] using start_left_step_nonnode caller tag raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx node
      | right =>
          cases raw with
          | nil => exact start_right_step_first_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
          | cons first raw =>
              by_cases firstNode : first = nodeTag
              · subst first
                cases raw with
                | nil => exact start_right_step_second_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
                | cons second raw =>
                    by_cases secondNode : second = nodeTag
                    · subst second
                      simpa [advance, controlLabel] using start_right_step_nodes caller raw
                        ⟨[], saved, scratch, pending, path⟩ regs ctx
                    · simpa [advance, controlLabel, secondNode] using
                        start_right_step_second_nonnode caller second raw
                          ⟨[], saved, scratch, pending, path⟩ regs ctx secondNode
              · have h := start_right_step_first_nonnode caller first raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx firstNode
                cases raw <;> simpa [advance, controlLabel, firstNode] using h
  | scanScratch d =>
      cases raw with
      | nil => exact scanScratch_step_nil caller d ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using scanScratch_step_node caller d raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx
          · by_cases empty : tag = emptyTag
            · subst tag
              cases pending with
              | nil => cases d with
                | left => exact scanScratch_left_step_finish caller raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
                | right => exact scanScratch_right_step_finish caller raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
              | cons token pending =>
                  cases token
                  cases pending with
                  | nil => cases d with
                    | left => exact scanScratch_left_step_finish caller raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                    | right => exact scanScratch_right_step_finish caller raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                  | cons token pending =>
                      cases token
                      simpa [advance, controlLabel] using scanScratch_step_empty_continue caller d raw pending
                        ⟨[], saved, scratch, [], path⟩ regs ctx
            · simpa [advance, controlLabel, node, empty] using scanScratch_step_foreign caller d tag raw
                ⟨[], saved, scratch, pending, path⟩ regs ctx node empty
  | checkRight =>
      cases raw with
      | nil => exact checkRight_step_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using checkRight_step_node caller raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx
          · simpa [advance, controlLabel, node] using checkRight_step_nonnode caller tag raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx node
  | restoreScratch mode =>
      cases scratch with
      | nil => exact restoreScratch_step_nil caller mode ⟨raw, saved, [], pending, path⟩ regs ctx
      | cons tag scratch => exact restoreScratch_step_cons caller mode tag scratch ⟨raw, saved, [], pending, path⟩ regs ctx
  | dropPending =>
      cases pending with
      | nil => exact dropPending_step_nil caller ⟨raw, saved, scratch, [], path⟩ regs ctx
      | cons token pending =>
          cases token
          exact dropPending_step_cons caller pending ⟨raw, saved, scratch, [], path⟩ regs ctx
  | restorePrefix r =>
      cases saved with
      | nil => exact restorePrefix_step_nil caller r ⟨raw, [], scratch, pending, path⟩ regs ctx
      | cons tag saved => exact restorePrefix_step_cons caller r tag saved ⟨raw, [], scratch, pending, path⟩ regs ctx

theorem advance_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) :=
  LocalRun.single caller ⟨True.intro, advance_step caller q D regs ctx⟩

theorem advance_countdown (q : Phase) (D : LocalData) :
    countdown (advance q D).1 (advance q D).2 + 1 ≤ countdown (.inl q) D := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => simp [advance, countdown]
      | cons b path =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> simp [advance, countdown, node] <;> omega
              · simp [advance, countdown, node]; omega
  | scanPrefix d =>
      cases raw with
      | nil => simp [advance, countdown]; omega
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, countdown, node]; omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · simp [advance, countdown, empty, finished]; omega
              · simp [advance, countdown, empty, finished, List.length_tail]; omega
            · simp [advance, countdown, node, empty]; omega
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons tag raw =>
              by_cases node : tag = nodeTag <;> simp [advance, countdown, node] <;> omega
      | right =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons first raw =>
              cases raw with
              | nil => simp [advance, countdown]; omega
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;>
                    simp [advance, countdown, nodes] <;> omega
  | scanScratch d =>
      cases raw with
      | nil => cases d <;> simp [advance, countdown, scratchFailure] <;> omega
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, countdown, node]; omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> simp [advance, countdown, empty, finished] <;> omega
              · simp [advance, countdown, empty, finished, List.length_tail]; omega
            · cases d <;> simp [advance, countdown, node, empty, scratchFailure] <;> omega
  | checkRight =>
      cases raw with
      | nil => simp [advance, countdown]; omega
      | cons tag raw =>
          by_cases node : tag = nodeTag <;> simp [advance, countdown, node] <;> omega
  | restoreScratch mode =>
      cases scratch <;> cases mode <;> simp [advance, countdown, modeResult, markerWord] <;> omega
  | dropPending => cases pending <;> simp [advance, countdown]; omega
  | restorePrefix r => cases saved <;> simp [advance, countdown]

structure Evaluation where
  result : Result
  data : LocalData
  steps : Nat
  deriving DecidableEq

/-- Total mathematical evaluation, justified by the all-state countdown. -/
def evaluate (control : Control) (D : LocalData) : Evaluation :=
  match control with
  | .inr r => ⟨r, D, 0⟩
  | .inl q =>
      let actual := advance q D
      let tail := evaluate actual.1 actual.2
      ⟨tail.result, tail.data, tail.steps + 1⟩
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

@[simp] theorem evaluate_result (r : Result) (D : LocalData) :
    evaluate (.inr r) D = ⟨r, D, 0⟩ := by rw [evaluate]

theorem evaluate_phase (q : Phase) (D : LocalData) :
    evaluate (.inl q) D =
      let tail := evaluate (advance q D).1 (advance q D).2
      ⟨tail.result, tail.data, tail.steps + 1⟩ := by rw [evaluate]

def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate (.inl q) D).steps

def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel (evaluate (.inl q) D).result)) (reset regs)
    (evaluate (.inl q) D).data ctx

theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  rw [phaseSteps, evaluate_phase]
  exact Nat.zero_lt_succ _

theorem evaluate_steps_le (control : Control) (D : LocalData) :
    (evaluate control D).steps ≤ countdown control D := by
  cases control with
  | inr r => simp [countdown]
  | inl q =>
      rw [evaluate_phase]
      have ih := evaluate_steps_le (advance q D).1 (advance q D).2
      have decreased := advance_countdown q D
      exact Nat.le_trans (Nat.add_le_add_right ih 1) decreased
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

theorem phaseSteps_le_countdown (q : Phase) (D : LocalData) :
    phaseSteps q D ≤ countdown (.inl q) D := evaluate_steps_le (.inl q) D

private theorem evaluate_reset_localRun (control : Control) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluate control D).steps
      (cfg (some (controlLabel control)) (reset regs) D ctx)
      (cfg (some (resultLabel (evaluate control D).result)) (reset regs)
        (evaluate control D).data ctx) := by
  cases control with
  | inr r =>
      simpa only [evaluate_result, controlLabel] using
        LocalRun.refl (caller := caller) (cfg (some (resultLabel r)) (reset regs) D ctx)
  | inl q =>
      simp only [evaluate_phase]
      refine LocalRun.cons ⟨True.intro, ?_⟩
        (evaluate_reset_localRun (advance q D).1 (advance q D).2 regs ctx)
      simpa only [controlLabel, reset_reset] using advance_step caller q D (reset regs) ctx
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseResult q regs D ctx) := by
  simp only [phaseSteps, phaseResult, evaluate_phase]
  exact LocalRun.cons ⟨True.intro, advance_step caller q D regs ctx⟩
    (evaluate_reset_localRun caller (advance q D).1 (advance q D).2 regs ctx)

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) :=
  LocalRun.iterate caller (phase_localRun caller q D regs ctx)

omit [DecidableEq K] in
@[simp] theorem phaseResult_reset (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult q (reset regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps q (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
theorem remainingSteps_control_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) =
      (evaluate control D).steps := by
  cases control with
  | inl q => rfl
  | inr r => simp [remainingSteps, controlLabel, resultLabel, cfg]

omit [DecidableEq K] in
@[simp] theorem remainingSteps_phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : remainingSteps (phaseResult (Λ := Λ) q regs D ctx) = 0 := rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) :
    0 < remainingSteps c ↔ Owned c.l := by
  cases label : c.l with
  | none => simp [remainingSteps, Owned, label]
  | some labelValue =>
      cases labelValue with
      | inl q => simp [remainingSteps, Owned, label, phaseSteps_pos]
      | inr external => simp [remainingSteps, Owned, label]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ q regs D ctx, c = cfg (some (phaseLabel q)) regs D ctx := by
  cases label : c.l with
  | none => simp [Owned, label] at owned
  | some labelValue =>
      cases labelValue with
      | inl q =>
          refine ⟨q, c.var, dataOfCfg c, (fun k => c.stk (.inr k)), ?_⟩
          simpa only [label, phaseLabel] using (cfg_eta c).symm
      | inr external => simp [Owned, label] at owned

omit [DecidableEq K] in
theorem phase_remaining (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) =
      remainingSteps (cfg (some (controlLabel (Λ := Λ) (advance q D).1))
        (reset regs) (advance q D).2 ctx) + 1 := by
  change phaseSteps q D = _
  rw [remainingSteps_control_cfg, phaseSteps, evaluate_phase]

theorem local_step_data {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ after.var = reset before.var ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  exact ⟨phase_remaining q D regs ctx, rfl, fun _ => rfl⟩

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := (local_step_data caller transition).1

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before ((remainingSteps_pos_iff before).mp positive)
  exact ⟨_, advance_step caller q D regs ctx, phase_remaining q D regs ctx⟩

theorem LocalRun.remaining {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    remainingSteps a = n + remainingSteps b := by
  induction run with
  | refl => simp
  | cons head tail ih =>
      have first := local_step_remaining caller head
      omega

def runSteps (d : RotationDirection) (raw : Word) (path : List Branch) : Nat :=
  phaseSteps (.seek d) { source := raw, path := path }

theorem runSteps_pos (d : RotationDirection) (raw : Word) (path : List Branch) :
    0 < runSteps d raw path := phaseSteps_pos _ _

theorem runSteps_le (d : RotationDirection) (raw : Word) (path : List Branch) :
    runSteps d raw path ≤ 3 * raw.length + path.length + 5 := by
  simpa only [runSteps, countdown, List.length_nil, Nat.add_zero] using
    phaseSteps_le_countdown (.seek d) { source := raw, path := path }

theorem runSteps_le_conservative (d : RotationDirection) (raw : Word) (path : List Branch) :
    runSteps d raw path ≤ 4 * raw.length + path.length + 12 := by
  have bound := runSteps_le d raw path
  omega

theorem restoreScratch_prefix_localRun (mode : RestoreMode) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := accepted ++ rest } ctx)
      (cfg (some (phaseLabel (.restoreScratch mode)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, scratch := rest } ctx) := by
  induction accepted generalizing D regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := rest } ctx)
  | cons tag accepted ih =>
      have first := restoreScratch_step_cons caller mode tag (accepted ++ rest) D regs ctx
      have tail := ih { D with source := tag :: D.source } (reset regs)
      simpa only [List.length_cons, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, List.cons_ne_nil, ite_false, reset_reset, ite_self,
        Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) tail

theorem restorePrefix_prefix_localRun (r : Result) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := accepted ++ rest } ctx)
      (cfg (some (phaseLabel (.restorePrefix r)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, saved := rest } ctx) := by
  induction accepted generalizing D regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := rest } ctx)
  | cons tag accepted ih =>
      have first := restorePrefix_step_cons caller r tag (accepted ++ rest) D regs ctx
      have tail := ih { D with source := tag :: D.source } (reset regs)
      simpa only [List.length_cons, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, List.cons_ne_nil, ite_false, reset_reset, ite_self,
        Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) tail

theorem dropPending_prefix_localRun (accepted rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel .dropPending)) regs { D with pending := accepted ++ rest } ctx)
      (cfg (some (phaseLabel .dropPending)) (if accepted = [] then regs else reset regs)
        { D with pending := rest } ctx) := by
  induction accepted generalizing regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel .dropPending)) regs { D with pending := rest } ctx)
  | cons token accepted ih =>
      cases token
      have first := dropPending_step_cons caller (accepted ++ rest) D regs ctx
      simpa only [List.length_cons, List.cons_append, List.cons_ne_nil, ite_false,
        reset_reset, ite_self, Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) (ih (reset regs))

theorem restoreScratch_prefix (mode : RestoreMode) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch mode)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, scratch := rest } ctx) :=
  LocalRun.iterate caller (restoreScratch_prefix_localRun caller mode accepted rest D regs ctx)

theorem restorePrefix_prefix (r : Result) (accepted rest : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel (.restorePrefix r)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, saved := rest } ctx) :=
  LocalRun.iterate caller (restorePrefix_prefix_localRun caller r accepted rest D regs ctx)

theorem dropPending_prefix (accepted rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel .dropPending)) regs { D with pending := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel .dropPending)) (if accepted = [] then regs else reset regs)
        { D with pending := rest } ctx) :=
  LocalRun.iterate caller (dropPending_prefix_localRun caller accepted rest D regs ctx)

def restorePrefixData (D : LocalData) : LocalData :=
  { D with source := D.saved.reverse ++ D.source, saved := [] }

def dropPendingData (D : LocalData) : LocalData :=
  { D with source := D.saved.reverse ++ D.source, saved := [], pending := [] }

def restoreScratchData (mode : RestoreMode) (D : LocalData) : LocalData :=
  { source := D.saved.reverse ++ markerWord mode ++ D.scratch.reverse ++ D.source,
    saved := [], scratch := [],
    pending := if modeResult mode = .success then D.pending else [], path := D.path }

def restoreScratchSteps (mode : RestoreMode) (D : LocalData) : Nat :=
  if modeResult mode = .success then D.scratch.length + D.saved.length + 2
  else D.scratch.length + D.pending.length + D.saved.length + 3

theorem restorePrefix_localRun (r : Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (D.saved.length + 1)
      (cfg (some (phaseLabel (.restorePrefix r))) regs D ctx)
      (cfg (some (resultLabel r)) (reset regs) (restorePrefixData D) ctx) := by
  let midRegs := if D.saved = [] then regs else reset regs
  have first := restorePrefix_prefix_localRun caller r D.saved [] D regs ctx
  have last := phase_step_localRun caller
    (restorePrefix_step_nil caller r (restorePrefixData D) midRegs ctx)
  have joined := LocalRun.trans caller first last
  simpa only [restorePrefixData, midRegs, List.append_nil, apply_ite,
    reset_reset, ite_self] using joined

theorem dropPending_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (D.pending.length + D.saved.length + 2)
      (cfg (some (phaseLabel .dropPending)) regs D ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (dropPendingData D) ctx) := by
  let midRegs := if D.pending = [] then regs else reset regs
  let cleared : LocalData := { D with pending := [] }
  have first := dropPending_prefix_localRun caller D.pending [] D regs ctx
  have probe := phase_step_localRun caller (dropPending_step_nil caller cleared midRegs ctx)
  have last := restorePrefix_localRun caller .failure cleared (reset midRegs) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first probe) last
  rw [show (D.pending.length + 1) + (D.saved.length + 1) =
    D.pending.length + D.saved.length + 2 by omega] at joined
  simpa [midRegs, cleared, restorePrefixData, dropPendingData, apply_ite, reset_reset] using joined

theorem restoreScratch_localRun (mode : RestoreMode) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (restoreScratchSteps mode D)
      (cfg (some (phaseLabel (.restoreScratch mode))) regs D ctx)
      (cfg (some (resultLabel (modeResult mode))) (reset regs) (restoreScratchData mode D) ctx) := by
  let midRegs := if D.scratch = [] then regs else reset regs
  let moved : LocalData := { D with source := D.scratch.reverse ++ D.source, scratch := [] }
  let marked : LocalData := { moved with source := markerWord mode ++ moved.source }
  have first := restoreScratch_prefix_localRun caller mode D.scratch [] D regs ctx
  have probe := phase_step_localRun caller (restoreScratch_step_nil caller mode moved midRegs ctx)
  by_cases success : modeResult mode = .success
  · have probe' : LocalRun caller 1
        (cfg (some (phaseLabel (.restoreScratch mode))) midRegs moved ctx)
        (cfg (some (phaseLabel (.restorePrefix .success))) (reset midRegs) marked ctx) := by
      simpa only [success, ite_true, moved, marked] using probe
    have last := restorePrefix_localRun caller .success marked (reset midRegs) ctx
    have joined := LocalRun.trans caller (LocalRun.trans caller first probe') last
    rw [show (D.scratch.length + 1) + (D.saved.length + 1) =
      D.scratch.length + D.saved.length + 2 by omega] at joined
    simpa [restoreScratchSteps, restoreScratchData, restorePrefixData, success,
      moved, marked, midRegs, List.append_assoc, apply_ite, reset_reset] using joined
  · have failure : modeResult mode = .failure := by
      cases mode <;> simp_all [modeResult]
    have probe' : LocalRun caller 1
        (cfg (some (phaseLabel (.restoreScratch mode))) midRegs moved ctx)
        (cfg (some (phaseLabel .dropPending)) (reset midRegs) marked ctx) := by
      simpa only [success, ite_false, moved, marked] using probe
    have last := dropPending_localRun caller marked (reset midRegs) ctx
    have joined := LocalRun.trans caller (LocalRun.trans caller first probe') last
    rw [show (D.scratch.length + 1) + (D.pending.length + D.saved.length + 2) =
      D.scratch.length + D.pending.length + D.saved.length + 3 by omega] at joined
    simpa [restoreScratchSteps, restoreScratchData, dropPendingData, success, failure,
      moved, marked, midRegs, List.append_assoc, apply_ite, reset_reset] using joined

theorem restorePrefix_iterate (r : Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[D.saved.length + 1]
      (some (cfg (some (phaseLabel (.restorePrefix r))) regs D ctx)) =
      some (cfg (some (resultLabel r)) (reset regs) (restorePrefixData D) ctx) :=
  LocalRun.iterate caller (restorePrefix_localRun caller r D regs ctx)

theorem dropPending_iterate (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[D.pending.length + D.saved.length + 2]
      (some (cfg (some (phaseLabel .dropPending)) regs D ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) (dropPendingData D) ctx) :=
  LocalRun.iterate caller (dropPending_localRun caller D regs ctx)

theorem restoreScratch_iterate (mode : RestoreMode) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[restoreScratchSteps mode D]
      (some (cfg (some (phaseLabel (.restoreScratch mode))) regs D ctx)) =
      some (cfg (some (resultLabel (modeResult mode))) (reset regs) (restoreScratchData mode D) ctx) :=
  LocalRun.iterate caller (restoreScratch_localRun caller mode D regs ctx)


end Resources.RotationCertificate.PositionedRotationMachine

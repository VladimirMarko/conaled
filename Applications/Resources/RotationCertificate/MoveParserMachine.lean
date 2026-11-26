import Applications.Resources.RotationCertificate.LinearParser
import Applications.Resources.BinaryCounter.FixedWidthMachine

/-!
# An open finite move-prefix parser

The finite blocks consume actual Tags into a Branch reverse stack, emit the
forward path on success, and physically restore the complete input on failure.
Source moves, paths, exact counts and delimiter debt occur only in proofs.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.MoveParserMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)

instance branchFintype : Fintype Branch where
  elems := {.left, .right}
  complete b := by cases b <;> decide

instance directionFintype : Fintype RotationDirection where
  elems := {.left, .right}
  complete d := by cases d <;> decide

inductive LocalStack | raw | reverse | path
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.raw, .reverse, .path}
  complete k := by cases k <;> decide

inductive Phase
  | start | scan (direction : RotationDirection)
  | emit (direction : RotationDirection) | undo (direction : RotationDirection)
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.start, .scan .left, .scan .right, .emit .left, .emit .right,
    .undo .left, .undo .right}
  complete phase := by cases phase with
    | start => decide
    | scan d => cases d <;> decide
    | emit d => cases d <;> decide
    | undo d => cases d <;> decide

inductive Result | success (direction : RotationDirection) | failure
  deriving DecidableEq

instance : Fintype Result where
  elems := {.success .left, .success .right, .failure}
  complete result := by cases result with
    | success d => cases d <;> decide
    | failure => decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Registers (R : Type) := Option Tag × R

variable {K Λ R : Type} {Γ : K → Type}

abbrev Alphabet (Γ : K → Type) : StackId K → Type
  | .inl .raw => Tag
  | .inl .reverse | .inl .path => Branch
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (Alphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (Alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (Alphabet Γ) (Label Λ) (Registers R)

def phaseLabel (phase : Phase) : Label Λ := .inl phase
def resultLabel (result : Result) : Label Λ := .inr (.inl result)
def callerLabel (label : Λ) : Label Λ := .inr (.inr label)

def reset (regs : Registers R) : Registers R := (none, regs.2)
def storeTag (regs : Registers R) (tag : Option Tag) : Registers R := (tag, regs.2)
def storeBranch (regs : Registers R) (branch : Option Branch) : Registers R :=
  (branch.map branchTag, regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl

/-- The total fallback is used only after a real Branch pop in the emit block. -/
def inverseBranch (tag : Tag) : Branch := if tag = pathRightTag then .right else .left

@[simp] theorem inverseBranch_branchTag (b : Branch) : inverseBranch (branchTag b) = b := by
  cases b <;> rfl

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- No callback reads a list, source parser, path, count or rank. -/
def block : Phase → Statement Γ Λ R
  | .start =>
      .pop (.inl .raw) storeTag (.branch (fun regs => regs.1.isSome)
        (.branch (fun regs => decide (regs.1 = some rotateLeftTag))
          (jump (phaseLabel (.scan .left)))
          (.branch (fun regs => decide (regs.1 = some rotateRightTag))
            (jump (phaseLabel (.scan .right)))
            (.push (.inl .raw) (fun regs => regs.1.getD 0) (jump (resultLabel .failure)))))
        (jump (resultLabel .failure)))
  | .scan d =>
      .pop (.inl .raw) storeTag (.branch (fun regs => regs.1.isSome)
        (.branch (fun regs => decide (regs.1 = some pathLeftTag))
          (.push (.inl .reverse) (fun _ => .left) (jump (phaseLabel (.scan d))))
          (.branch (fun regs => decide (regs.1 = some pathRightTag))
            (.push (.inl .reverse) (fun _ => .right) (jump (phaseLabel (.scan d))))
            (.branch (fun regs => decide (regs.1 = some endMoveTag))
              (jump (phaseLabel (.emit d)))
              (.push (.inl .raw) (fun regs => regs.1.getD 0) (jump (phaseLabel (.undo d)))))))
        (jump (phaseLabel (.undo d))))
  | .emit d =>
      .pop (.inl .reverse) storeBranch (.branch (fun regs => regs.1.isSome)
        (.push (.inl .path) (fun regs => inverseBranch (regs.1.getD pathLeftTag))
          (jump (phaseLabel (.emit d))))
        (jump (resultLabel (.success d))))
  | .undo d =>
      .pop (.inl .reverse) storeBranch (.branch (fun regs => regs.1.isSome)
        (.push (.inl .raw) (fun regs => regs.1.getD pathLeftTag) (jump (phaseLabel (.undo d))))
        (.push (.inl .raw) (fun _ => directionTag d) (jump (resultLabel .failure))))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl phase => block phase
  | .inr external => caller external

theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase) :
    ambient = program (fun external => ambient (.inr external)) := by
  funext label
  cases label with
  | inl phase => exact agrees phase
  | inr external => rfl

def cfg (label : Option (Label Λ)) (regs : Registers R) (raw : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .raw => raw
    | .inl .reverse => rev
    | .inl .path => out
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk (.inl .raw) = right.stk (.inl .raw))
    (rev : left.stk (.inl .reverse) = right.stk (.inl .reverse))
    (out : left.stk (.inl .path) = right.stk (.inl .path))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stores : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | raw => exact raw
      | reverse => exact rev
      | path => exact out
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stores
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .raw)) (c.stk (.inl .reverse))
      (c.stk (.inl .path)) (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

/-- Number of consecutive actual branch Tags, used only in proof-side contracts. -/
def branchCount : Word → Nat
  | [] => 0
  | tag :: raw => if tag = pathLeftTag ∨ tag = pathRightTag then branchCount raw + 1 else 0

@[simp] theorem branchCount_nil : branchCount [] = 0 := rfl
@[simp] theorem branchCount_branch (b : Branch) (raw : Word) :
    branchCount (branchTag b :: raw) = branchCount raw + 1 := by cases b <;> rfl
@[simp] theorem branchCount_end (raw : Word) : branchCount (endMoveTag :: raw) = 0 := rfl

theorem branchCount_foreign (tag : Tag) (raw : Word)
    (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    branchCount (tag :: raw) = 0 := by simp [branchCount, left, right]

theorem branchCount_le (raw : Word) : branchCount raw ≤ raw.length := by
  induction raw with
  | nil => exact Nat.le_refl _
  | cons tag raw ih => simp only [branchCount, List.length_cons]; split <;> omega

theorem branchCount_prefix (accepted : List Branch) (raw : Word) :
    branchCount (pathTags accepted ++ raw) = accepted.length + branchCount raw := by
  induction accepted with
  | nil => simp only [pathTags, List.map_nil, List.nil_append, List.length_nil, Nat.zero_add]
  | cons b accepted ih =>
      change branchCount (branchTag b :: (pathTags accepted ++ raw)) = _
      rw [branchCount_branch, ih]
      simp only [List.length_cons]
      omega

theorem branchCount_code (path : List Branch) (rest : Word) :
    branchCount (pathTags path ++ [endMoveTag] ++ rest) = path.length := by
  rw [List.append_assoc, branchCount_prefix]
  rfl

/-- The source failure tariff follows its recursive-none branches, not a time bound. -/
theorem parsePathRun_failure_cost (raw : Word) (failure : (parsePathRun raw).1 = none) :
    (parsePathRun raw).2 = 2 * branchCount raw + 2 := by
  induction raw with
  | nil => rfl
  | cons tag raw ih =>
      have branchCase (b : Branch) (failed : (parsePathRun (branchTag b :: raw)).1 = none) :
          (parsePathRun (branchTag b :: raw)).2 = 2 * branchCount (branchTag b :: raw) + 2 := by
        cases child : (parsePathRun raw).1 with
        | none =>
            have cost := ih child
            rw [parsePathRun_branch, branchCount_branch]
            simp only [Resources.bind, child]
            omega
        | some pair =>
            rcases pair with ⟨path, rest⟩
            rw [parsePathRun_branch] at failed
            simp only [Resources.bind, child] at failed
            cases failed
      by_cases ended : tag = endMoveTag
      · subst tag
        rw [parsePathRun_end] at failure
        cases failure
      · by_cases left : tag = pathLeftTag
        · subst tag
          exact branchCase .left failure
        · by_cases right : tag = pathRightTag
          · subst tag
            exact branchCase .right failure
          · rw [parsePathRun_foreign tag raw ended left right, branchCount_foreign tag raw left right]

def scanSteps (raw : Word) (rev : List Branch) : Nat := 2 * branchCount raw + rev.length + 2

def startSteps : Word → List Branch → Nat
  | [], _ => 1
  | tag :: raw, rev =>
      if tag = rotateLeftTag ∨ tag = rotateRightTag then 2 * branchCount raw + rev.length + 3 else 1

def fullSteps (raw : Word) : Nat := startSteps raw []

@[simp] theorem startSteps_direction (d : RotationDirection) (raw : Word) (rev : List Branch) :
    startSteps (directionTag d :: raw) rev = scanSteps raw rev + 1 := by
  cases d <;> rfl

theorem startSteps_foreign (tag : Tag) (raw : Word) (rev : List Branch)
    (left : tag ≠ rotateLeftTag) (right : tag ≠ rotateRightTag) :
    startSteps (tag :: raw) rev = 1 := by simp [startSteps, left, right]

@[simp] theorem fullSteps_nil : fullSteps [] = 1 := rfl
@[simp] theorem fullSteps_direction (d : RotationDirection) (raw : Word) :
    fullSteps (directionTag d :: raw) = 2 * branchCount raw + 3 := by
  rw [fullSteps, startSteps_direction]
  simp [scanSteps]

theorem fullSteps_foreign (tag : Tag) (raw : Word)
    (left : tag ≠ rotateLeftTag) (right : tag ≠ rotateRightTag) :
    fullSteps (tag :: raw) = 1 := startSteps_foreign tag raw [] left right

theorem scanSteps_pos (raw : Word) (rev : List Branch) : 0 < scanSteps raw rev := by
  unfold scanSteps
  omega

theorem startSteps_pos (raw : Word) (rev : List Branch) : 0 < startSteps raw rev := by
  cases raw with
  | nil => exact Nat.zero_lt_one
  | cons tag raw =>
      by_cases direction : tag = rotateLeftTag ∨ tag = rotateRightTag
      · simpa only [startSteps, ite_eq_left direction] using
          Nat.succ_pos (2 * branchCount raw + rev.length + 2)
      · simpa only [startSteps, ite_eq_right direction] using Nat.zero_lt_one

theorem fullSteps_pos (raw : Word) : 0 < fullSteps raw := startSteps_pos raw []

theorem fullSteps_le (raw : Word) : fullSteps raw ≤ 2 * raw.length + 1 := by
  cases raw with
  | nil => decide
  | cons tag raw =>
      have bound := branchCount_le raw
      simp only [fullSteps, startSteps, List.length_nil, List.length_cons]
      split <;> omega

theorem fullSteps_code (move : RotationMove) (rest : Word) :
    fullSteps (moveCode move ++ rest) = 2 * move.position.length + 3 := by
  change fullSteps (directionTag move.direction :: (pathTags move.position ++ [endMoveTag] ++ rest)) = _
  rw [fullSteps_direction, branchCount_code]

theorem parseMoveRun_direction_failure_cost (d : RotationDirection) (raw : Word)
    (failed : (parsePathRun raw).1 = none) :
    (parseMoveRun (directionTag d :: raw)).2 = 2 * branchCount raw + 4 := by
  have cost := parsePathRun_failure_cost raw failed
  rw [parseMoveRun_direction]
  simp only [Resources.bind, failed]
  omega

theorem parseMoveRun_failure_cost (raw : Word) (failed : (parseMoveRun raw).1 = none) :
    (parseMoveRun raw).2 = fullSteps raw + 1 := by
  cases raw with
  | nil => rfl
  | cons tag raw =>
      have directionCase (d : RotationDirection)
          (failure : (parseMoveRun (directionTag d :: raw)).1 = none) :
          (parseMoveRun (directionTag d :: raw)).2 = fullSteps (directionTag d :: raw) + 1 := by
        cases child : (parsePathRun raw).1 with
        | none =>
            simpa only [fullSteps_direction] using parseMoveRun_direction_failure_cost d raw child
        | some pair =>
            rcases pair with ⟨path, rest⟩
            rw [parseMoveRun_direction] at failure
            simp only [Resources.bind, child] at failure
            cases failure
      by_cases left : tag = rotateLeftTag
      · subst tag
        exact directionCase .left failed
      · by_cases right : tag = rotateRightTag
        · subst tag
          exact directionCase .right failed
        · rw [parseMoveRun_foreign tag raw left right, fullSteps_foreign tag raw left right]

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)
def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

@[simp] theorem next_none (caller : External Λ → Statement Γ Λ R) : next caller none = none := rfl
@[simp] theorem next_some (caller : External Λ → Statement Γ Λ R) (c : Cfg Γ Λ R) :
    next caller (some c) = step caller c := rfl

variable (caller : External Λ → Statement Γ Λ R)

theorem start_step_nil (rev out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .start)) regs [] rev out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] rev out ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_step_direction (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .start)) regs (directionTag d :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.scan d))) (reset regs) raw rev out ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_step_foreign (tag : Tag) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (left : tag ≠ rotateLeftTag) (right : tag ≠ rotateRightTag) :
    step caller (cfg (some (phaseLabel .start)) regs (tag :: raw) rev out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) (tag :: raw) rev out ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel, resultLabel,
    storeTag, jump, reset, left, right, Function.update]

theorem scan_step_nil (d : RotationDirection) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scan d))) regs [] rev out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) [] rev out ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_branch (d : RotationDirection) (b : Branch) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (branchTag b :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.scan d))) (reset regs) raw (b :: rev) out ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_end (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (endMoveTag :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.emit d))) (reset regs) raw rev out ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_foreign (d : RotationDirection) (tag : Tag) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (ended : tag ≠ endMoveTag) (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (tag :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) (tag :: raw) rev out ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, reset, ended, left, right, Function.update]

theorem emit_step_cons (d : RotationDirection) (b : Branch) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.emit d))) regs raw (b :: rev) out ctx) =
      some (cfg (some (phaseLabel (.emit d))) (reset regs) raw rev (b :: out) ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emit_step_nil (d : RotationDirection) (raw : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.emit d))) regs raw [] out ctx) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] out ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem undo_step_cons (d : RotationDirection) (b : Branch) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.undo d))) regs raw (b :: rev) out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) (branchTag b :: raw) rev out ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem undo_step_nil (d : RotationDirection) (raw : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.undo d))) regs raw [] out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) (directionTag d :: raw) [] out ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem iterate_step (n : Nat) (before after : Cfg Γ Λ R)
    (first : step caller before = some after) :
    (next caller)^[n + 1] (some before) = (next caller)^[n] (some after) := by
  rw [Function.iterate_succ_apply, next_some, first]

theorem emit_iterate (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1] (some (cfg (some (phaseLabel (.emit d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] (rev.reverse ++ out) ctx) := by
  induction rev generalizing out regs with
  | nil => simpa using emit_step_nil caller d raw out regs ctx
  | cons b rev ih =>
      rw [show (b :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (emit_step_cons caller d b raw rev out regs ctx), ih, reset_reset]
      simp [List.reverse_cons, List.append_assoc]

theorem undo_iterate (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1] (some (cfg (some (phaseLabel (.undo d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags rev.reverse ++ raw)) [] out ctx) := by
  induction rev generalizing raw regs with
  | nil => simpa [pathTags] using undo_step_nil caller d raw out regs ctx
  | cons b rev ih =>
      rw [show (b :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (undo_step_cons caller d b raw rev out regs ctx), ih, reset_reset]
      simp [pathTags, List.reverse_cons, List.map_append, List.append_assoc]

theorem emit_prefix_append (d : RotationDirection) (raw : Word) (accepted rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel (.emit d))) regs raw (accepted ++ rev) out ctx)) =
      some (cfg (some (phaseLabel (.emit d))) (if accepted = [] then regs else reset regs)
        raw rev (accepted.reverse ++ out) ctx) := by
  induction accepted generalizing out regs with
  | nil => rfl
  | cons b accepted ih =>
      simp only [List.length_cons, List.cons_append]
      rw [iterate_step caller _ _ _ (emit_step_cons caller d b raw (accepted ++ rev) out regs ctx), ih]
      by_cases empty : accepted = [] <;> simp [empty, reset_reset, List.reverse_cons, List.append_assoc]

theorem undo_prefix_append (d : RotationDirection) (raw : Word) (accepted rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel (.undo d))) regs raw (accepted ++ rev) out ctx)) =
      some (cfg (some (phaseLabel (.undo d))) (if accepted = [] then regs else reset regs)
        (pathTags accepted.reverse ++ raw) rev out ctx) := by
  induction accepted generalizing raw regs with
  | nil => rfl
  | cons b accepted ih =>
      simp only [List.length_cons, List.cons_append]
      rw [iterate_step caller _ _ _ (undo_step_cons caller d b raw (accepted ++ rev) out regs ctx), ih]
      by_cases empty : accepted = [] <;>
        simp [empty, reset_reset, pathTags, List.reverse_cons, List.map_append, List.append_assoc]

private theorem take_nil_iff (rev : List Branch) (j : Nat) (bound : j ≤ rev.length) :
    rev.take j = [] ↔ j = 0 := by
  constructor
  · intro empty
    have length := congrArg List.length empty
    simpa only [List.length_take, Nat.min_eq_left bound, List.length_nil] using length
  · rintro rfl
    rfl

theorem emit_prefix (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ rev.length) :
    (next caller)^[j] (some (cfg (some (phaseLabel (.emit d))) regs raw rev out ctx)) =
      some (cfg (some (phaseLabel (.emit d))) (if j = 0 then regs else reset regs)
        raw (rev.drop j) ((rev.take j).reverse ++ out) ctx) := by
  have run := emit_prefix_append caller d raw (rev.take j) (rev.drop j) out regs ctx
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left bound,
    take_nil_iff rev j bound] using run

theorem undo_prefix (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ rev.length) :
    (next caller)^[j] (some (cfg (some (phaseLabel (.undo d))) regs raw rev out ctx)) =
      some (cfg (some (phaseLabel (.undo d))) (if j = 0 then regs else reset regs)
        (pathTags (rev.take j).reverse ++ raw) (rev.drop j) out ctx) := by
  have run := undo_prefix_append caller d raw (rev.take j) (rev.drop j) out regs ctx
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left bound,
    take_nil_iff rev j bound] using run

theorem scan_prefix (d : RotationDirection) (accepted : List Branch) (raw : Word)
    (rev out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel (.scan d))) regs (pathTags accepted ++ raw) rev out ctx)) =
      some (cfg (some (phaseLabel (.scan d))) (if accepted = [] then regs else reset regs)
        raw (accepted.reverse ++ rev) out ctx) := by
  induction accepted generalizing rev regs with
  | nil => rfl
  | cons b accepted ih =>
      change (next caller)^[accepted.length + 1]
        (some (cfg (some (phaseLabel (.scan d))) regs
          (branchTag b :: (pathTags accepted ++ raw)) rev out ctx)) = _
      rw [iterate_step caller _ _ _ (scan_step_branch caller d b (pathTags accepted ++ raw) rev out regs ctx), ih]
      by_cases empty : accepted = [] <;> simp [empty, reset_reset, List.reverse_cons, List.append_assoc]

omit [DecidableEq K] in
def scanResult (d : RotationDirection) (regs : Registers R) (original : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) : Option (List Branch × Word) → Cfg Γ Λ R
  | none => cfg (some (resultLabel .failure)) (reset regs)
      (directionTag d :: (pathTags rev.reverse ++ original)) [] out ctx
  | some (path, rest) => cfg (some (resultLabel (.success d))) (reset regs)
      rest [] (rev.reverse ++ path ++ out) ctx

theorem scan_iterate (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[scanSteps raw rev]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (scanResult d regs raw rev out ctx (parsePathRun raw).1) := by
  induction raw generalizing rev regs with
  | nil =>
      rw [show scanSteps [] rev = (rev.length + 1) + 1 by simp [scanSteps],
        iterate_step caller _ _ _ (scan_step_nil caller d rev out regs ctx), undo_iterate]
      simp [scanResult, reset_reset]
  | cons tag raw ih =>
      have branchCase (b : Branch) :
          (next caller)^[scanSteps (branchTag b :: raw) rev]
              (some (cfg (some (phaseLabel (.scan d))) regs (branchTag b :: raw) rev out ctx)) =
            some (scanResult d regs (branchTag b :: raw) rev out ctx
              (parsePathRun (branchTag b :: raw)).1) := by
        rw [show scanSteps (branchTag b :: raw) rev = scanSteps raw (b :: rev) + 1 by
              simp [scanSteps]; omega,
          iterate_step caller _ _ _ (scan_step_branch caller d b raw rev out regs ctx), ih]
        cases parsed : (parsePathRun raw).1 with
        | none =>
            simp [scanResult, parsePathRun_branch, Resources.bind, parsed, reset_reset,
              pathTags, List.reverse_cons, List.map_append, List.append_assoc]
        | some pair =>
            rcases pair with ⟨path, rest⟩
            simp [scanResult, parsePathRun_branch, Resources.bind, parsed, reset_reset,
              List.reverse_cons, List.append_assoc]
      by_cases left : tag = pathLeftTag
      · subst tag
        exact branchCase .left
      · by_cases right : tag = pathRightTag
        · subst tag
          exact branchCase .right
        · by_cases ended : tag = endMoveTag
          · subst tag
            rw [show scanSteps (endMoveTag :: raw) rev = (rev.length + 1) + 1 by
                  simp [scanSteps],
              iterate_step caller _ _ _ (scan_step_end caller d raw rev out regs ctx), emit_iterate]
            simp [scanResult, reset_reset]
          · rw [show scanSteps (tag :: raw) rev = (rev.length + 1) + 1 by
                  rw [scanSteps, branchCount_foreign tag raw left right]; omega,
              iterate_step caller _ _ _ (scan_step_foreign caller d tag raw rev out regs ctx ended left right),
              undo_iterate]
            simp [scanResult, parsePathRun_foreign tag raw ended left right, reset_reset]

theorem scan_of_some (d : RotationDirection) (raw : Word) (path : List Branch) (rest : Word)
    (rev out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    (next caller)^[2 * path.length + rev.length + 2]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs)
        rest [] (rev.reverse ++ path ++ out) ctx) := by
  have count : scanSteps raw rev = 2 * path.length + rev.length + 2 := by
    rw [(parsePathRun_iff raw path rest).mp returned, scanSteps, branchCount_code]
  simpa only [count, returned, scanResult] using scan_iterate caller d raw rev out regs ctx

theorem scan_of_none (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (failed : (parsePathRun raw).1 = none) :
    (next caller)^[scanSteps raw rev]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags rev.reverse ++ raw)) [] out ctx) := by
  simpa only [failed, scanResult] using scan_iterate caller d raw rev out regs ctx

omit [DecidableEq K] in
def entry (regs : Registers R) (raw : Word) (out : List Branch) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel .start)) regs raw [] out ctx

omit [DecidableEq K] in
def resultCfg (regs : Registers R) (original : Word) (out : List Branch)
    (ctx : ∀ k, List (Γ k)) : Option (RotationMove × Word) → Cfg Γ Λ R
  | none => cfg (some (resultLabel .failure)) (reset regs) original [] out ctx
  | some (move, rest) => cfg (some (resultLabel (.success move.direction))) (reset regs)
      rest [] (move.position ++ out) ctx

theorem run_source (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
      some (resultCfg regs raw out ctx (parseMoveRun raw).1) := by
  cases raw with
  | nil => simpa [entry, resultCfg] using start_step_nil caller [] out regs ctx
  | cons tag raw =>
      have directionCase (d : RotationDirection) :
          (next caller)^[fullSteps (directionTag d :: raw)]
              (some (entry regs (directionTag d :: raw) out ctx)) =
            some (resultCfg regs (directionTag d :: raw) out ctx
              (parseMoveRun (directionTag d :: raw)).1) := by
        rw [fullSteps, startSteps_direction]
        unfold entry
        rw [iterate_step caller _ _ _ (start_step_direction caller d raw [] out regs ctx), scan_iterate]
        cases parsed : (parsePathRun raw).1 with
        | none => simp [scanResult, resultCfg, parseMoveRun_direction, Resources.bind, parsed, reset_reset, pathTags]
        | some pair =>
            rcases pair with ⟨path, rest⟩
            simp [scanResult, resultCfg, parseMoveRun_direction, Resources.bind, parsed, reset_reset]
      by_cases left : tag = rotateLeftTag
      · subst tag
        exact directionCase .left
      · by_cases right : tag = rotateRightTag
        · subst tag
          exact directionCase .right
        · simpa [entry, fullSteps_foreign tag raw left right, resultCfg,
            parseMoveRun_foreign tag raw left right] using
            start_step_foreign caller tag raw [] out regs ctx left right

theorem run_of_some (raw : Word) (move : RotationMove) (rest : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
      some (cfg (some (resultLabel (.success move.direction))) (reset regs)
        rest [] (move.position ++ out) ctx) := by
  simpa only [returned, resultCfg] using run_source caller raw out regs ctx

theorem run_of_none (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun raw).1 = none) :
    (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx) := by
  simpa only [failed, resultCfg] using run_source caller raw out regs ctx

theorem run_code (move : RotationMove) (rest : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * move.position.length + 3] (some (entry regs (moveCode move ++ rest) out ctx)) =
      some (cfg (some (resultLabel (.success move.direction))) (reset regs)
        rest [] (move.position ++ out) ctx) := by
  simpa only [fullSteps_code, parseMoveRun_code, resultCfg] using
    run_source caller (moveCode move ++ rest) out regs ctx

theorem run_emit (move : RotationMove) (rest : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * move.position.length + 3] (some (entry regs (emitMoveRun move rest).1 out ctx)) =
      some (cfg (some (resultLabel (.success move.direction))) (reset regs)
        rest [] (move.position ++ out) ctx) := by
  rw [emitMoveRun_value]
  exact run_code caller move rest out regs ctx

def runInTime (raw : Word) (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw out ctx)
      (some (resultCfg regs raw out ctx (parseMoveRun raw).1)) (fullSteps raw) where
  steps := fullSteps raw
  evals_in_steps := run_source caller raw out regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (raw : Word) (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw out ctx)
      (some (resultCfg regs raw out ctx (parseMoveRun raw).1)) (2 * raw.length + 1) where
  steps := fullSteps raw
  evals_in_steps := run_source caller raw out regs ctx
  steps_le_m := fullSteps_le raw

def phaseSteps : Phase → Word → List Branch → Nat
  | .start, raw, rev => startSteps raw rev
  | .scan _, raw, rev => scanSteps raw rev
  | .emit _, _, rev | .undo _, _, rev => rev.length + 1

def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl phase) => phaseSteps phase (c.stk (.inl .raw)) (c.stk (.inl .reverse))
  | _ => 0

def phaseDebt : Phase → Nat
  | .start => 0
  | .scan _ | .undo _ => 1
  | .emit _ => 2

def debt : Option (Label Λ) → Nat
  | some (.inl phase) => phaseDebt phase
  | some (.inr (.inl (.success _))) => 2
  | _ => 0

def ownedCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk (.inl .raw)).length + (c.stk (.inl .reverse)).length + (c.stk (.inl .path)).length

/-- Physical cells plus the actual label's consumed direction/delimiter debt. -/
def potential (c : Cfg Γ Λ R) : Nat := ownedCells c + debt c.l

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases control : c.l with
  | none => simp [remainingSteps, Owned, control]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, control]
    | inl phase =>
        cases phase with
        | start =>
            simp only [remainingSteps, control, phaseSteps, Owned, iff_true]
            exact startSteps_pos _ _
        | scan d =>
            simp only [remainingSteps, control, phaseSteps, Owned, iff_true]
            exact scanSteps_pos _ _
        | emit d => simp [remainingSteps, control, phaseSteps, Owned]
        | undo d => simp [remainingSteps, control, phaseSteps, Owned]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ phase regs raw rev out ctx, c = cfg (some (phaseLabel phase)) regs raw rev out ctx := by
  cases control : c.l with
  | none => simp [Owned, control] at owned
  | some label => cases label with
    | inr external => simp [Owned, control] at owned
    | inl phase =>
        refine ⟨phase, c.var, c.stk (.inl .raw), c.stk (.inl .reverse),
          c.stk (.inl .path), (fun k => c.stk (.inr k)), ?_⟩
        simpa only [control, phaseLabel] using (cfg_eta c).symm

/-- Every dirty owned state has actual progress, exact rank and exact physical potential. -/
theorem phase_step_data (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ after, step caller (cfg (some (phaseLabel phase)) regs raw rev out ctx) = some after ∧
      phaseSteps phase raw rev = remainingSteps after + 1 ∧ after.var = reset regs ∧
      (∀ k, after.stk (.inr k) = ctx k) ∧
      potential after = potential (cfg (Λ := Λ) (some (phaseLabel phase)) regs raw rev out ctx) := by
  cases phase with
  | start =>
      cases raw with
      | nil =>
          refine ⟨_, start_step_nil caller rev out regs ctx, rfl, rfl, fun _ => rfl, ?_⟩
          rfl
      | cons tag raw =>
          by_cases left : tag = rotateLeftTag
          · subst tag
            refine ⟨_, start_step_direction caller .left raw rev out regs ctx, ?_, rfl, fun _ => rfl, ?_⟩
            · change startSteps (directionTag .left :: raw) rev = scanSteps raw rev + 1
              exact startSteps_direction .left raw rev
            · simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
          · by_cases right : tag = rotateRightTag
            · subst tag
              refine ⟨_, start_step_direction caller .right raw rev out regs ctx, ?_, rfl, fun _ => rfl, ?_⟩
              · change startSteps (directionTag .right :: raw) rev = scanSteps raw rev + 1
                exact startSteps_direction .right raw rev
              · simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
            · refine ⟨_, start_step_foreign caller tag raw rev out regs ctx left right,
                ?_, rfl, fun _ => rfl, ?_⟩
              · simp [phaseSteps, startSteps, remainingSteps, cfg, resultLabel, left, right]
              · rfl
  | scan d =>
      cases raw with
      | nil =>
          refine ⟨_, scan_step_nil caller d rev out regs ctx, ?_, rfl, fun _ => rfl, rfl⟩
          change scanSteps [] rev = rev.length + 1 + 1
          simp [scanSteps]
      | cons tag raw =>
          by_cases left : tag = pathLeftTag
          · subst tag
            refine ⟨_, scan_step_branch caller d .left raw rev out regs ctx, ?_, rfl, fun _ => rfl, ?_⟩
            · change scanSteps (branchTag .left :: raw) rev = scanSteps raw (.left :: rev) + 1
              simp [scanSteps]; omega
            · simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
          · by_cases right : tag = pathRightTag
            · subst tag
              refine ⟨_, scan_step_branch caller d .right raw rev out regs ctx, ?_, rfl, fun _ => rfl, ?_⟩
              · change scanSteps (branchTag .right :: raw) rev = scanSteps raw (.right :: rev) + 1
                simp [scanSteps]; omega
              · simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
            · by_cases ended : tag = endMoveTag
              · subst tag
                refine ⟨_, scan_step_end caller d raw rev out regs ctx, ?_, rfl, fun _ => rfl, ?_⟩
                · change scanSteps (endMoveTag :: raw) rev = rev.length + 1 + 1
                  simp [scanSteps]
                · simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
              · refine ⟨_, scan_step_foreign caller d tag raw rev out regs ctx ended left right,
                  ?_, rfl, fun _ => rfl, rfl⟩
                change scanSteps (tag :: raw) rev = rev.length + 1 + 1
                simp [scanSteps, branchCount_foreign tag raw left right]
  | emit d =>
      cases rev with
      | nil =>
          refine ⟨_, emit_step_nil caller d raw out regs ctx, rfl, rfl, fun _ => rfl, rfl⟩
      | cons b rev =>
          refine ⟨_, emit_step_cons caller d b raw rev out regs ctx, rfl, rfl, fun _ => rfl, ?_⟩
          simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega
  | undo d =>
      cases rev with
      | nil =>
          refine ⟨_, undo_step_nil caller d raw out regs ctx, rfl, rfl, fun _ => rfl, ?_⟩
          simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel, resultLabel]; omega
      | cons b rev =>
          refine ⟨_, undo_step_cons caller d b raw rev out regs ctx, rfl, rfl, fun _ => rfl, ?_⟩
          simp [potential, ownedCells, debt, phaseDebt, cfg, phaseLabel]; omega

def LocalStep (before after : Cfg Γ Λ R) : Prop := Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ after.var = reset before.var ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧ potential after = potential before := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ := owned_cases before transition.1
  obtain ⟨actual, executed, rank, registers, frame, mass⟩ := phase_step_data caller phase raw rev out regs ctx
  have same : actual = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  exact ⟨rank, registers, frame, mass⟩

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ :=
    owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ := phase_step_data caller phase raw rev out regs ctx
  exact ⟨after, executed, rank⟩

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ := owned_cases c owned
  rfl

theorem prefix_local_register (n : Nat) (start reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (positive : 0 < n) : reached.var.1 = none := by
  induction n generalizing start reached with
  | zero => omega
  | succ n ih =>
      have rankPositive : 0 < remainingSteps start := by omega
      obtain ⟨middle, first, decreased⟩ := local_progress caller start rankPositive
      have owned := (remainingSteps_pos_iff start).mp rankPositive
      have canonical := (local_step_data caller ⟨owned, first⟩).2.1
      rw [Function.iterate_succ_apply, next_some, first] at executed
      by_cases empty : n = 0
      · subst n
        have same : middle = reached := Option.some.inj executed
        simpa only [same, reset] using congrArg Prod.fst canonical
      · exact ih middle reached (by omega) executed (by omega)

theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧ (0 < n → reached.var.1 = none) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n start reached bound executed

theorem phase_prefix (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps phase raw rev) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached ∧
      remainingSteps reached = phaseSteps phase raw rev - n ∧
      Relation.ReflTransGen (LocalStep caller) (cfg (some (phaseLabel phase)) regs raw rev out ctx) reached ∧
      (n < phaseSteps phase raw rev ↔ Owned reached.l) ∧ (0 < n → reached.var.1 = none) :=
  owned_prefix caller _ n bound

theorem run_prefix (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ fullSteps raw) :
    ∃ reached, (next caller)^[n] (some (entry regs raw out ctx)) = some reached ∧
      remainingSteps reached = fullSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs raw out ctx) reached ∧
      (n < fullSteps raw ↔ Owned reached.l) ∧ (0 < n → reached.var.1 = none) :=
  owned_prefix caller _ n bound

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) := by
  exact Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

theorem run_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (raw : Word) (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ fullSteps raw) :
    (next caller)^[n] (some (entry regs raw out ctx)) =
      (next other)^[n] (some (entry regs raw out ctx)) :=
  prefix_caller_independent caller other _ n bound

theorem first_return_exact (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (returned : ¬ Owned reached.l) : n = remainingSteps start := by
  obtain ⟨actual, run, _, _, owned, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  have notStrict : ¬ n < remainingSteps start := fun h => returned (owned.mp h)
  omega

theorem run_first_return (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (resultCfg (Λ := Λ) regs raw out ctx (parseMoveRun raw).1).l ∧
      ∀ n, n < fullSteps raw → ∃ reached,
        (next caller)^[n] (some (entry regs raw out ctx)) = some reached ∧ Owned reached.l := by
  constructor
  · cases parsed : (parseMoveRun raw).1 with
    | none => simp [resultCfg, cfg, resultLabel, Owned]
    | some pair => rcases pair with ⟨move, rest⟩; simp [resultCfg, cfg, resultLabel, Owned]
  · intro n strict
    obtain ⟨reached, run, _, _, owned, _⟩ := run_prefix caller raw out regs ctx n (Nat.le_of_lt strict)
    exact ⟨reached, run, owned.mp strict⟩

theorem ambient_run_source (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (raw : Word) (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[fullSteps raw]
        (some (entry regs raw out ctx)) = some (resultCfg regs raw out ctx (parseMoveRun raw).1) := by
  rw [program_eq_of_agrees ambient agrees]
  exact run_source _ raw out regs ctx

theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      potential reached = potential start := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl, rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, frame, mass⟩ := local_step_data caller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2.1 k), mass.trans ih.2.2⟩
      simpa only [registers, reset] using ih.1

/-- Exact fields and potential for arbitrary dirty entry, up to its own first handoff. -/
theorem prefix_preserves (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = (if n = 0 then start.var else reset start.var) ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ potential reached = potential start := by
  obtain ⟨actual, run, _, path, _, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  obtain ⟨registers, frame, mass⟩ := local_reaches_preserves caller path
  refine ⟨?_, frame, mass⟩
  by_cases zero : n = 0
  · subst n
    have equal : start = reached := Option.some.inj executed
    simp only [equal, ite_true]
  · rw [ite_eq_right zero]
    apply Prod.ext
    · exact prefix_local_register caller n start reached bound executed (by omega)
    · exact registers

theorem run_prefix_preserves (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ fullSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw out ctx)) = some reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      ownedCells reached + debt reached.l = raw.length + out.length := by
  exact prefix_preserves caller (entry regs raw out ctx) reached n bound executed

section Space
variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length
def stackCells (c : Cfg Γ Λ R) : Nat := ownedCells c + contextCells (fun k => c.stk (.inr k))

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .raw + f .reverse + f .path := by
  change (∑ k ∈ ({.raw, .reverse, .path} : Finset LocalStack), f k) = _
  simp; omega

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := by
  rw [Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (raw : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs raw rev out ctx) = raw.length + rev.length + out.length + contextCells ctx := rfl

theorem owned_prefix_stackCells_le (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ ownedCells start + debt start.l + contextCells (fun k => start.stk (.inr k)) := by
  obtain ⟨_, frame, mass⟩ := prefix_preserves caller start reached n bound executed
  have sameContext : (fun k => reached.stk (.inr k)) = fun k => start.stk (.inr k) := funext frame
  have boundCells : ownedCells reached ≤ ownedCells start + debt start.l := by
    unfold potential at mass
    omega
  simpa only [stackCells, sameContext] using Nat.add_le_add_right boundCells
    (contextCells (fun k => start.stk (.inr k)))

theorem phase_prefix_stackCells_le (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps phase raw rev)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached) :
    stackCells reached ≤ raw.length + rev.length + out.length + phaseDebt phase + contextCells ctx :=
  owned_prefix_stackCells_le caller
    (cfg (some (phaseLabel phase)) regs raw rev out ctx) reached n bound executed

theorem prefix_stackCells_le (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ fullSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw out ctx)) = some reached) :
    stackCells reached ≤ raw.length + out.length + contextCells ctx := by
  simpa only [entry, ownedCells, debt, phaseDebt, phaseLabel, cfg, List.length_nil, Nat.add_zero] using
    owned_prefix_stackCells_le caller (entry regs raw out ctx) reached n bound executed

omit [DecidableEq K] in
theorem initial_stackCells (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (entry (Λ := Λ) regs raw out ctx) = raw.length + out.length + contextCells ctx := rfl

end Space

omit [DecidableEq K] in
theorem resultCfg_injective (regs : Registers R) (raw : Word) (out : List Branch)
    (ctx : ∀ k, List (Γ k)) : Function.Injective (resultCfg (Λ := Λ) regs raw out ctx) := by
  intro left right equal
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some pair =>
          rcases pair with ⟨move, rest⟩
          have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
          cases labels
  | some pair =>
      rcases pair with ⟨move, rest⟩
      cases right with
      | none =>
          have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
          cases labels
      | some pair =>
          rcases pair with ⟨other, suffix⟩
          have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
          have rawEq := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .raw)) equal
          have outputEq := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .path)) equal
          have directionEq : move.direction = other.direction := by
            simpa only [resultCfg, cfg, resultLabel, Option.some.injEq,
              Sum.inr.injEq, Sum.inl.injEq, Result.success.injEq] using labels
          change rest = suffix at rawEq
          change move.position ++ out = other.position ++ out at outputEq
          have pathEq : move.position = other.position := List.append_cancel_right outputEq
          have moveEq : move = other := by
            cases move
            cases other
            cases directionEq
            cases pathEq
            rfl
          exact congrArg some (Prod.ext moveEq rawEq)

/-- Recognition is at the actual first handoff, before any arbitrary caller runs. -/
def FirstSuccess (raw : Word) (move : RotationMove) (rest : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
    some (cfg (some (resultLabel (.success move.direction))) (reset regs)
      rest [] (move.position ++ out) ctx)

theorem firstSuccess_iff (raw : Word) (move : RotationMove) (rest : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw move rest out regs ctx ↔ (parseMoveRun raw).1 = some (move, rest) := by
  constructor
  · intro observed
    unfold FirstSuccess at observed
    rw [run_source] at observed
    exact resultCfg_injective regs raw out ctx (Option.some.inj observed)
  · exact run_of_some caller raw move rest out regs ctx

theorem firstSuccess_code_iff (raw : Word) (move : RotationMove) (rest : Word)
    (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw move rest out regs ctx ↔ raw = moveCode move ++ rest := by
  rw [firstSuccess_iff, parseMoveRun_iff]

theorem firstSuccess_emit_iff (raw : Word) (move : RotationMove) (rest : Word)
    (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw move rest out regs ctx ↔ raw = (emitMoveRun move rest).1 := by
  rw [emitMoveRun_value, firstSuccess_code_iff]

def FirstFailure (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
    some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx)

theorem firstFailure_iff (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstFailure caller raw out regs ctx ↔ (parseMoveRun raw).1 = none := by
  constructor
  · intro observed
    unfold FirstFailure at observed
    rw [run_source] at observed
    exact resultCfg_injective regs raw out ctx (Option.some.inj observed)
  · exact run_of_none caller raw out regs ctx

theorem firstSuccess_unique (raw : Word) (move other : RotationMove) (rest suffix : Word)
    (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (first : FirstSuccess caller raw move rest out regs ctx)
    (second : FirstSuccess caller raw other suffix out regs ctx) : move = other ∧ rest = suffix := by
  have left := (firstSuccess_iff caller raw move rest out regs ctx).mp first
  have right := (firstSuccess_iff caller raw other suffix out regs ctx).mp second
  exact Prod.mk.inj (Option.some.inj (left.symm.trans right))

omit [DecidableEq K] in
theorem fullSteps_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    fullSteps raw = 2 * move.position.length + 3 := by
  rw [(parseMoveRun_iff raw move rest).mp returned, fullSteps_code]

theorem firstSuccess_costs (raw : Word) (move : RotationMove) (rest : Word)
    (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : FirstSuccess caller raw move rest out regs ctx) :
    (parseMoveRun raw).2 = 3 * move.position.length + 4 ∧
      fullSteps raw = 2 * move.position.length + 3 ∧
      raw.length = move.position.length + 2 + rest.length := by
  have source := (firstSuccess_iff caller raw move rest out regs ctx).mp returned
  exact ⟨parseMoveRun_cost_of_some raw move rest source, fullSteps_of_some raw move rest source,
    parseMoveRun_consumed_length raw move rest source⟩

theorem firstFailure_cost (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : FirstFailure caller raw out regs ctx) :
    (parseMoveRun raw).2 = fullSteps raw + 1 :=
  parseMoveRun_failure_cost raw ((firstFailure_iff caller raw out regs ctx).mp failed)

omit [DecidableEq K] in
theorem parsePathRun_prefix_none (accepted : List Branch) (raw : Word)
    (failed : (parsePathRun raw).1 = none) :
    (parsePathRun (pathTags accepted ++ raw)).1 = none := by
  induction accepted with
  | nil => exact failed
  | cons b accepted ih =>
      change (parsePathRun (branchTag b :: (pathTags accepted ++ raw))).1 = none
      rw [parsePathRun_branch]
      simp only [Resources.bind, ih]

omit [DecidableEq K] in
theorem parsePathRun_eof_prefix (accepted : List Branch) :
    parsePathRun (pathTags accepted) = (none, 2 * accepted.length + 2) := by
  have failed : (parsePathRun (pathTags accepted)).1 = none := by
    simpa only [List.append_nil] using parsePathRun_prefix_none accepted [] rfl
  apply Prod.ext failed
  have count : branchCount (pathTags accepted) = accepted.length := by
    simpa only [List.append_nil, branchCount_nil, Nat.add_zero] using branchCount_prefix accepted []
  simpa only [count] using parsePathRun_failure_cost (pathTags accepted) failed

omit [DecidableEq K] in
theorem parsePathRun_foreign_prefix (accepted : List Branch) (tag : Tag) (tail : Word)
    (ended : tag ≠ endMoveTag) (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    parsePathRun (pathTags accepted ++ tag :: tail) = (none, 2 * accepted.length + 2) := by
  have failed : (parsePathRun (pathTags accepted ++ tag :: tail)).1 = none :=
    parsePathRun_prefix_none accepted (tag :: tail) (by rw [parsePathRun_foreign tag tail ended left right])
  apply Prod.ext failed
  have count : branchCount (pathTags accepted ++ tag :: tail) = accepted.length := by
    rw [branchCount_prefix, branchCount_foreign tag tail left right, Nat.add_zero]
  simpa only [count] using parsePathRun_failure_cost (pathTags accepted ++ tag :: tail) failed

omit [DecidableEq K] in
theorem parseMoveRun_eof_prefix (d : RotationDirection) (accepted : List Branch) :
    parseMoveRun (directionTag d :: pathTags accepted) = (none, 2 * accepted.length + 4) := by
  rw [parseMoveRun_direction, parsePathRun_eof_prefix]
  simp only [Resources.bind]

omit [DecidableEq K] in
theorem parseMoveRun_foreign_prefix (d : RotationDirection) (accepted : List Branch) (tag : Tag) (tail : Word)
    (ended : tag ≠ endMoveTag) (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    parseMoveRun (directionTag d :: (pathTags accepted ++ tag :: tail)) =
      (none, 2 * accepted.length + 4) := by
  rw [parseMoveRun_direction, parsePathRun_foreign_prefix accepted tag tail ended left right]
  simp only [Resources.bind]

theorem run_eof_prefix (d : RotationDirection) (accepted out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + 3]
        (some (entry regs (directionTag d :: pathTags accepted) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: pathTags accepted) [] out ctx) := by
  have count : branchCount (pathTags accepted) = accepted.length := by
    simpa only [List.append_nil, branchCount_nil, Nat.add_zero] using branchCount_prefix accepted []
  simpa only [fullSteps_direction, count, parseMoveRun_eof_prefix, resultCfg] using
    run_source caller (directionTag d :: pathTags accepted) out regs ctx

theorem run_foreign_prefix (d : RotationDirection) (accepted : List Branch) (tag : Tag) (tail : Word)
    (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (ended : tag ≠ endMoveTag) (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    (next caller)^[2 * accepted.length + 3]
        (some (entry regs (directionTag d :: (pathTags accepted ++ tag :: tail)) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags accepted ++ tag :: tail)) [] out ctx) := by
  have count : branchCount (pathTags accepted ++ tag :: tail) = accepted.length := by
    rw [branchCount_prefix, branchCount_foreign tag tail left right, Nat.add_zero]
  simpa only [fullSteps_direction, count,
    parseMoveRun_foreign_prefix d accepted tag tail ended left right, resultCfg] using
    run_source caller (directionTag d :: (pathTags accepted ++ tag :: tail)) out regs ctx

/-- The malformed family has exactly N raw cells, including N = 0. -/
def sharpRaw : Nat → Word
  | 0 => []
  | n + 1 => directionTag .left :: pathTags (List.replicate n Branch.left)

@[simp] theorem sharpRaw_length (n : Nat) : (sharpRaw n).length = n := by
  cases n <;> simp [sharpRaw]

theorem sharpRaw_eq (n : Nat) : sharpRaw (n + 1) = rotateLeftTag :: List.replicate n pathLeftTag := by
  simp only [sharpRaw, pathTags, List.map_replicate]
  rfl

@[simp] theorem fullSteps_sharpRaw (n : Nat) : fullSteps (sharpRaw n) = 2 * n + 1 := by
  cases n with
  | zero => rfl
  | succ n =>
      have count : branchCount (pathTags (List.replicate n Branch.left)) = n := by
        simpa only [List.append_nil, List.length_replicate, branchCount_nil, Nat.add_zero] using
          branchCount_prefix (List.replicate n Branch.left) []
      rw [sharpRaw, fullSteps_direction, count]
      omega

theorem parseMoveRun_sharpRaw (n : Nat) : parseMoveRun (sharpRaw n) = (none, 2 * n + 2) := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [sharpRaw, parseMoveRun_eof_prefix, List.length_replicate]
      congr 1

theorem run_sharpRaw (n : Nat) (out : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * n + 1] (some (entry regs (sharpRaw n) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) (sharpRaw n) [] out ctx) := by
  simpa only [fullSteps_sharpRaw, parseMoveRun_sharpRaw, resultCfg] using
    run_source caller (sharpRaw n) out regs ctx

theorem sharpRaw_first_return (n : Nat) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (j : Nat) (strict : j < 2 * n + 1) :
    ∃ reached, (next caller)^[j] (some (entry regs (sharpRaw n) out ctx)) = some reached ∧ Owned reached.l := by
  exact (run_first_return caller (sharpRaw n) out regs ctx).2 j (by simpa only [fullSteps_sharpRaw] using strict)

theorem time_bound_sharp (n : Nat) :
    ∃ raw : Word, raw.length = n ∧ fullSteps raw = 2 * n + 1 ∧ (parseMoveRun raw).1 = none :=
  ⟨sharpRaw n, sharpRaw_length n, fullSteps_sharpRaw n, by rw [parseMoveRun_sharpRaw]⟩

section SharpSpace
variable [Fintype K]

omit [DecidableEq K] in
theorem sharpRaw_return_cells (n : Nat) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (Λ := Λ) (some (resultLabel .failure)) (reset regs) (sharpRaw n) [] out ctx) =
      n + out.length + contextCells ctx := by
  simp only [stackCells_cfg, sharpRaw_length, List.length_nil, Nat.add_zero]

theorem space_bound_sharp (n : Nat) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∃ reached, (next caller)^[2 * n + 1] (some (entry regs (sharpRaw n) out ctx)) = some reached ∧
      ¬ Owned reached.l ∧ stackCells reached = n + out.length + contextCells ctx ∧ 0 < 2 * n + 1 := by
  refine ⟨_, run_sharpRaw caller n out regs ctx, ?_, sharpRaw_return_cells n out regs ctx, ?_⟩
  · simp [Owned, cfg, resultLabel]
  · omega

end SharpSpace

omit [DecidableEq K] in
def startResult (regs : Registers R) (raw : Word) (rev out : List Branch)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  match raw with
  | [] => cfg (some (resultLabel .failure)) (reset regs) [] rev out ctx
  | tag :: rest =>
      if tag = rotateLeftTag then scanResult .left regs rest rev out ctx (parsePathRun rest).1
      else if tag = rotateRightTag then scanResult .right regs rest rev out ctx (parsePathRun rest).1
      else cfg (some (resultLabel .failure)) (reset regs) raw rev out ctx

/-- Dirty start is also total: immediate failure preserves its preexisting reverse stack. -/
theorem start_iterate (raw : Word) (rev out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[startSteps raw rev]
        (some (cfg (some (phaseLabel .start)) regs raw rev out ctx)) =
      some (startResult regs raw rev out ctx) := by
  cases raw with
  | nil =>
      simpa only [startSteps, startResult, Function.iterate_one, next_some] using
        start_step_nil caller rev out regs ctx
  | cons tag raw =>
      have directionCase (d : RotationDirection) :
          (next caller)^[startSteps (directionTag d :: raw) rev]
              (some (cfg (some (phaseLabel .start)) regs (directionTag d :: raw) rev out ctx)) =
            some (scanResult d regs raw rev out ctx (parsePathRun raw).1) := by
        rw [startSteps_direction,
          iterate_step caller _ _ _ (start_step_direction caller d raw rev out regs ctx), scan_iterate]
        cases parsed : (parsePathRun raw).1 with
        | none => rfl
        | some pair => rcases pair with ⟨path, rest⟩; rfl
      by_cases left : tag = rotateLeftTag
      · subst tag
        exact directionCase .left
      · by_cases right : tag = rotateRightTag
        · subst tag
          exact directionCase .right
        · simpa only [startSteps_foreign tag raw rev left right, startResult,
            ite_eq_right left, ite_eq_right right, Function.iterate_one, next_some] using
            start_step_foreign caller tag raw rev out regs ctx left right

omit [DecidableEq K] in
def phaseResult (phase : Phase) (regs : Registers R) (raw : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  match phase with
  | .start => startResult regs raw rev out ctx
  | .scan d => scanResult d regs raw rev out ctx (parsePathRun raw).1
  | .emit d => cfg (some (resultLabel (.success d))) (reset regs) raw [] (rev.reverse ++ out) ctx
  | .undo d => cfg (some (resultLabel .failure)) (reset regs)
      (directionTag d :: (pathTags rev.reverse ++ raw)) [] out ctx

theorem phase_iterate (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps phase raw rev]
        (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) =
      some (phaseResult phase regs raw rev out ctx) := by
  cases phase with
  | start => exact start_iterate caller raw rev out regs ctx
  | scan d => exact scan_iterate caller d raw rev out regs ctx
  | emit d => exact emit_iterate caller d raw rev out regs ctx
  | undo d => exact undo_iterate caller d raw rev out regs ctx

omit [DecidableEq K] in
theorem scanResult_not_owned (d : RotationDirection) (regs : Registers R) (raw : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) (parsed : Option (List Branch × Word)) :
    ¬ Owned (scanResult (Λ := Λ) d regs raw rev out ctx parsed).l := by
  cases parsed with
  | none => simp only [scanResult, cfg, resultLabel, Owned, not_false_eq_true]
  | some pair =>
      rcases pair with ⟨path, rest⟩
      simp only [scanResult, cfg, resultLabel, Owned, not_false_eq_true]

omit [DecidableEq K] in
theorem phaseResult_not_owned (phase : Phase) (regs : Registers R) (raw : Word)
    (rev out : List Branch) (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (phaseResult (Λ := Λ) phase regs raw rev out ctx).l := by
  cases phase with
  | start =>
      cases raw with
      | nil => simp only [phaseResult, startResult, cfg, resultLabel, Owned, not_false_eq_true]
      | cons tag raw =>
          simp only [phaseResult, startResult]
          split
          · exact scanResult_not_owned _ _ _ _ _ _ _
          · split
            · exact scanResult_not_owned _ _ _ _ _ _ _
            · simp only [cfg, resultLabel, Owned, not_false_eq_true]
  | scan d => exact scanResult_not_owned _ _ _ _ _ _ _
  | emit d => simp only [phaseResult, cfg, resultLabel, Owned, not_false_eq_true]
  | undo d => simp only [phaseResult, cfg, resultLabel, Owned, not_false_eq_true]

theorem phase_first_return (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (phaseResult (Λ := Λ) phase regs raw rev out ctx).l ∧
      ∀ n, n < phaseSteps phase raw rev → ∃ reached,
        (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached ∧
          Owned reached.l := by
  refine ⟨phaseResult_not_owned phase regs raw rev out ctx, ?_⟩
  intro n strict
  obtain ⟨reached, run, _, _, owned, _⟩ := phase_prefix caller phase raw rev out regs ctx n (Nat.le_of_lt strict)
  exact ⟨reached, run, owned.mp strict⟩

def phaseInTime (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel phase)) regs raw rev out ctx)
      (some (phaseResult phase regs raw rev out ctx)) (phaseSteps phase raw rev) where
  steps := phaseSteps phase raw rev
  evals_in_steps := phase_iterate caller phase raw rev out regs ctx
  steps_le_m := Nat.le_refl _

theorem ambient_prefix_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact prefix_caller_independent _ caller start n bound

section FinitePackage

def ownedLabelEquiv : Phase ≃ {label : Label Λ // Owned (some label)} where
  toFun phase := ⟨phaseLabel phase, True.intro⟩
  invFun
    | ⟨.inl phase, _⟩ => phase
    | ⟨.inr _, bad⟩ => False.elim bad
  left_inv _ := rfl
  right_inv label := by
    rcases label with ⟨label, owned⟩
    cases label with
    | inl phase => rfl
    | inr external => cases owned

instance ownedFintype : Fintype {label : Label Λ // Owned (some label)} :=
  Fintype.ofEquiv Phase ownedLabelEquiv

theorem owned_card : Fintype.card {label : Label Λ // Owned (some label)} = 7 := by
  calc
    _ = Fintype.card Phase := (Fintype.card_congr ownedLabelEquiv).symm
    _ = 7 := by decide

theorem phase_card : Fintype.card Phase = 7 := by decide
theorem result_card : Fintype.card Result = 3 := by decide
theorem branch_card : Fintype.card Branch = 2 := by decide
theorem direction_card : Fintype.card RotationDirection = 2 := by decide

omit [DecidableEq K] in
theorem stackId_card [Fintype K] : Fintype.card (StackId K) = 3 + Fintype.card K := by
  rw [Fintype.card_sum]
  rfl

theorem label_card [Fintype Λ] : Fintype.card (Label Λ) = 10 + Fintype.card Λ := by
  simp only [Label, External, Fintype.card_sum, phase_card, result_card]
  omega

theorem registers_card [Fintype R] : Fintype.card (Registers R) = 17 * Fintype.card R := by
  have tagCard : Fintype.card Tag = 16 := by decide
  simp only [Registers, Fintype.card_prod, Fintype.card_option, tagCard]

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- Fixed finite blocks and caller, chosen before raw data; the local results stay live. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .raw
  k₁ := .inl .path
  Γ := Alphabet Γ
  Λ := Label Λ
  main := phaseLabel .start
  σ := Registers R
  initialState := (none, initial)
  Γk₀Fin := alphabetFintype (.inl .raw)
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw = entry (none, initial) raw [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem machine_run_source (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[fullSteps raw]
        (some (Turing.initList (machine caller initial) raw)) =
      some (resultCfg (none, initial) raw [] (fun _ => []) (parseMoveRun raw).1) := by
  rw [initList_eq]
  exact run_source caller raw [] (none, initial) (fun _ => [])

def machineRunInTime (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (resultCfg (none, initial) raw [] (fun _ => []) (parseMoveRun raw).1)) (fullSteps raw) where
  steps := fullSteps raw
  evals_in_steps := machine_run_source caller initial raw
  steps_le_m := Nat.le_refl _

def machineRunInLinearTime (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (resultCfg (none, initial) raw [] (fun _ => []) (parseMoveRun raw).1)) (2 * raw.length + 1) where
  steps := fullSteps raw
  evals_in_steps := machine_run_source caller initial raw
  steps_le_m := fullSteps_le raw

theorem machine_prefix_stackCells_le (initial : R) (raw : Word) (n : Nat)
    (bound : n ≤ fullSteps raw) (reached : Cfg Γ Λ R)
    (executed :
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached) :
    stackCells reached ≤ raw.length := by
  rw [initList_eq] at executed
  have cells := prefix_stackCells_le caller raw [] (none, initial) (fun _ => []) n bound reached executed
  simpa [contextCells] using cells

end FinitePackage

end Resources.RotationCertificate.MoveParserMachine

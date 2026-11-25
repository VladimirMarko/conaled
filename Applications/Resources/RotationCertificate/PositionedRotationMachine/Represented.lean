import Applications.Resources.RotationCertificate.PositionedRotationMachine.Execution

/-!
# PositionedRotationMachine: Represented
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.PositionedRotationMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Scanning, represented execution and source refinement -/

/-- Exact represented first-return clock; no runtime callback evaluates it. -/
def representedClock : RotationDirection → List Branch → BinaryTree Unit → Nat
  | _, [], .nil => 4
  | .left, [], .node _ A .nil => 2 * (treeCode A).length + 6
  | .left, [], .node _ A (.node _ _ _) => 2 * (treeCode A).length + 5
  | .right, [], .node _ .nil _ => 4
  | .right, [], .node _ (.node _ A _) _ => 2 * (treeCode A).length + 4
  | _, _ :: _, .nil => 3
  | d, .left :: p, .node _ l _ => representedClock d p l + 2
  | d, .right :: p, .node _ l r =>
      representedClock d p r + 2 * (1 + (treeCode l).length)

/-- Actual physical tail: the head that fails at nil has already been popped. -/
def remainingPath : List Branch → BinaryTree Unit → List Branch
  | [], _ => []
  | _ :: p, .nil => p
  | .left :: p, .node _ l _ => remainingPath p l
  | .right :: p, .node _ _ r => remainingPath p r

/-- Successful ancestor descents, excluding a final missing-node observation. -/
def descentCount : List Branch → BinaryTree Unit → Nat
  | [], _ => 0
  | _ :: _, .nil => 0
  | .left :: p, .node _ l _ => 1 + descentCount p l
  | .right :: p, .node _ _ r => 1 + descentCount p r

/-- Number of source Tags physically moved to saved during navigation. -/
def navigationLength : List Branch → BinaryTree Unit → Nat
  | [], _ => 0
  | _ :: _, .nil => 0
  | .left :: p, .node _ l _ => 1 + navigationLength p l
  | .right :: p, .node _ l r =>
      1 + (treeCode l).length + navigationLength p r

/-- The focused tree before the final empty-path or missing-node observation. -/
def stoppedTree : List Branch → BinaryTree Unit → BinaryTree Unit
  | [], t => t
  | _ :: _, .nil => .nil
  | .left :: p, .node _ l _ => stoppedTree p l
  | .right :: p, .node _ _ r => stoppedTree p r

/-- The untested path at the stopped cursor; unlike remainingPath it keeps a failing head. -/
def stoppedPath : List Branch → BinaryTree Unit → List Branch
  | [], _ => []
  | b :: p, .nil => b :: p
  | .left :: p, .node _ l _ => stoppedPath p l
  | .right :: p, .node _ _ r => stoppedPath p r

omit [DecidableEq K] in
theorem remainingPath_suffix (p : List Branch) (s : BinaryTree Unit) :
    ∃ consumed, p = consumed ++ remainingPath p s := by
  induction p generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons b p ih =>
      cases s with
      | nil => exact ⟨[b], rfl⟩
      | node a l r =>
          cases b with
          | left =>
              obtain ⟨consumed, word⟩ := ih l
              exact ⟨.left :: consumed, congrArg (List.cons .left) word⟩
          | right =>
              obtain ⟨consumed, word⟩ := ih r
              exact ⟨.right :: consumed, congrArg (List.cons .right) word⟩

omit [DecidableEq K] in
theorem remainingPath_eq_stopped (p : List Branch) (s : BinaryTree Unit) :
    remainingPath p s =
      if stoppedPath p s = [] then [] else (stoppedPath p s).tail := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => simp only [remainingPath, stoppedPath, List.cons_ne_nil, ite_false,
          List.tail_cons]
      | node a l r => cases b with
        | left => exact ih l
        | right => exact ih r

omit [DecidableEq K] in
theorem stoppedTree_nil_of_path_nonempty (p : List Branch) (s : BinaryTree Unit)
    (nonempty : stoppedPath p s ≠ []) : stoppedTree p s = .nil := by
  induction p generalizing s with
  | nil => exact (nonempty rfl).elim
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r => cases b with
        | left => exact ih l nonempty
        | right => exact ih r nonempty

omit [DecidableEq K] in
theorem representedClock_eq_stopped (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) :
    representedClock d p s = 2 * navigationLength p s +
      if stoppedPath p s = [] then representedClock d [] (stoppedTree p s) else 3 := by
  induction p generalizing s with
  | nil => simp only [navigationLength, stoppedPath, stoppedTree, ite_true,
      Nat.mul_zero, Nat.zero_add]
  | cons b p ih =>
      cases s with
      | nil => simp only [representedClock, navigationLength, stoppedPath,
          List.cons_ne_nil, ite_false, Nat.mul_zero, Nat.zero_add]
      | node a l r =>
          cases b with
          | left =>
              simp only [representedClock, navigationLength, stoppedPath, stoppedTree]
              rw [ih l]
              by_cases ending : stoppedPath p l = [] <;> simp [ending] <;> omega
          | right =>
              simp only [representedClock, navigationLength, stoppedPath, stoppedTree]
              rw [ih r]
              by_cases ending : stoppedPath p r = [] <;> simp [ending] <;> omega

/-- A nearest-focus-first frame; its Unit payload is the actual encoded payload. -/
inductive PositionFrame where
  | cameLeft (right : BinaryTree Unit)
  | cameRight (left : BinaryTree Unit)

def plugFrames : List PositionFrame → BinaryTree Unit → BinaryTree Unit
  | [], focus => focus
  | .cameLeft right :: outer, focus => plugFrames outer (.node () focus right)
  | .cameRight left :: outer, focus => plugFrames outer (.node () left focus)

def contextPrefix : List PositionFrame → Word
  | [] => []
  | .cameLeft _ :: outer => contextPrefix outer ++ [nodeTag]
  | .cameRight left :: outer => contextPrefix outer ++ [nodeTag] ++ treeCode left

def contextSuffix : List PositionFrame → Word
  | [] => []
  | .cameLeft right :: outer => treeCode right ++ contextSuffix outer
  | .cameRight _ :: outer => contextSuffix outer

omit [DecidableEq K] in
theorem treeCode_plugFrames (frames : List PositionFrame) (focus : BinaryTree Unit) :
    treeCode (plugFrames frames focus) =
      contextPrefix frames ++ treeCode focus ++ contextSuffix frames := by
  induction frames generalizing focus with
  | nil => simp only [plugFrames, contextPrefix, contextSuffix, List.nil_append, List.append_nil]
  | cons frame outer ih =>
      cases frame with
      | cameLeft right =>
          rw [plugFrames, ih]
          simp only [contextPrefix, contextSuffix, treeCode, List.append_assoc,
            List.cons_append, List.nil_append]
      | cameRight left =>
          rw [plugFrames, ih]
          simp only [contextPrefix, contextSuffix, treeCode, List.append_assoc,
            List.cons_append, List.nil_append]

omit [DecidableEq K] in
theorem source_root (d : RotationDirection) (s : BinaryTree Unit) :
    applyMoveRun ⟨d, []⟩ s = ((rotateRun d s).1, (rotateRun d s).2 + 1) :=
  applyAtRun_root (rotateRun d) s

omit [DecidableEq K] in
theorem source_nil_cons (d : RotationDirection) (b : Branch) (p : List Branch) :
    applyMoveRun ⟨d, b :: p⟩ (.nil : BinaryTree Unit) = (none, 2) :=
  applyAtRun_nil_cons (rotateRun d) b p

omit [DecidableEq K] in
theorem source_left (d : RotationDirection) (p : List Branch) (l r : BinaryTree Unit) :
    applyMoveRun ⟨d, .left :: p⟩ (.node () l r) =
      let actual := applyMoveRun ⟨d, p⟩ l
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node () child r), actual.2 + 3) := by
  unfold applyMoveRun
  rw [applyAtRun_left]
  dsimp only
  cases result : (applyAtRun (rotateRun d) p l).1 <;> rfl

omit [DecidableEq K] in
theorem source_right (d : RotationDirection) (p : List Branch) (l r : BinaryTree Unit) :
    applyMoveRun ⟨d, .right :: p⟩ (.node () l r) =
      let actual := applyMoveRun ⟨d, p⟩ r
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node () l child), actual.2 + 3) := by
  unfold applyMoveRun
  rw [applyAtRun_right]
  dsimp only
  cases result : (applyAtRun (rotateRun d) p r).1 <;> rfl

omit [DecidableEq K] in
theorem source_cost_eq_stopped (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) :
    (applyMoveRun ⟨d, p⟩ s).2 =
      if (applyMoveRun ⟨d, p⟩ s).1.isSome then 3 * descentCount p s + 5
      else 2 * descentCount p s + if stoppedPath p s = [] then 3 else 2 := by
  induction p generalizing s with
  | nil =>
      rw [source_root]
      cases actual : (rotateRun d s).1 with
      | none =>
          rw [rotateRun_cost_of_none d s actual]
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false,
            descentCount, stoppedPath, ite_true, Nat.mul_zero, Nat.zero_add]
      | some t =>
          rw [rotateRun_cost_of_some d s t actual]
          simp only [Option.isSome_some, ite_true, descentCount,
            Nat.mul_zero, Nat.zero_add]
  | cons b p ih =>
      cases s with
      | nil => simp [source_nil_cons, descentCount, stoppedPath]
      | node a l r =>
          cases a
          cases b with
          | left =>
              have child := ih l
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 <;>
                by_cases ending : stoppedPath p l = [] <;>
                simp [source_left, actual, descentCount, stoppedPath, ending] at child ⊢ <;> omega
          | right =>
              have child := ih r
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 <;>
                by_cases ending : stoppedPath p r = [] <;>
                simp [source_right, actual, descentCount, stoppedPath, ending] at child ⊢ <;> omega

omit [DecidableEq K] in
theorem remainingPath_nil_of_source_success (d : RotationDirection) (p : List Branch)
    (s t : BinaryTree Unit) (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) :
    remainingPath p s = [] := by
  induction p generalizing s t with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => simp only [source_nil_cons, reduceCtorEq] at returned
      | node a l r =>
          cases a
          cases b with
          | left =>
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 with
              | none => simp only [source_left, actual, reduceCtorEq] at returned
              | some child => exact ih l child actual
          | right =>
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 with
              | none => simp only [source_right, actual, reduceCtorEq] at returned
              | some child => exact ih r child actual

/-- A word whose scan does not yet discharge the last pending slot. -/
inductive Continues : Word → Nat → Nat → Prop where
  | nil (h : Nat) : Continues [] h h
  | node {accepted : Word} {h k : Nat} :
      Continues accepted h k → Continues (accepted ++ [nodeTag]) h (k + 1)
  | empty {accepted : Word} {h k : Nat} :
      Continues accepted h (k + 2) → Continues (accepted ++ [emptyTag]) h (k + 1)

omit [DecidableEq K] in
theorem continues_of_openPrefix {accepted : Word} {p : Nat}
    (opened : TreeParserMachine.OpenPrefix accepted p) : Continues accepted 1 p := by
  induction opened with
  | nil => exact .nil 1
  | node opened ih => exact .node ih
  | empty opened ih => exact .empty ih

/-- Zero accepted symbols preserve stale fields; positive scan prefixes reset them. -/
def afterScanRegisters (accepted : Word) (regs : Registers R) : Registers R :=
  if accepted = [] then regs else reset regs

omit [DecidableEq K] in
@[simp] theorem reset_afterScanRegisters (accepted : Word) (regs : Registers R) :
    reset (afterScanRegisters accepted regs) = reset regs := by
  cases accepted <;> rfl

omit [DecidableEq K] in
@[simp] theorem afterScanRegisters_append (accepted : Word) (tag : Tag)
    (regs : Registers R) : afterScanRegisters (accepted ++ [tag]) regs = reset regs := by
  simp only [afterScanRegisters, List.append_eq_nil_iff, List.cons_ne_nil, and_false, ite_false]

/-- Every continued prefix is an actual owned segment in the saved-word scanner. -/
theorem scanPrefix_continues_localRun {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          saved := accepted.reverse ++ D.saved,
          pending := List.replicate k () } ctx) := by
  induction continued generalizing raw D regs with
  | nil h =>
      simpa only [List.length_nil, List.nil_append, List.reverse_nil,
        afterScanRegisters, ite_true] using
        (LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.scanPrefix d))) regs
            { D with source := raw, pending := List.replicate h () } ctx))
  | @node accepted h k continued ih =>
      let middle : LocalData := { D with
        source := nodeTag :: raw,
        saved := accepted.reverse ++ D.saved,
        pending := List.replicate k () }
      have first := ih (nodeTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := raw,
              saved := nodeTag :: (accepted.reverse ++ D.saved),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, reset_afterScanRegisters, List.replicate_succ] using
          scanPrefix_step_node caller d raw middle (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined
  | @empty accepted h k continued ih =>
      let middle : LocalData := { D with
        source := emptyTag :: raw,
        saved := accepted.reverse ++ D.saved,
        pending := List.replicate (k + 2) () }
      have first := ih (emptyTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := raw,
              saved := emptyTag :: (accepted.reverse ++ D.saved),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, List.replicate_succ, reset_afterScanRegisters] using
          scanPrefix_step_empty_continue caller d raw (List.replicate k ()) middle
            (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined

/-- Every continued prefix is an actual owned segment in either scratch scanner. -/
theorem scanScratch_continues_localRun {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          scratch := accepted.reverse ++ D.scratch,
          pending := List.replicate k () } ctx) := by
  induction continued generalizing raw D regs with
  | nil h =>
      simpa only [List.length_nil, List.nil_append, List.reverse_nil,
        afterScanRegisters, ite_true] using
        (LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.scanScratch d))) regs
            { D with source := raw, pending := List.replicate h () } ctx))
  | @node accepted h k continued ih =>
      let middle : LocalData := { D with
        source := nodeTag :: raw,
        scratch := accepted.reverse ++ D.scratch,
        pending := List.replicate k () }
      have first := ih (nodeTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := raw,
              scratch := nodeTag :: (accepted.reverse ++ D.scratch),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, reset_afterScanRegisters, List.replicate_succ] using
          scanScratch_step_node caller d raw middle (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined
  | @empty accepted h k continued ih =>
      let middle : LocalData := { D with
        source := emptyTag :: raw,
        scratch := accepted.reverse ++ D.scratch,
        pending := List.replicate (k + 2) () }
      have first := ih (emptyTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := raw,
              scratch := emptyTag :: (accepted.reverse ++ D.scratch),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, List.replicate_succ, reset_afterScanRegisters] using
          scanScratch_step_empty_continue caller d raw (List.replicate k ()) middle
            (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined

/-- A completed subtree consumes one pending slot and chooses this saved-scanner phase. -/
def prefixScanEnd (d : RotationDirection) (outer : List Unit) : Phase :=
  if outer = [] then .seek d else .scanPrefix d

/-- Scratch completion can finish the left scan or perform the right marker insertion. -/
def scratchScanEnd (d : RotationDirection) (outer : List Unit) : Phase :=
  if outer = [] then
    match d with
    | .left => .checkRight
    | .right => .restoreScratch .successRight
  else .scanScratch d

/-- The right scanner has already pushed its node in the last scanning activation. -/
def scratchScanSource (d : RotationDirection) (outer : List Unit) (raw : Word) : Word :=
  if outer = [] then
    match d with
    | .left => raw
    | .right => nodeTag :: raw
  else raw

/-- One represented tree is scanned into an arbitrary saved accumulator, with every outer slot. -/
theorem scanPrefix_treeCode_localRun (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (treeCode t).length
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)
      (cfg (some (phaseLabel (prefixScanEnd d outer))) (reset regs)
        { D with
          source := raw,
          saved := (treeCode t).reverse ++ D.saved,
          pending := outer } ctx) := by
  induction t generalizing raw outer D regs with
  | nil =>
      cases outer with
      | nil =>
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, prefixScanEnd, ite_true] using
            scanPrefix_step_empty_finish caller d raw { D with pending := [()] } regs ctx rfl
      | cons token outer =>
          cases token
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, prefixScanEnd, List.cons_ne_nil, ite_false] using
            scanPrefix_step_empty_continue caller d raw outer D regs ctx
  | node a l r ihl ihr =>
      cases a
      have head : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) regs
            { D with source := treeCode (.node () l r) ++ raw, pending := () :: outer } ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := treeCode l ++ (treeCode r ++ raw),
              saved := nodeTag :: D.saved,
              pending := () :: () :: outer } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [treeCode, List.cons_append, List.append_assoc] using
          scanPrefix_step_node caller d (treeCode l ++ (treeCode r ++ raw))
            { D with pending := () :: outer } regs ctx
      have left := ihl (treeCode r ++ raw) (() :: outer)
        { D with saved := nodeTag :: D.saved } (reset regs)
      simp only [prefixScanEnd, List.cons_ne_nil, ite_false, reset_reset] at left
      have right := ihr raw outer
        { D with saved := (treeCode l).reverse ++ nodeTag :: D.saved } (reset regs)
      have joined := LocalRun.trans caller head (LocalRun.trans caller left right)
      simpa only [treeCode, List.length_cons, List.length_append, List.reverse_cons,
        List.reverse_append, List.append_assoc, List.singleton_append, reset_reset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- One represented tree is scanned into arbitrary scratch, with a literal untouched suffix. -/
theorem scanScratch_treeCode_localRun (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (treeCode t).length
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)
      (cfg (some (phaseLabel (scratchScanEnd d outer))) (reset regs)
        { D with
          source := scratchScanSource d outer raw,
          scratch := (treeCode t).reverse ++ D.scratch,
          pending := outer } ctx) := by
  induction t generalizing raw outer D regs with
  | nil =>
      cases outer with
      | nil =>
          cases d with
          | left =>
              apply LocalRun.single caller
              refine ⟨True.intro, ?_⟩
              simpa only [treeCode, List.singleton_append, List.reverse_cons,
                List.reverse_nil, List.nil_append, scratchScanEnd, scratchScanSource,
                ite_true] using
                scanScratch_left_step_finish caller raw { D with pending := [()] } regs ctx rfl
          | right =>
              apply LocalRun.single caller
              refine ⟨True.intro, ?_⟩
              simpa only [treeCode, List.singleton_append, List.reverse_cons,
                List.reverse_nil, List.nil_append, scratchScanEnd, scratchScanSource,
                ite_true] using
                scanScratch_right_step_finish caller raw { D with pending := [()] } regs ctx rfl
      | cons token outer =>
          cases token
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false] using
            scanScratch_step_empty_continue caller d raw outer D regs ctx
  | node a l r ihl ihr =>
      cases a
      have head : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) regs
            { D with source := treeCode (.node () l r) ++ raw, pending := () :: outer } ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := treeCode l ++ (treeCode r ++ raw),
              scratch := nodeTag :: D.scratch,
              pending := () :: () :: outer } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [treeCode, List.cons_append, List.append_assoc] using
          scanScratch_step_node caller d (treeCode l ++ (treeCode r ++ raw))
            { D with pending := () :: outer } regs ctx
      have left := ihl (treeCode r ++ raw) (() :: outer)
        { D with scratch := nodeTag :: D.scratch } (reset regs)
      simp only [scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false, reset_reset] at left
      have right := ihr raw outer
        { D with scratch := (treeCode l).reverse ++ nodeTag :: D.scratch } (reset regs)
      have joined := LocalRun.trans caller head (LocalRun.trans caller left right)
      simpa only [treeCode, List.length_cons, List.length_append, List.reverse_cons,
        List.reverse_append, List.append_assoc, List.singleton_append, reset_reset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined


/-- A continued saved scan pays for the blocked probe, pending cleanup and saved restoration. -/
theorem scanPrefix_blocked_localRun {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + k + D.saved.length + 3)
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { D with
          source := D.saved.reverse ++ accepted ++ raw,
          saved := [], pending := [] } ctx) := by
  let middle : LocalData := { D with
    source := raw, saved := accepted.reverse ++ D.saved, pending := List.replicate k () }
  have first := scanPrefix_continues_localRun caller continued d raw D regs ctx
  have probe : LocalRun caller 1
      (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) middle ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases raw with
    | nil =>
        simpa only [middle, reset_afterScanRegisters] using
          scanPrefix_step_nil caller d middle (afterScanRegisters accepted regs) ctx
    | cons tag raw =>
        simpa only [middle, reset_afterScanRegisters] using
          scanPrefix_step_foreign caller d tag raw middle (afterScanRegisters accepted regs)
            ctx blocked.1 blocked.2
  have cleanup := dropPending_localRun caller middle (reset regs) ctx
  have joined := LocalRun.trans caller first (LocalRun.trans caller probe cleanup)
  convert joined using 1 <;>
    simp [middle, dropPendingData, List.reverse_append, List.append_assoc]; omega

/-- A continued scratch scan restores both accumulators and the exact missing root markers. -/
theorem scanScratch_blocked_localRun {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + k + D.scratch.length + D.saved.length + 4)
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := D.saved.reverse ++ markerWord (scratchFailure d) ++
            D.scratch.reverse ++ accepted ++ raw,
          saved := [], scratch := [], pending := [], path := D.path } ctx) := by
  let middle : LocalData := { D with
    source := raw, scratch := accepted.reverse ++ D.scratch, pending := List.replicate k () }
  have first := scanScratch_continues_localRun caller continued d raw D regs ctx
  have probe : LocalRun caller 1
      (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
      (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs) middle ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases raw with
    | nil =>
        simpa only [middle, reset_afterScanRegisters] using
          scanScratch_step_nil caller d middle (afterScanRegisters accepted regs) ctx
    | cons tag raw =>
        simpa only [middle, reset_afterScanRegisters] using
          scanScratch_step_foreign caller d tag raw middle (afterScanRegisters accepted regs)
            ctx blocked.1 blocked.2
  have cleanup := restoreScratch_localRun caller (scratchFailure d) middle (reset regs) ctx
  have joined := LocalRun.trans caller first (LocalRun.trans caller probe cleanup)
  cases d <;> convert joined using 1 <;>
    simp [middle, restoreScratchSteps, restoreScratchData, scratchFailure, modeResult,
      List.reverse_append, List.append_assoc] <;> omega

/-- A clean left-root pattern returns after the actual scan, check and marker restoration. -/
theorem root_left_pattern_localRun (A : BinaryTree Unit) (z f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 5 + f.length)
      (cfg (some (phaseLabel (.seek .left))) regs
        { source := nodeTag :: (treeCode A ++ nodeTag :: z), saved := f } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ [nodeTag, nodeTag] ++ treeCode A ++ z } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := nodeTag :: z, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .left
      { base with source := nodeTag :: (treeCode A ++ nodeTag :: z) } regs ctx)
  have start := phase_step_localRun caller (
    start_left_step_node caller (treeCode A ++ nodeTag :: z) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .left A (nodeTag :: z) [] base
    (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have check := phase_step_localRun caller (
    checkRight_step_node caller z scanned (reset regs) ctx)
  have restore := restoreScratch_localRun caller .successLeft
    { scanned with source := z } (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan check restore
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller check restore)))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- Right-root scanning performs its first marker push before successful restoration starts. -/
theorem root_right_pattern_localRun (A : BinaryTree Unit) (z f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 4 + f.length)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := nodeTag :: nodeTag :: (treeCode A ++ z), saved := f } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ [nodeTag] ++ treeCode A ++ nodeTag :: z } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := nodeTag :: z, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .right
      { base with source := nodeTag :: nodeTag :: (treeCode A ++ z) } regs ctx)
  have start := phase_step_localRun caller (
    start_right_step_nodes caller (treeCode A ++ z) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .right A z [] base (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have restore := restoreScratch_localRun caller .successRight scanned (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan restore
  have joined := LocalRun.trans caller seek
    (LocalRun.trans caller start (LocalRun.trans caller scan restore))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- A source whose next pop cannot produce the required node marker. -/
def NoNodeHead : Word → Prop
  | [] => True
  | tag :: _ => tag ≠ nodeTag

/-- Failed first-node probes restore the complete literal input before returning. -/
theorem root_nonnode_localRun (d : RotationDirection) (w f : Word)
    (notNode : NoNodeHead w) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (f.length + 4)
      (cfg (some (phaseLabel (.seek d))) regs { source := w, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs) { source := f.reverse ++ w } ctx) := by
  let D : LocalData := { source := w, saved := f }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller d D regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start d))) (reset regs) D ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) D ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases d with
    | left =>
        cases w with
        | nil => simpa only [D, reset_reset] using start_left_step_nil caller D (reset regs) ctx
        | cons tag raw => simpa only [D, reset_reset] using
            start_left_step_nonnode caller tag raw D (reset regs) ctx notNode
    | right =>
        cases w with
        | nil => simpa only [D, reset_reset] using start_right_step_first_nil caller D (reset regs) ctx
        | cons tag raw => simpa only [D, reset_reset] using
            start_right_step_first_nonnode caller tag raw D (reset regs) ctx notNode
  have cleanup := dropPending_localRun caller D (reset regs) ctx
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start cleanup)
  convert joined using 1 <;> simp [D, dropPendingData]; omega

/-- A right-root failure after its second pop restores both popped observations. -/
theorem root_right_second_nonnode_localRun (w f : Word) (notNode : NoNodeHead w)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (f.length + 4)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := nodeTag :: w, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ nodeTag :: w } ctx) := by
  let D : LocalData := { source := nodeTag :: w, saved := f }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .right D regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start .right))) (reset regs) D ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) D ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases w with
    | nil => simpa only [D, reset_reset] using
        start_right_step_second_nil caller D (reset regs) ctx
    | cons tag raw => simpa only [D, reset_reset] using
        start_right_step_second_nonnode caller tag raw D (reset regs) ctx notNode
  have cleanup := dropPending_localRun caller D (reset regs) ctx
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start cleanup)
  convert joined using 1 <;> simp [D, dropPendingData]; omega

/-- A left-root scan may finish normally and then fail its required following-node check. -/
theorem root_left_after_nonnode_localRun (A : BinaryTree Unit) (w f : Word)
    (notNode : NoNodeHead w) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 6 + f.length)
      (cfg (some (phaseLabel (.seek .left))) regs
        { source := nodeTag :: (treeCode A ++ w), saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ nodeTag :: (treeCode A ++ w) } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := w, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .left
      { base with source := nodeTag :: (treeCode A ++ w) } regs ctx)
  have start := phase_step_localRun caller (
    start_left_step_node caller (treeCode A ++ w) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .left A w [] base (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have check : LocalRun caller 1
      (cfg (some (phaseLabel .checkRight)) (reset regs) scanned ctx)
      (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) scanned ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases w with
    | nil => simpa only [scanned, reset_reset] using checkRight_step_nil caller scanned (reset regs) ctx
    | cons tag raw => simpa only [scanned, reset_reset] using
        checkRight_step_nonnode caller tag raw scanned (reset regs) ctx notNode
  have cleanup := restoreScratch_localRun caller .failureLeft scanned (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan check cleanup
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller check cleanup)))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- Open one-slot scans that meet EOF or a foreign tag restore their complete raw root. -/
theorem root_blocked_localRun (d : RotationDirection) {accepted raw : Word} {p : Nat}
    (opened : TreeParserMachine.OpenPrefix accepted p) (blocked : TreeParserMachine.Blocked raw)
    (f : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + p + f.length + 6)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := markerWord (scratchFailure d) ++ accepted ++ raw, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ markerWord (scratchFailure d) ++ accepted ++ raw } ctx) := by
  let base : LocalData := { saved := f }
  have scan := scanScratch_blocked_localRun caller (continues_of_openPrefix opened) blocked
    d base (reset regs) ctx
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller d
      { base with source := markerWord (scratchFailure d) ++ accepted ++ raw } regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start d))) (reset regs)
        { base with source := markerWord (scratchFailure d) ++ accepted ++ raw } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { base with source := accepted ++ raw, pending := [()] } ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases d with
    | left => simpa [base, scratchFailure, markerWord] using
        start_left_step_node caller (accepted ++ raw) base (reset regs) ctx
    | right => simpa [base, scratchFailure, markerWord] using
        start_right_step_nodes caller (accepted ++ raw) base (reset regs) ctx
  simp only [base, List.length_nil, reset_reset, List.replicate_one] at scan
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start scan)
  convert joined using 1 <;> simp; omega

/-- The source observation chooses the first owned return label. -/
def sourceResult (value : Option (BinaryTree Unit)) : Result :=
  if value.isSome then .success else .failure

/-- The strengthened represented theorem retains arbitrary old saved data and literal suffix. -/
theorem run_code_localRun (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (representedClock d p s + f.length)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx) := by
  induction p generalizing s f z regs with
  | nil =>
      cases s with
      | nil =>
          have run := root_nonnode_localRun caller d (emptyTag :: z) f (by change emptyTag ≠ nodeTag; decide) regs ctx
          simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun, treeCode,
            Nat.add_comm] using run
      | node a l r =>
          cases a
          cases d with
          | left =>
              cases r with
              | nil =>
                  have run := root_left_after_nonnode_localRun caller l (emptyTag :: z) f
                    (by change emptyTag ≠ nodeTag; decide) regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
              | node b B C =>
                  cases b
                  have run := root_left_pattern_localRun caller l (treeCode B ++ treeCode C ++ z)
                    f regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
          | right =>
              cases l with
              | nil =>
                  have run := root_right_second_nonnode_localRun caller (emptyTag :: (treeCode r ++ z))
                    f (by change emptyTag ≠ nodeTag; decide) regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc, Nat.add_comm] using run
              | node a A B =>
                  cases a
                  have run := root_right_pattern_localRun caller A (treeCode B ++ treeCode r ++ z)
                    f regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
  | cons b p ih =>
      cases s with
      | nil =>
          let D : LocalData := { source := emptyTag :: z, saved := f, path := p }
          have head := phase_step_localRun caller (
            seek_step_source_nonnode caller d b p emptyTag z D regs ctx (by decide))
          have cleanup := dropPending_localRun caller D (reset regs) ctx
          have joined := LocalRun.trans caller head cleanup
          convert joined using 1 <;>
            simp [D, representedClock, remainingPath, sourceResult, source_nil_cons,
              treeCode, dropPendingData]; omega
      | node a l r =>
          cases a
          cases b with
          | left =>
              let D : LocalData := { saved := f }
              have head := phase_step_localRun caller (
                seek_step_node_left caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have tail := ih l (nodeTag :: f) (treeCode r ++ z) (reset regs)
              have joined := LocalRun.trans caller head tail
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 <;> convert joined using 1 <;>
                simp [D, representedClock, remainingPath, sourceResult, source_left, actual,
                  treeCode, List.reverse_cons, List.append_assoc] <;> omega
          | right =>
              let D : LocalData := { saved := f }
              let scanned : LocalData := { saved := nodeTag :: f, path := p }
              have head := phase_step_localRun caller (
                seek_step_node_right caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have scan := scanPrefix_treeCode_localRun caller d l (treeCode r ++ z) [] scanned
                (reset regs) ctx
              simp only [prefixScanEnd, ite_true, reset_reset] at scan
              have tail := ih r ((treeCode l).reverse ++ nodeTag :: f) z (reset regs)
              have joined := LocalRun.trans caller head (LocalRun.trans caller scan tail)
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 <;> convert joined using 1 <;>
                simp [D, representedClock, remainingPath, sourceResult, source_right,
                  actual, treeCode, List.reverse_cons, List.reverse_append, List.append_assoc] <;> omega

/-- An owned segment to a live result determines the evaluator's exact count and endpoint. -/
theorem LocalRun.phase_endpoint {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : Result}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  have count := LocalRun.remaining caller run
  change phaseSteps q D = n + 0 at count
  rw [Nat.add_zero] at count
  refine ⟨count, ?_⟩
  have canonical := phase_iterate caller q D regs ctx
  rw [count] at canonical
  exact Option.some.inj (canonical.symm.trans (LocalRun.iterate caller run))

/-- The represented result is the complete first endpoint chosen by the finite evaluator. -/
theorem phaseResult_code (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseSteps (.seek d) { source := treeCode s ++ z, saved := f, path := p } =
        representedClock d p s + f.length ∧
      phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
          { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
            path := remainingPath p s } ctx :=
  LocalRun.phase_endpoint caller (run_code_localRun caller d p s f z regs ctx)

/-- Exact ordinary iteration, retaining the old saved word, suffix and actual residual path. -/
theorem run_code (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx) :=
  LocalRun.iterate caller (run_code_localRun caller d p s f z regs ctx)

/-- A successful source move produces its actual rotated tree and consumes the whole path. -/
theorem run_code_of_some (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ treeCode t ++ z } ctx) := by
  simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
    remainingPath_nil_of_source_success d p s t returned] using
    run_code caller d p s f z regs ctx

/-- Failed source moves restore the original tree while retaining the physically unvisited path tail. -/
theorem run_code_of_none (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (failed : (applyMoveRun ⟨d, p⟩ s).1 = none) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ treeCode s ++ z, path := remainingPath p s } ctx) := by
  simpa only [failed, sourceResult, Option.isSome_none, Bool.false_eq_true, ite_false,
    Option.getD_none] using run_code caller d p s f z regs ctx

/-- Source success is equivalent to the first live result, before arbitrary caller code runs. -/
theorem represented_first_success_iff (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx).l =
        some (resultLabel .success) ↔ ∃ t, (applyMoveRun ⟨d, p⟩ s).1 = some t := by
  rw [(phaseResult_code caller d p s f z regs ctx).2]
  cases actual : (applyMoveRun ⟨d, p⟩ s).1 <;>
    simp [sourceResult, cfg, resultLabel]

/-- A Type-valued timed witness with its actual exact represented count and complete endpoint. -/
def representedInTime (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (some (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx))
      (representedClock d p s + f.length) where
  steps := representedClock d p s + f.length
  evals_in_steps := run_code caller d p s f z regs ctx
  steps_le_m := Nat.le_refl _

/-- A constructed failure segment excludes success at the canonical first live return. -/
theorem LocalRun.not_phaseSuccess {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel .failure)) outRegs E outCtx)) :
    (phaseResult (Λ := Λ) q regs D ctx).l ≠ some (resultLabel .success) := by
  rw [(LocalRun.phase_endpoint caller run).2]
  intro impossible
  cases impossible

/-- Literal left-root recognition; the suffix is arbitrary and need not be tree syntax. -/
theorem root_left_phaseResult_success_iff (caller : External Λ → Statement Γ Λ R) (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek .left) regs { source := w, saved := f } ctx).l =
        some (resultLabel .success) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: (treeCode A ++ nodeTag :: z) := by
  constructor
  · intro success
    cases w with
    | nil =>
        have blocked := LocalRun.not_phaseSuccess caller
          (root_nonnode_localRun caller .left [] f True.intro regs ctx)
        exact (blocked success).elim
    | cons tag raw =>
        by_cases node : tag = nodeTag
        · subst tag
          cases parsed : (parseTreeRun raw).1 with
          | none =>
              obtain ⟨accepted, rest, p, word, opened, stopped⟩ :=
                (TreeParserMachine.parseTreeRun_none_iff_openPrefix raw).mp parsed
              have blocked := LocalRun.not_phaseSuccess caller
                (root_blocked_localRun caller .left opened stopped f regs ctx)
              apply False.elim (blocked ?_)
              simpa [scratchFailure, markerWord, word, List.append_assoc] using success
          | some result =>
              rcases result with ⟨A, rest⟩
              have word := (parseTreeRun_iff raw A rest).mp parsed
              cases rest with
              | nil =>
                  have blocked := LocalRun.not_phaseSuccess caller
                    (root_left_after_nonnode_localRun caller A [] f True.intro regs ctx)
                  apply False.elim (blocked ?_)
                  simpa only [word] using success
              | cons required z =>
                  by_cases node : required = nodeTag
                  · exact ⟨A, z, by simp only [word, node]⟩
                  · have blocked := LocalRun.not_phaseSuccess caller
                      (root_left_after_nonnode_localRun caller A (required :: z) f node regs ctx)
                    apply False.elim (blocked ?_)
                    simpa only [word] using success
        · have blocked := LocalRun.not_phaseSuccess caller
            (root_nonnode_localRun caller .left (tag :: raw) f node regs ctx)
          exact (blocked success).elim
  · rintro ⟨A, z, rfl⟩
    rw [(LocalRun.phase_endpoint caller (root_left_pattern_localRun caller A z f regs ctx)).2]
    rfl

/-- Literal right-root recognition includes the scanner's final in-block marker insertion. -/
theorem root_right_phaseResult_success_iff (caller : External Λ → Statement Γ Λ R) (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek .right) regs { source := w, saved := f } ctx).l =
        some (resultLabel .success) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: nodeTag :: (treeCode A ++ z) := by
  constructor
  · intro success
    cases w with
    | nil =>
        have blocked := LocalRun.not_phaseSuccess caller
          (root_nonnode_localRun caller .right [] f True.intro regs ctx)
        exact (blocked success).elim
    | cons first raw =>
        by_cases node : first = nodeTag
        · subst first
          cases raw with
          | nil =>
              have blocked := LocalRun.not_phaseSuccess caller
                (root_right_second_nonnode_localRun caller [] f True.intro regs ctx)
              exact (blocked success).elim
          | cons second raw =>
              by_cases node : second = nodeTag
              · subst second
                cases parsed : (parseTreeRun raw).1 with
                | none =>
                    obtain ⟨accepted, rest, p, word, opened, stopped⟩ :=
                      (TreeParserMachine.parseTreeRun_none_iff_openPrefix raw).mp parsed
                    have blocked := LocalRun.not_phaseSuccess caller
                      (root_blocked_localRun caller .right opened stopped f regs ctx)
                    apply False.elim (blocked ?_)
                    simpa [scratchFailure, markerWord, word, List.append_assoc] using success
                | some result =>
                    rcases result with ⟨A, z⟩
                    exact ⟨A, z, by rw [(parseTreeRun_iff raw A z).mp parsed]⟩
              · have blocked := LocalRun.not_phaseSuccess caller
                  (root_right_second_nonnode_localRun caller (second :: raw) f node regs ctx)
                exact (blocked success).elim
        · have blocked := LocalRun.not_phaseSuccess caller
            (root_nonnode_localRun caller .right (first :: raw) f node regs ctx)
          exact (blocked success).elim
  · rintro ⟨A, z, rfl⟩
    rw [(LocalRun.phase_endpoint caller (root_right_pattern_localRun caller A z f regs ctx)).2]
    rfl

/-- All strict earlier steps are owned: LocalRun cannot continue through an external caller. -/
theorem firstSuccess_iff_phaseResult (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx) reached ∧
      reached.l = some (resultLabel .success)) ↔
        (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel .success) := by
  constructor
  · rintro ⟨n, reached, run, label⟩
    have count := LocalRun.remaining caller run
    have terminal : remainingSteps reached = 0 := by
      simp only [remainingSteps, label, resultLabel]
    change phaseSteps q D = n + remainingSteps reached at count
    rw [terminal, Nat.add_zero] at count
    have canonical := phase_iterate caller q D regs ctx
    rw [count] at canonical
    have same := Option.some.inj (canonical.symm.trans (LocalRun.iterate caller run))
    rw [same]
    exact label
  · intro label
    exact ⟨phaseSteps q D, phaseResult (Λ := Λ) q regs D ctx, phase_localRun caller q D regs ctx, label⟩

/-- Exact left raw-root success iff, expressed through actual owned transitions. -/
theorem root_left_first_success_iff (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n
      (cfg (some (phaseLabel (.seek .left))) regs { source := w, saved := f } ctx) reached ∧
        reached.l = some (resultLabel .success)) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: (treeCode A ++ nodeTag :: z) := by
  rw [firstSuccess_iff_phaseResult caller, root_left_phaseResult_success_iff caller]

/-- Exact right raw-root success iff; no whole-input parser premise is imposed. -/
theorem root_right_first_success_iff (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n
      (cfg (some (phaseLabel (.seek .right))) regs { source := w, saved := f } ctx) reached ∧
        reached.l = some (resultLabel .success)) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: nodeTag :: (treeCode A ++ z) := by
  rw [firstSuccess_iff_phaseResult caller, root_right_phaseResult_success_iff caller]

/-- Actual successful navigation frames, ordered from the focused subtree outwards. -/
def navigationFrames : List Branch → BinaryTree Unit → List PositionFrame
  | [], _ => []
  | _ :: _, .nil => []
  | .left :: p, .node _ l r => navigationFrames p l ++ [.cameLeft r]
  | .right :: p, .node _ l r => navigationFrames p r ++ [.cameRight l]

omit [DecidableEq K] in
theorem plugFrames_append (inner outer : List PositionFrame) (focus : BinaryTree Unit) :
    plugFrames (inner ++ outer) focus = plugFrames outer (plugFrames inner focus) := by
  induction inner generalizing focus with
  | nil => rfl
  | cons frame inner ih => cases frame <;> exact ih _

omit [DecidableEq K] in
theorem contextPrefix_append (inner outer : List PositionFrame) :
    contextPrefix (inner ++ outer) = contextPrefix outer ++ contextPrefix inner := by
  induction inner with
  | nil => simp only [List.nil_append, contextPrefix, List.append_nil]
  | cons frame inner ih => cases frame <;>
      simp only [List.cons_append, contextPrefix, ih, List.append_assoc]

omit [DecidableEq K] in
theorem contextSuffix_append (inner outer : List PositionFrame) :
    contextSuffix (inner ++ outer) = contextSuffix inner ++ contextSuffix outer := by
  induction inner with
  | nil => rfl
  | cons frame inner ih => cases frame <;>
      simp only [List.cons_append, contextSuffix, ih, List.append_assoc]

omit [DecidableEq K] in
theorem navigationFrames_plug (p : List Branch) (s : BinaryTree Unit) :
    plugFrames (navigationFrames p s) (stoppedTree p s) = s := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r =>
          cases a
          cases b with
          | left => simp only [navigationFrames, stoppedTree, plugFrames_append, ih, plugFrames]
          | right => simp only [navigationFrames, stoppedTree, plugFrames_append, ih, plugFrames]

omit [DecidableEq K] in
theorem treeCode_cursor (p : List Branch) (s : BinaryTree Unit) :
    treeCode s = contextPrefix (navigationFrames p s) ++ treeCode (stoppedTree p s) ++
      contextSuffix (navigationFrames p s) := by
  have encoded := treeCode_plugFrames (navigationFrames p s) (stoppedTree p s)
  rw [navigationFrames_plug] at encoded
  exact encoded

omit [DecidableEq K] in
theorem navigationLength_eq_prefix (p : List Branch) (s : BinaryTree Unit) :
    navigationLength p s = (contextPrefix (navigationFrames p s)).length := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r =>
          cases b with
          | left => simp only [navigationLength, navigationFrames, contextPrefix_append,
              contextPrefix, List.nil_append, List.length_append, List.length_singleton, ih]
          | right => simp only [navigationLength, navigationFrames, contextPrefix_append,
              contextPrefix, List.nil_append, List.length_append, List.length_singleton, ih]

omit [DecidableEq K] in
@[simp] theorem afterScanRegisters_reset (accepted : Word) (regs : Registers R) :
    afterScanRegisters accepted (reset regs) = reset regs := by
  cases accepted <;> rfl

/-- The physical cursor before the final observation has moved exactly the context prefix. -/
theorem seek_cursor_localRun (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (navigationLength p s)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (phaseLabel (.seek d)))
        (afterScanRegisters (contextPrefix (navigationFrames p s)) regs)
        { source := treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z,
          saved := (contextPrefix (navigationFrames p s)).reverse ++ f,
          path := stoppedPath p s } ctx) := by
  induction p generalizing s f z regs with
  | nil =>
      simpa only [navigationLength, navigationFrames, stoppedTree, stoppedPath,
        contextPrefix, contextSuffix, afterScanRegisters, ite_true, List.reverse_nil,
        List.nil_append, List.append_nil] using
        LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.seek d))) regs { source := treeCode s ++ z, saved := f } ctx)
  | cons b p ih =>
      cases s with
      | nil =>
          simpa only [navigationLength, navigationFrames, stoppedTree, stoppedPath,
            contextPrefix, contextSuffix, afterScanRegisters, ite_true, List.reverse_nil,
            List.nil_append, List.append_nil] using
            LocalRun.refl (caller := caller)
              (cfg (some (phaseLabel (.seek d))) regs
                { source := treeCode .nil ++ z, saved := f, path := b :: p } ctx)
      | node a l r =>
          cases a
          cases b with
          | left =>
              let D : LocalData := { saved := f }
              have head := phase_step_localRun caller
                (seek_step_node_left caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have tail := ih l (nodeTag :: f) (treeCode r ++ z) (reset regs)
              simp only [afterScanRegisters_reset] at tail
              have joined := LocalRun.trans caller head tail
              simpa only [D, navigationLength, navigationFrames, stoppedTree, stoppedPath,
                treeCode, contextPrefix_append, contextSuffix_append, contextPrefix, contextSuffix,
                List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
                List.reverse_cons, List.reverse_append, List.reverse_nil,
                afterScanRegisters, List.cons_ne_nil, ite_false] using joined
          | right =>
              let D : LocalData := { saved := f }
              let scanned : LocalData := { saved := nodeTag :: f, path := p }
              have head := phase_step_localRun caller
                (seek_step_node_right caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have scan := scanPrefix_treeCode_localRun caller d l (treeCode r ++ z) [] scanned
                (reset regs) ctx
              simp only [prefixScanEnd, ite_true, reset_reset] at scan
              have tail := ih r ((treeCode l).reverse ++ nodeTag :: f) z (reset regs)
              simp only [afterScanRegisters_reset] at tail
              have joined := LocalRun.trans caller head (LocalRun.trans caller scan tail)
              simpa only [D, scanned, navigationLength, navigationFrames, stoppedTree, stoppedPath,
                treeCode, contextPrefix_append, contextSuffix_append, contextPrefix, contextSuffix,
                List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
                List.reverse_cons, List.reverse_append, List.reverse_nil, List.reverse_reverse,
                afterScanRegisters, List.cons_ne_nil, ite_false,
                Nat.add_assoc] using joined

/-- Ordinary iteration to the actual cursor retains a failing head until its next activation. -/
theorem seek_cursor_iterate (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[navigationLength p s]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (phaseLabel (.seek d)))
        (afterScanRegisters (contextPrefix (navigationFrames p s)) regs)
        { source := treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z,
          saved := (contextPrefix (navigationFrames p s)).reverse ++ f,
          path := stoppedPath p s } ctx) :=
  LocalRun.iterate caller (seek_cursor_localRun caller d p s f z regs ctx)

/-- Ordinary iteration for every continued prefix of the saved-word scan. -/
theorem scanPrefix_continues {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          saved := accepted.reverse ++ D.saved,
          pending := List.replicate k () } ctx) :=
  LocalRun.iterate caller (scanPrefix_continues_localRun caller continued d raw D regs ctx)

/-- Ordinary iteration for every continued prefix of the scratch scan. -/
theorem scanScratch_continues {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          scratch := accepted.reverse ++ D.scratch,
          pending := List.replicate k () } ctx) :=
  LocalRun.iterate caller (scanScratch_continues_localRun caller continued d raw D regs ctx)

/-- A represented prefix scan with its complete ordinary-iteration endpoint. -/
theorem scanPrefix_treeCode (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[(treeCode t).length]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)) =
      some (cfg (some (phaseLabel (prefixScanEnd d outer))) (reset regs)
        { D with
          source := raw,
          saved := (treeCode t).reverse ++ D.saved,
          pending := outer } ctx) :=
  LocalRun.iterate caller (scanPrefix_treeCode_localRun caller d t raw outer D regs ctx)

/-- A represented scratch scan includes the right mode's final same-activation push. -/
theorem scanScratch_treeCode (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[(treeCode t).length]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)) =
      some (cfg (some (phaseLabel (scratchScanEnd d outer))) (reset regs)
        { D with
          source := scratchScanSource d outer raw,
          scratch := (treeCode t).reverse ++ D.scratch,
          pending := outer } ctx) :=
  LocalRun.iterate caller (scanScratch_treeCode_localRun caller d t raw outer D regs ctx)

/-- Saved-scan blocked cleanup, with its exact paid probes and dirty scratch retained. -/
theorem scanPrefix_blocked {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + k + D.saved.length + 3]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { D with
          source := D.saved.reverse ++ accepted ++ raw,
          saved := [], pending := [] } ctx) :=
  LocalRun.iterate caller (scanPrefix_blocked_localRun caller continued blocked d D regs ctx)

/-- Scratch-scan blocked cleanup restores every old accumulator and required missing marker. -/
theorem scanScratch_blocked {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + k + D.scratch.length + D.saved.length + 4]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { source := D.saved.reverse ++ markerWord (scratchFailure d) ++
            D.scratch.reverse ++ accepted ++ raw,
          saved := [], scratch := [], pending := [], path := D.path } ctx) :=
  LocalRun.iterate caller (scanScratch_blocked_localRun caller continued blocked d D regs ctx)

/-- Complete first-success endpoints identify both tree and suffix after cancelling old saved data. -/
theorem phaseResult_code_success_iff (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (f z outSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel .success)) (reset regs)
          { source := f.reverse ++ treeCode t ++ outSuffix } ctx ↔
      (applyMoveRun ⟨d, p⟩ s).1 = some t ∧ z = outSuffix := by
  constructor
  · intro endpoint
    have canonical := (phaseResult_code caller d p s f z regs ctx).2
    have same := canonical.symm.trans endpoint
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) same
    cases actual : (applyMoveRun ⟨d, p⟩ s).1 with
    | none => simp [actual, sourceResult, cfg, resultLabel] at label
    | some u =>
        have source := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).source) same
        have prefixed : f.reverse ++ (treeCode u ++ z) =
            f.reverse ++ (treeCode t ++ outSuffix) := by
          simpa only [dataOfCfg_cfg, actual, Option.getD_some, List.append_assoc] using source
        have codes : treeCode u ++ z = treeCode t ++ outSuffix :=
          List.append_cancel_left prefixed
        obtain ⟨tree, suffix⟩ := parseTreeRun_prefix_injective u t z outSuffix codes
        exact ⟨congrArg some tree, suffix⟩
  · rintro ⟨returned, rfl⟩
    simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
      remainingPath_nil_of_source_success d p s t returned] using
      (phaseResult_code caller d p s f z regs ctx).2

/-- An actual owned successful segment fixes the source result, raw suffix and exact duration. -/
theorem run_code_success_iff (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (f z outSuffix : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ treeCode t ++ outSuffix } ctx) ↔
      (applyMoveRun ⟨d, p⟩ s).1 = some t ∧ z = outSuffix ∧
        n = representedClock d p s + f.length := by
  constructor
  · intro run
    have endpoint := LocalRun.phase_endpoint caller run
    have decoded := (phaseResult_code_success_iff caller d p s t f z outSuffix regs ctx).mp endpoint.2
    exact ⟨decoded.1, decoded.2,
      endpoint.1.symm.trans (phaseResult_code caller d p s f z regs ctx).1⟩
  · rintro ⟨returned, rfl, rfl⟩
    simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
      remainingPath_nil_of_source_success d p s t returned] using
      run_code_localRun caller d p s f z regs ctx

/-- The actual source semantics, node preservation and tariff follow from the complete first endpoint. -/
theorem represented_success_semantics (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (endpoint : phaseResult (Λ := Λ) (.seek d) regs
      { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel .success)) (reset regs)
          { source := f.reverse ++ treeCode t ++ z } ctx) :
    Trees.Rotations.applyMove? ⟨d, p⟩ s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun ⟨d, p⟩ s).2 = 3 * p.length + 5 ∧
      (f.reverse ++ treeCode t ++ z).length = f.length + 2 * s.numNodes + 1 + z.length := by
  have returned := ((phaseResult_code_success_iff caller d p s t f z z regs ctx).mp endpoint).1
  have nodes := applyMoveRun_numNodes ⟨d, p⟩ s t returned
  refine ⟨(applyMoveRun_value ⟨d, p⟩ s).symm.trans returned, nodes,
    applyMoveRun_cost_of_some ⟨d, p⟩ s t returned, ?_⟩
  simp only [List.length_append, List.length_reverse, treeCode_length, nodes, Nat.add_assoc]

/-- Failure restoration and successful rotation have the same represented output length. -/
theorem represented_output_length (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (dataOfCfg (phaseResult (Λ := Λ) (.seek d) regs
      { source := treeCode s ++ z, saved := f, path := p } ctx)).source.length =
        f.length + 2 * s.numNodes + 1 + z.length := by
  rw [(phaseResult_code caller d p s f z regs ctx).2]
  change (f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z).length = _
  cases actual : (applyMoveRun ⟨d, p⟩ s).1 with
  | none => simp only [Option.getD_none, List.length_append, List.length_reverse,
      treeCode_length, Nat.add_assoc]
  | some t => simp only [Option.getD_some, List.length_append, List.length_reverse,
      treeCode_length, applyMoveRun_numNodes ⟨d, p⟩ s t actual, Nat.add_assoc]

omit [DecidableEq K] in
/-- Success descends through the entire installed position; its source tariff is independently fixed. -/
theorem descentCount_eq_length_of_source_success (d : RotationDirection) (p : List Branch)
    (s t : BinaryTree Unit) (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) :
    descentCount p s = p.length := by
  have measured := source_cost_eq_stopped d p s
  rw [returned] at measured
  simp only [Option.isSome_some, ite_true] at measured
  have cost := applyMoveRun_cost_of_some ⟨d, p⟩ s t returned
  change (applyMoveRun ⟨d, p⟩ s).2 = 3 * p.length + 5 at cost
  omega


def localTagCells (D : LocalData) : Nat := D.source.length + D.saved.length + D.scratch.length
def localCells (D : LocalData) : Nat :=
  D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length

def phaseDebt : Phase → Nat
  | .scanScratch .left | .checkRight | .restoreScratch .successRight | .restoreScratch .failureLeft => 1
  | .scanScratch .right | .restoreScratch .successLeft | .restoreScratch .failureRight => 2
  | _ => 0

def controlDebt : Control → Nat
  | .inl q => phaseDebt q
  | .inr _ => 0

def phaseCredit : Phase → LocalData → Nat
  | .seek _, D | .scanPrefix _, D | .start _, D | .scanScratch _, D | .checkRight, D => D.source.length
  | _, _ => 0

def controlCredit : Control → LocalData → Nat
  | .inl q, D => phaseCredit q D
  | .inr _, _ => 0

def localPotential (control : Control) (D : LocalData) : Nat :=
  localCells D + controlDebt control + controlCredit control D

theorem advance_mass (q : Phase) (D : LocalData) :
    localTagCells (advance q D).2 + controlDebt (advance q D).1 = localTagCells D + phaseDebt q ∧
      localPotential (advance q D).1 (advance q D).2 ≤ localPotential (.inl q) D := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons b path =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node]; omega
  | scanPrefix d =>
      cases raw with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished,
                  List.length_tail] <;> omega
            · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                controlDebt, phaseDebt, controlCredit, phaseCredit, node, empty]
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons tag raw =>
              by_cases node : tag = nodeTag <;> constructor <;>
                simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
      | right =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons first raw =>
              cases raw with
              | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit]
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;> constructor <;>
                    simp [advance, localTagCells, localPotential, localCells,
                      controlDebt, phaseDebt, controlCredit, phaseCredit, nodes] <;> omega
  | scanScratch d =>
      cases raw with
      | nil => cases d <;> constructor <;>
          simp [advance, localTagCells, localPotential, localCells,
            controlDebt, phaseDebt, controlCredit, phaseCredit, scratchFailure]
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished,
                  List.length_tail] <;> omega
            · cases d <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                controlDebt, phaseDebt, controlCredit, phaseCredit, node, empty, scratchFailure]
  | checkRight =>
      cases raw with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons tag raw =>
          by_cases node : tag = nodeTag <;> constructor <;>
            simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
  | restoreScratch mode =>
      cases scratch <;> cases mode <;> constructor <;>
        simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit, markerWord, modeResult] <;> omega
  | dropPending => cases pending <;> constructor <;>
      simp [advance, localTagCells, localPotential, localCells,
        controlDebt, phaseDebt, controlCredit, phaseCredit]
  | restorePrefix r => cases saved <;> constructor <;>
      simp [advance, localTagCells, localPotential, localCells,
        controlDebt, phaseDebt, controlCredit, phaseCredit] <;> omega

def tagCells (c : Cfg Γ Λ R) : Nat := localTagCells (dataOfCfg c)
def ownedCells (c : Cfg Γ Λ R) : Nat := localCells (dataOfCfg c)

def debt : Option (Label Λ) → Nat
  | some (.inl q) => phaseDebt q
  | _ => 0

def credit (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseCredit q (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
@[simp] theorem tagCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : tagCells (cfg label regs D ctx) = localTagCells D := rfl

@[simp] theorem debt_controlLabel (control : Control) :
    debt (some (controlLabel (Λ := Λ) control)) = controlDebt control := by
  cases control <;> rfl

omit [DecidableEq K] in
@[simp] theorem credit_control_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    credit (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) = controlCredit control D := by
  cases control <;> rfl

theorem local_step_tag_debt {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    tagCells after + debt after.l = tagCells before + debt before.l := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  change localTagCells (advance q D).2 + debt (some (controlLabel (Λ := Λ) (advance q D).1)) =
    localTagCells D + phaseDebt q
  rw [debt_controlLabel]
  exact (advance_mass q D).1

theorem local_reaches_tag_debt {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    tagCells reached + debt reached.l = tagCells start + debt start.l := by
  induction path with
  | refl => rfl
  | @tail before after _ transition ih => exact (local_step_tag_debt caller transition).trans ih


end Resources.RotationCertificate.PositionedRotationMachine

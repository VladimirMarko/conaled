import Applications.Resources.RotationCertificate.LinearParser

/-!
# Structural stack parsing of preorder tree prefixes

The input loop recurses only on the actual word tail. Resumption recurses only
on the pending frames and constructs each parent from the actual returned
children. One entry, new stack cons, new tree node, or returned Option costs
one; frames and done/next controls are free packaging. Mathematical prefixes,
lengths and node counts occur only in proofs. These are source-event costs,
not allocation, bit complexity or machine time.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate

inductive TreeFrame where
  | needLeft
  | needRight (left : BinaryTree Unit)

inductive TreeResume where
  | done (tree : BinaryTree Unit)
  | next (frames : List TreeFrame)

/-- Resume with the actual completed child; a right child closes its parent. -/
def resumeTreeRun : List TreeFrame → BinaryTree Unit → Measured TreeResume Nat
  | [], t => (.done t, 1)
  | .needLeft :: outer, t => (.next (.needRight t :: outer), 2)
  | .needRight l :: outer, t =>
      bind ((BinaryTree.node () l t), 2) (resumeTreeRun outer)

/-- Pending preorder material, used only as an independent mathematical invariant. -/
def stackPrefix : List TreeFrame → Word
  | [] => []
  | .needLeft :: outer => stackPrefix outer ++ [nodeTag]
  | .needRight l :: outer => stackPrefix outer ++ [nodeTag] ++ treeCode l

theorem resumeTreeRun_prefix (frames : List TreeFrame) (t : BinaryTree Unit) :
    match (resumeTreeRun frames t).1 with
    | .done u => stackPrefix frames ++ treeCode t = treeCode u
    | .next next => stackPrefix frames ++ treeCode t = stackPrefix next := by
  induction frames generalizing t with
  | nil => rfl
  | cons frame outer ih =>
      cases frame with
      | needLeft => simp only [resumeTreeRun, stackPrefix, List.append_assoc]
      | needRight l =>
          simpa only [resumeTreeRun, bind, stackPrefix, treeCode,
            List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
            using ih (.node () l t)

/-- The potential is twice the number of pending frames. -/
theorem resumeTreeRun_cost (frames : List TreeFrame) (t : BinaryTree Unit) :
    match (resumeTreeRun frames t).1 with
    | .done _ => (resumeTreeRun frames t).2 ≤ 2 * frames.length + 1
    | .next next =>
        (resumeTreeRun frames t).2 + 2 * next.length ≤ 2 * frames.length + 2 := by
  induction frames generalizing t with
  | nil => change 1 ≤ 1; exact le_rfl
  | cons frame outer ih =>
      cases frame with
      | needLeft => simp only [resumeTreeRun, List.length_cons]; omega
      | needRight l =>
          have bound := ih (.node () l t)
          simp only [resumeTreeRun, bind, List.length_cons]
          cases result : (resumeTreeRun outer (.node () l t)).1 with
          | done u => simp only [result] at bound; omega
          | next next => simp only [result] at bound; omega

def parseTreeLoop : Word → List TreeFrame → Measured (Option (BinaryTree Unit × Word)) Nat
  | [], _ => (none, 2)
  | tag :: raw, frames =>
      if tag = nodeTag then
        let next := parseTreeLoop raw (.needLeft :: frames)
        (next.1, 2 + next.2)
      else if tag = emptyTag then
        let next := bind (resumeTreeRun frames .nil) (fun result => match result with
          | .done t => (some (t, raw), 1)
          | .next nextFrames => parseTreeLoop raw nextFrames)
        (next.1, 1 + next.2)
      else (none, 2)

/-- Proof-facing name for the existing resumption/continuation expression.
It is not an additional charged parser state. -/
private def finishTreeRun (frames : List TreeFrame) (t : BinaryTree Unit) (rest : Word) :
    Measured (Option (BinaryTree Unit × Word)) Nat :=
  bind (resumeTreeRun frames t) (fun result => match result with
    | .done u => (some (u, rest), 1)
    | .next next => parseTreeLoop rest next)

@[simp] theorem parseTreeLoop_nil (frames : List TreeFrame) :
    parseTreeLoop [] frames = (none, 2) := rfl

theorem parseTreeLoop_node (raw : Word) (frames : List TreeFrame) :
    parseTreeLoop (nodeTag :: raw) frames =
      let next := parseTreeLoop raw (.needLeft :: frames)
      (next.1, 2 + next.2) := by rw [parseTreeLoop, ite_eq_left rfl]

private theorem parseTreeLoop_empty (raw : Word) (frames : List TreeFrame) :
    parseTreeLoop (emptyTag :: raw) frames =
      let next := finishTreeRun frames .nil raw
      (next.1, 1 + next.2) := rfl

theorem parseTreeLoop_foreign (tag : Tag) (raw : Word) (frames : List TreeFrame)
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    parseTreeLoop (tag :: raw) frames = (none, 2) := by
  simp only [parseTreeLoop, ite_eq_right notNode, ite_eq_right notEmpty]

private theorem finishTreeRun_needLeft (outer : List TreeFrame) (t : BinaryTree Unit)
    (rest : Word) :
    finishTreeRun (.needLeft :: outer) t rest =
      let next := parseTreeLoop rest (.needRight t :: outer)
      (next.1, 2 + next.2) := rfl

private theorem finishTreeRun_needRight (outer : List TreeFrame) (l t : BinaryTree Unit)
    (rest : Word) :
    finishTreeRun (.needRight l :: outer) t rest =
      let next := finishTreeRun outer (.node () l t) rest
      (next.1, 2 + next.2) := by
  simp only [finishTreeRun, resumeTreeRun, bind, Nat.add_assoc]

/-- Consume a tree under arbitrary pending frames, retaining even a failed continuation. -/
private theorem parseTreeLoop_code (t : BinaryTree Unit) (rest : Word)
    (frames : List TreeFrame) :
    parseTreeLoop (treeCode t ++ rest) frames =
      let next := finishTreeRun frames t rest
      (next.1, (7 * t.numNodes + 1) + next.2) := by
  induction t generalizing frames rest with
  | nil => exact parseTreeLoop_empty rest frames
  | node a l r ihl ihr =>
      cases a
      simp only [treeCode, List.cons_append, List.append_assoc, parseTreeLoop_node]
      rw [ihl, finishTreeRun_needLeft, ihr, finishTreeRun_needRight]
      apply Prod.ext
      · rfl
      · dsimp only [Prod.snd, BinaryTree.numNodes]
        change 2 + (7 * l.numNodes + 1 + (2 + (7 * r.numNodes + 1 +
          (2 + (finishTreeRun frames (.node () l r) rest).2)))) =
          7 * (l.numNodes + r.numNodes + 1) + 1 +
            (finishTreeRun frames (.node () l r) rest).2
        omega

private theorem parseTreeLoop_sound (raw : Word) (frames : List TreeFrame)
    (t : BinaryTree Unit) (rest : Word)
    (returned : (parseTreeLoop raw frames).1 = some (t, rest)) :
    stackPrefix frames ++ raw = treeCode t ++ rest := by
  induction raw generalizing frames with
  | nil => cases returned
  | cons tag raw ih =>
      by_cases node : tag = nodeTag
      · subst tag
        rw [parseTreeLoop_node] at returned
        have consumed := ih (.needLeft :: frames) returned
        simpa only [stackPrefix, List.append_assoc, List.singleton_append] using consumed
      · by_cases empty : tag = emptyTag
        · subst tag
          rw [parseTreeLoop_empty] at returned
          simp only [finishTreeRun, bind] at returned
          have prefixEq := resumeTreeRun_prefix frames .nil
          cases resumed : (resumeTreeRun frames .nil).1 with
          | done u =>
              simp only [resumed, Option.some.injEq, Prod.mk.injEq] at returned
              rcases returned with ⟨rfl, rfl⟩
              simp only [resumed] at prefixEq
              simpa only [treeCode, List.append_assoc, List.singleton_append] using
                congrArg (fun word => word ++ raw) prefixEq
          | next next =>
              simp only [resumed] at returned prefixEq
              have consumed := ih next returned
              rw [← prefixEq] at consumed
              simpa only [treeCode, List.append_assoc, List.singleton_append] using consumed
        · rw [parseTreeLoop_foreign tag raw frames node empty] at returned
          cases returned

theorem parseTreeLoop_cost_le (raw : Word) (frames : List TreeFrame) :
    (parseTreeLoop raw frames).2 ≤ 5 * raw.length + 2 * frames.length + 2 := by
  induction raw generalizing frames with
  | nil => simp only [parseTreeLoop_nil, List.length_nil]; omega
  | cons tag raw ih =>
      by_cases node : tag = nodeTag
      · subst tag
        rw [parseTreeLoop_node]
        have bound := ih (.needLeft :: frames)
        simp only [List.length_cons] at bound ⊢
        omega
      · by_cases empty : tag = emptyTag
        · subst tag
          rw [parseTreeLoop_empty]
          simp only [finishTreeRun, bind, List.length_cons]
          have bound := resumeTreeRun_cost frames .nil
          cases resumed : (resumeTreeRun frames .nil).1 with
          | done u => simp only [resumed] at bound; dsimp; omega
          | next next =>
              simp only [resumed] at bound
              have tailBound := ih next
              dsimp
              omega
        · rw [parseTreeLoop_foreign tag raw frames node empty]
          dsimp
          omega

def parseTreeRun (raw : Word) : Measured (Option (BinaryTree Unit × Word)) Nat :=
  parseTreeLoop raw []

theorem parseTreeRun_code (t : BinaryTree Unit) (rest : Word) :
    parseTreeRun (treeCode t ++ rest) = (some (t, rest), 7 * t.numNodes + 3) := by
  rw [parseTreeRun, parseTreeLoop_code]
  simp only [finishTreeRun, resumeTreeRun, bind]

/-- Exact recognition of every raw prefix with its untouched suffix. -/
theorem parseTreeRun_iff (raw : Word) (t : BinaryTree Unit) (rest : Word) :
    (parseTreeRun raw).1 = some (t, rest) ↔ raw = treeCode t ++ rest := by
  constructor
  · intro returned
    exact parseTreeLoop_sound raw [] t rest returned
  · intro encoded
    subst raw
    exact congrArg Prod.fst (parseTreeRun_code t rest)

theorem parseTreeRun_cost_of_some (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (returned : (parseTreeRun raw).1 = some (t, rest)) :
    (parseTreeRun raw).2 = 7 * t.numNodes + 3 := by
  rw [(parseTreeRun_iff raw t rest).1 returned, parseTreeRun_code]

theorem parseTreeRun_cost_le (raw : Word) :
    (parseTreeRun raw).2 ≤ 5 * raw.length + 2 := by
  simpa only [parseTreeRun, List.length_nil, Nat.mul_zero, Nat.add_zero] using
    parseTreeLoop_cost_le raw []

theorem parseTreeRun_consumed_length (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (returned : (parseTreeRun raw).1 = some (t, rest)) :
    raw.length = 2 * t.numNodes + 1 + rest.length := by
  rw [(parseTreeRun_iff raw t rest).1 returned, List.length_append, treeCode_length]

theorem parseTreeRun_rest_length_lt (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (returned : (parseTreeRun raw).1 = some (t, rest)) : rest.length < raw.length := by
  have consumed := parseTreeRun_consumed_length raw t rest returned
  omega

theorem parseTreeRun_prefix_injective (s t : BinaryTree Unit) (rest suffix : Word)
    (encoded : treeCode s ++ rest = treeCode t ++ suffix) : s = t ∧ rest = suffix := by
  have observed := congrArg (fun raw => (parseTreeRun raw).1) encoded
  simpa only [parseTreeRun_code, Option.some.injEq, Prod.mk.injEq] using observed

theorem parseTreeRun_emit (t : BinaryTree Unit) (rest : Word) :
    parseTreeRun (emitTreeRun t rest).1 = (some (t, rest), 7 * t.numNodes + 3) := by
  rw [emitTreeRun_value, parseTreeRun_code]

end Resources.RotationCertificate

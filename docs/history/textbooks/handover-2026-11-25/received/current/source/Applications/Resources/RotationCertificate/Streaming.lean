import Applications.Resources.RotationCertificate.LinearParser

/-!
# Actual streaming rotation-certificate verification

Each stream activation charges one entry. EOF invokes the actual structural
tree comparison. A nonempty word first executes the fixed-width predecessor,
then the actual move parser, then the actual positioned rotation, and recurses
on their returned bits, tree and suffix. A newly returned false costs one.
Failure stops before any later stage or suffix is inspected.

The parser pair is matched with its equality so that the already proved strict
suffix decrease can justify recursion. Its actual observation is added to the
continuation observation. The termination measure and its proof are erased;
lengths and decoded natural fuel do not occur in the executed body.
These are explicit source-event observations, not machine-time or NP claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Trees.Rotations (RotationMove applyMove? applyMoves?)
open Resources.BinaryCounter (Bits value decFixedRun decFixedRun_none_iff
  decFixedRun_some_value decFixedRun_some_length decFixedRun_some_spec
  decFixedRun_exists_of_pos decFixedRun_cost_le decFixedRun_replicate_false)

/-- Execute one actual move at a time, with binary-fuel failure before parsing. -/
def checkStreamRun (bs : Bits) (s t : BinaryTree Unit) (cert : Word) :
    Measured Bool Nat :=
  CallCount.tick (match cert with
    | [] => eqTreeRun s t
    | tag :: raw =>
        bind (decFixedRun bs) (fun fuel => match fuel with
          | none => (false, 1)
          | some ys =>
              match parsed : parseMoveRun (tag :: raw) with
              | (none, cost) => (false, cost + 1)
              | (some (move, rest), cost) =>
                  let continued := bind (applyMoveRun move s) (fun result =>
                    match result with
                    | none => (false, 1)
                    | some next => checkStreamRun ys next t rest)
                  (continued.1, cost + continued.2)))
termination_by cert.length
decreasing_by
  exact parseMoveRun_rest_length_lt _ _ _ (congrArg Prod.fst parsed)

@[simp] theorem checkStreamRun_nil (bs : Bits) (s t : BinaryTree Unit) :
    checkStreamRun bs s t [] = CallCount.tick (eqTreeRun s t) := by
  rw [checkStreamRun]

/-- The whole-result equation exposes the actual sequence and every early stop. -/
theorem checkStreamRun_cons (bs : Bits) (s t : BinaryTree Unit)
    (tag : Tag) (raw : Word) :
    checkStreamRun bs s t (tag :: raw) =
      CallCount.tick (bind (decFixedRun bs) (fun fuel => match fuel with
        | none => (false, 1)
        | some ys => bind (parseMoveRun (tag :: raw)) (fun parsed =>
            match parsed with
            | none => (false, 1)
            | some (move, rest) => bind (applyMoveRun move s) (fun result =>
                match result with
                | none => (false, 1)
                | some next => checkStreamRun ys next t rest)))) := by
  rw [checkStreamRun]
  simp only [CallCount.tick, bind]
  cases fuel : (decFixedRun bs).1 with
  | none => rfl
  | some ys =>
      cases parsed : parseMoveRun (tag :: raw) with
      | mk result cost =>
          cases result with
          | none => rfl
          | some pair => cases pair; rfl

/-- The entire nonempty word is untouched when the actual predecessor fails. -/
theorem checkStreamRun_no_fuel (bs : Bits) (s t : BinaryTree Unit)
    (tag : Tag) (raw : Word) (failed : (decFixedRun bs).1 = none) :
    checkStreamRun bs s t (tag :: raw) = (false, (decFixedRun bs).2 + 2) := by
  rw [checkStreamRun_cons]
  simp only [CallCount.tick, bind, failed]

theorem checkStreamRun_zero (bs : Bits) (s t : BinaryTree Unit)
    (tag : Tag) (raw : Word) (zero : value bs = 0) :
    checkStreamRun bs s t (tag :: raw) = (false, (decFixedRun bs).2 + 2) :=
  checkStreamRun_no_fuel bs s t tag raw ((decFixedRun_none_iff bs).2 zero)

theorem checkStreamRun_replicate_false (width : Nat) (s t : BinaryTree Unit)
    (tag : Tag) (raw : Word) :
    checkStreamRun (List.replicate width false) s t (tag :: raw) =
      (false, 2 * width + 4) := by
  have failed := congrArg Prod.fst (decFixedRun_replicate_false width)
  rw [checkStreamRun_no_fuel _ _ _ _ _ failed, decFixedRun_replicate_false]

theorem checkStreamRun_parse_failure (bs ys : Bits) (s t : BinaryTree Unit)
    (tag : Tag) (raw : Word) (fuel : (decFixedRun bs).1 = some ys)
    (failed : (parseMoveRun (tag :: raw)).1 = none) :
    checkStreamRun bs s t (tag :: raw) =
      (false, (decFixedRun bs).2 + (parseMoveRun (tag :: raw)).2 + 2) := by
  rw [checkStreamRun_cons]
  simp only [CallCount.tick, bind, fuel, failed]
  congr 1

/-- A successful parse supplies the complete unused suffix; a failed move stops there. -/
theorem checkStreamRun_move_failure (bs ys : Bits) (s t : BinaryTree Unit)
    (cert rest : Word) (move : RotationMove)
    (fuel : (decFixedRun bs).1 = some ys)
    (parsed : (parseMoveRun cert).1 = some (move, rest))
    (failed : (applyMoveRun move s).1 = none) :
    checkStreamRun bs s t cert =
      (false, (decFixedRun bs).2 + (parseMoveRun cert).2 +
        (applyMoveRun move s).2 + 2) := by
  cases cert with
  | nil => simp only [parseMoveRun_nil] at parsed; cases parsed
  | cons tag raw =>
      rw [checkStreamRun_cons]
      simp only [CallCount.tick, bind, fuel, parsed, failed]
      congr 1
      omega

/-- Recurse only on the actual returned predecessor, next tree and unused suffix. -/
theorem checkStreamRun_step (bs ys : Bits) (s next t : BinaryTree Unit)
    (cert rest : Word) (move : RotationMove)
    (fuel : (decFixedRun bs).1 = some ys)
    (parsed : (parseMoveRun cert).1 = some (move, rest))
    (executed : (applyMoveRun move s).1 = some next) :
    checkStreamRun bs s t cert =
      ((checkStreamRun ys next t rest).1,
        (decFixedRun bs).2 + (parseMoveRun cert).2 + (applyMoveRun move s).2 +
          (checkStreamRun ys next t rest).2 + 1) := by
  cases cert with
  | nil => simp only [parseMoveRun_nil] at parsed; cases parsed
  | cons tag raw =>
      rw [checkStreamRun_cons]
      simp only [CallCount.tick, bind, fuel, parsed, executed]
      congr 1
      omega

private theorem checkStreamRun_sound_aux (size : Nat) :
    ∀ (cert : Word), cert.length = size →
      ∀ (bs : Bits) (s t : BinaryTree Unit),
        (checkStreamRun bs s t cert).1 = true →
          ∃ moves, cert = certCode moves ∧ applyMoves? moves s = some t ∧
            moves.length ≤ value bs := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro cert length bs s t accepted
      cases cert with
      | nil =>
          have same : s = t := by
            rw [checkStreamRun_nil, CallCount.tick_value, eqTreeRun_value] at accepted
            exact of_decide_eq_true accepted
          subst t
          exact ⟨[], rfl, rfl, Nat.zero_le _⟩
      | cons tag raw =>
          rw [checkStreamRun_cons] at accepted
          simp only [CallCount.tick_value, bind_value] at accepted
          cases fuel : (decFixedRun bs).1 with
          | none => simp only [fuel] at accepted; cases accepted
          | some ys =>
              simp only [fuel, bind_value] at accepted
              cases parsed : (parseMoveRun (tag :: raw)).1 with
              | none => simp only [parsed] at accepted; cases accepted
              | some pair =>
                  rcases pair with ⟨move, rest⟩
                  simp only [parsed, bind_value] at accepted
                  cases executed : (applyMoveRun move s).1 with
                  | none => simp only [executed] at accepted; cases accepted
                  | some next =>
                      simp only [executed] at accepted
                      have shorter : rest.length < size := by
                        have consumed := parseMoveRun_rest_length_lt
                          (tag :: raw) move rest parsed
                        omega
                      rcases ih rest.length shorter rest rfl ys next t accepted with
                        ⟨moves, encoded, traced, bounded⟩
                      have first : applyMove? move s = some next :=
                        (applyMoveRun_value move s).symm.trans executed
                      refine ⟨move :: moves, ?_, ?_, ?_⟩
                      · rw [(parseMoveRun_iff (tag :: raw) move rest).1 parsed, encoded]
                        rfl
                      · simp only [Trees.Rotations.applyMoves?_cons, first, Option.bind_some]
                        exact traced
                      · have arithmetic := decFixedRun_some_value fuel
                        simp only [List.length_cons]
                        omega

/-- Every actual accepting run decodes a legal trace within the binary threshold. -/
theorem checkStreamRun_sound (bs : Bits) (s t : BinaryTree Unit) (cert : Word)
    (accepted : (checkStreamRun bs s t cert).1 = true) :
    ∃ moves, cert = certCode moves ∧ applyMoves? moves s = some t ∧
      moves.length ≤ value bs :=
  checkStreamRun_sound_aux cert.length cert rfl bs s t accepted

/-- A legal bounded trace is accepted using its literal finite-word encoding. -/
theorem checkStreamRun_complete (moves : List RotationMove) :
    ∀ (bs : Bits) (s t : BinaryTree Unit),
      applyMoves? moves s = some t → moves.length ≤ value bs →
        (checkStreamRun bs s t (certCode moves)).1 = true := by
  induction moves with
  | nil =>
      intro bs s t traced bounded
      simp only [Trees.Rotations.applyMoves?_nil, Option.some.injEq] at traced
      subst t
      simp only [certCode, checkStreamRun_nil, CallCount.tick_value, eqTreeRun_value,
        decide_true]
  | cons move moves ih =>
      intro bs s t traced bounded
      have positive : 0 < value bs := by
        simp only [List.length_cons] at bounded
        omega
      obtain ⟨ys, fuel⟩ := decFixedRun_exists_of_pos positive
      have arithmetic := decFixedRun_some_value fuel
      have remaining : moves.length ≤ value ys := by
        simp only [List.length_cons] at bounded
        omega
      cases first : applyMove? move s with
      | none =>
          simp only [Trees.Rotations.applyMoves?_cons, first, Option.bind_none] at traced
          cases traced
      | some next =>
          have executed : (applyMoveRun move s).1 = some next := by
            rw [applyMoveRun_value]
            exact first
          have tailRun : applyMoves? moves next = some t := by
            simpa only [Trees.Rotations.applyMoves?_cons, first, Option.bind_some] using traced
          have parsed : (parseMoveRun (certCode (move :: moves))).1 =
              some (move, certCode moves) :=
            congrArg Prod.fst (parseMoveRun_code move (certCode moves))
          rw [checkStreamRun_step bs ys s next t _ _ move fuel parsed executed]
          exact ih ys next t tailRun remaining

/-- Exact recognition on arbitrary raw words, without syntax or reachability assumptions. -/
theorem checkStreamRun_iff (bs : Bits) (s t : BinaryTree Unit) (cert : Word) :
    (checkStreamRun bs s t cert).1 = true ↔
      ∃ moves, cert = certCode moves ∧ applyMoves? moves s = some t ∧
        moves.length ≤ value bs := by
  constructor
  · exact checkStreamRun_sound bs s t cert
  · rintro ⟨moves, rfl, traced, bounded⟩
    exact checkStreamRun_complete moves bs s t traced bounded

/-- Uniform work includes malformed certificates and every early-stop branch.
The measure is proof-only: successful parsing supplies the actual shorter suffix. -/
theorem checkStreamRun_cost_le (bs : Bits) (s t : BinaryTree Unit) (cert : Word) :
    (checkStreamRun bs s t cert).2 ≤
      (3 * bs.length + 3 * s.numNodes + 12) * cert.length + 3 * s.numNodes + 6 := by
  have all : ∀ width : Nat, ∀ (fuel : Bits) (source target : BinaryTree Unit)
      (word : Word), word.length = width →
      (checkStreamRun fuel source target word).2 ≤
        (3 * fuel.length + 3 * source.numNodes + 12) * word.length +
          3 * source.numNodes + 6 := by
    intro width
    induction width using Nat.strong_induction_on with
    | h width ih =>
        intro fuel source target word length
        cases word with
        | nil =>
            have bound := eqTreeRun_cost_le source target
            rw [checkStreamRun_nil]
            simp only [CallCount.tick, List.length_nil, Nat.mul_zero, Nat.zero_add]
            omega
        | cons tag raw =>
            have positive : 1 ≤ (tag :: raw).length := by simp
            have scaled : 3 * fuel.length + 3 * source.numNodes + 8 ≤
                (3 * fuel.length + 3 * source.numNodes + 8) * (tag :: raw).length := by
              simpa only [Nat.mul_one] using
                Nat.mul_le_mul_left (3 * fuel.length + 3 * source.numNodes + 8) positive
            have allowance : 3 * fuel.length + 3 * source.numNodes + 8 +
                4 * (tag :: raw).length ≤
                (3 * fuel.length + 3 * source.numNodes + 12) * (tag :: raw).length := by
              calc
                _ ≤ (3 * fuel.length + 3 * source.numNodes + 8) *
                    (tag :: raw).length + 4 * (tag :: raw).length :=
                  Nat.add_le_add_right scaled _
                _ = ((3 * fuel.length + 3 * source.numNodes + 8) + 4) *
                    (tag :: raw).length :=
                  (Nat.add_mul (3 * fuel.length + 3 * source.numNodes + 8) 4
                    (tag :: raw).length).symm
                _ = _ := by congr 1
            have decrementBound := decFixedRun_cost_le fuel
            have parserBound := parseMoveRun_cost_le (tag :: raw)
            simp only [List.length_cons] at allowance parserBound
            rw [checkStreamRun_cons]
            simp only [CallCount.tick, Resources.bind]
            cases decremented : (decFixedRun fuel).1 with
            | none => dsimp; omega
            | some nextFuel =>
                dsimp only
                cases parsed : (parseMoveRun (tag :: raw)).1 with
                | none => dsimp; omega
                | some pair =>
                    rcases pair with ⟨move, rest⟩
                    dsimp only
                    have moveBound := applyMoveRun_cost_le move source
                    cases moved : (applyMoveRun move source).1 with
                    | none => dsimp; omega
                    | some next =>
                        dsimp only
                        have consumed :=
                          parseMoveRun_consumed_length (tag :: raw) move rest parsed
                        have short : rest.length < width := by
                          rw [← length]
                          exact parseMoveRun_rest_length_lt (tag :: raw) move rest parsed
                        have tailBound := ih rest.length short nextFuel next target rest rfl
                        rw [decFixedRun_some_length decremented,
                          applyMoveRun_numNodes move source next moved] at tailBound
                        have parsedCost :=
                          parseMoveRun_cost_of_some (tag :: raw) move rest parsed
                        have prefixPositive : 1 ≤ move.position.length + 2 := by omega
                        have prefixScale : 3 * fuel.length + 3 * source.numNodes + 6 ≤
                            (3 * fuel.length + 3 * source.numNodes + 6) *
                              (move.position.length + 2) := by
                          simpa only [Nat.mul_one] using
                            Nat.mul_le_mul_left (3 * fuel.length + 3 * source.numNodes + 6)
                              prefixPositive
                        have prefixBound : (decFixedRun fuel).2 +
                            ((parseMoveRun (tag :: raw)).2 + (applyMoveRun move source).2) + 1 ≤
                            (3 * fuel.length + 3 * source.numNodes + 12) *
                              (move.position.length + 2) := by
                          rw [show 3 * fuel.length + 3 * source.numNodes + 12 =
                            (3 * fuel.length + 3 * source.numNodes + 6) + 6 by omega,
                            Nat.add_mul]
                          omega
                        rw [consumed, Nat.mul_add]
                        omega
  exact all cert.length bs s t cert rfl

end Resources.RotationCertificate

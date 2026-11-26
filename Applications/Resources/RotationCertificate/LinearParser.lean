import Applications.Resources.RotationCertificate.Encoding

/-!
# Actual linear bit, path and move prefix parsers

Each parser dispatch costs one. Returning some or none costs one; rebuilding
a decoded bit/path cons costs one. Recursive branches bind the actual returned
Option and suffix: failure adds two, successful cons reconstruction adds three.
The move adapter adds its dispatch and returned Option, with free record/pair
packaging. Delimiters and foreign symbols stop immediately; their remaining
suffixes are not scanned. Lengths and independent codes occur only in proofs.
These are source-event observations, not machine complexity or a tree parser.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)

def parseBitsRun : Word → Measured (Option (Bits × Word)) Nat
  | [] => (none, 2)
  | tag :: raw =>
      if tag = endInputTag then (some ([], raw), 2)
      else if tag = bitZeroTag then
        bind (parseBitsRun raw) (fun result => match result with
          | none => (none, 2)
          | some (bs, rest) => (some (false :: bs, rest), 3))
      else if tag = bitOneTag then
        bind (parseBitsRun raw) (fun result => match result with
          | none => (none, 2)
          | some (bs, rest) => (some (true :: bs, rest), 3))
      else (none, 2)

@[simp] theorem parseBitsRun_nil : parseBitsRun [] = (none, 2) := rfl

@[simp] theorem parseBitsRun_end (rest : Word) :
    parseBitsRun (endInputTag :: rest) = (some ([], rest), 2) := rfl

theorem parseBitsRun_bit (b : Bool) (raw : Word) :
    parseBitsRun (bitTag b :: raw) =
      bind (parseBitsRun raw) (fun result => match result with
        | none => (none, 2)
        | some (bs, rest) => (some (b :: bs, rest), 3)) := by
  cases b <;> rfl

theorem parseBitsRun_foreign (tag : Tag) (raw : Word)
    (notEnd : tag ≠ endInputTag) (notZero : tag ≠ bitZeroTag) (notOne : tag ≠ bitOneTag) :
    parseBitsRun (tag :: raw) = (none, 2) := by
  simp only [parseBitsRun, ite_eq_right notEnd, ite_eq_right notZero, ite_eq_right notOne]

theorem parseBitsRun_code (bs : Bits) (rest : Word) :
    parseBitsRun (bitTags bs ++ [endInputTag] ++ rest) =
      (some (bs, rest), 3 * bs.length + 2) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change parseBitsRun (bitTag b :: (bitTags bs ++ [endInputTag] ++ rest)) = _
      rw [parseBitsRun_bit, ih]
      simp only [bind, List.length_cons]
      apply Prod.ext
      · rfl
      · dsimp; omega

private theorem parseBitsRun_sound (raw : Word) (bs : Bits) (rest : Word)
    (returned : (parseBitsRun raw).1 = some (bs, rest)) :
    raw = bitTags bs ++ [endInputTag] ++ rest := by
  induction raw generalizing bs rest with
  | nil => cases returned
  | cons tag raw ih =>
      by_cases ended : tag = endInputTag
      · subst tag
        rw [parseBitsRun_end] at returned
        simp only [Option.some.injEq, Prod.mk.injEq] at returned
        rcases returned with ⟨rfl, rfl⟩
        rfl
      · by_cases zero : tag = bitZeroTag
        · subst tag
          change (parseBitsRun (bitTag false :: raw)).1 = some (bs, rest) at returned
          rw [parseBitsRun_bit] at returned
          simp only [bind] at returned
          cases child : (parseBitsRun raw).1 with
          | none => simp only [child] at returned; cases returned
          | some pair =>
              rcases pair with ⟨ys, suffix⟩
              simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
              rcases returned with ⟨rfl, rfl⟩
              change bitTag false :: raw = bitTag false :: (bitTags ys ++ [endInputTag] ++ suffix)
              rw [ih ys suffix child]
        · by_cases one : tag = bitOneTag
          · subst tag
            change (parseBitsRun (bitTag true :: raw)).1 = some (bs, rest) at returned
            rw [parseBitsRun_bit] at returned
            simp only [bind] at returned
            cases child : (parseBitsRun raw).1 with
            | none => simp only [child] at returned; cases returned
            | some pair =>
                rcases pair with ⟨ys, suffix⟩
                simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
                rcases returned with ⟨rfl, rfl⟩
                change bitTag true :: raw = bitTag true :: (bitTags ys ++ [endInputTag] ++ suffix)
                rw [ih ys suffix child]
          · rw [parseBitsRun_foreign tag raw ended zero one] at returned
            cases returned

/-- Exact prefix recognition with an arbitrary, untouched suffix. -/
theorem parseBitsRun_iff (raw : Word) (bs : Bits) (rest : Word) :
    (parseBitsRun raw).1 = some (bs, rest) ↔
      raw = bitTags bs ++ [endInputTag] ++ rest := by
  constructor
  · exact parseBitsRun_sound raw bs rest
  · intro encoded
    subst raw
    exact congrArg Prod.fst (parseBitsRun_code bs rest)

theorem parseBitsRun_cost_of_some (raw : Word) (bs : Bits) (rest : Word)
    (returned : (parseBitsRun raw).1 = some (bs, rest)) :
    (parseBitsRun raw).2 = 3 * bs.length + 2 := by
  rw [(parseBitsRun_iff raw bs rest).1 returned, parseBitsRun_code]

theorem parseBitsRun_cost_le (raw : Word) :
    (parseBitsRun raw).2 ≤ 3 * raw.length + 2 := by
  induction raw with
  | nil => decide
  | cons tag raw ih =>
      rw [parseBitsRun]
      simp only [List.length_cons]
      split
      · dsimp; omega
      · split
        · simp only [bind]
          cases child : (parseBitsRun raw).1 <;> dsimp <;> omega
        · split
          · simp only [bind]
            cases child : (parseBitsRun raw).1 <;> dsimp <;> omega
          · dsimp; omega

theorem parseBitsRun_consumed_length (raw : Word) (bs : Bits) (rest : Word)
    (returned : (parseBitsRun raw).1 = some (bs, rest)) :
    raw.length = bs.length + 1 + rest.length := by
  rw [(parseBitsRun_iff raw bs rest).1 returned]
  simp only [List.length_append, bitTags_length, List.length_cons, List.length_nil]

theorem bitTags_prefix_injective (bs cs : Bits) (rest suffix : Word)
    (encoded : bitTags bs ++ [endInputTag] ++ rest =
      bitTags cs ++ [endInputTag] ++ suffix) : bs = cs ∧ rest = suffix := by
  have observed := congrArg (fun raw => (parseBitsRun raw).1) encoded
  simpa only [parseBitsRun_code, Option.some.injEq, Prod.mk.injEq] using observed

theorem parseBitsRun_emit (bs : Bits) (rest : Word) :
    parseBitsRun (emitBitsRun bs (endInputTag :: rest)).1 =
      (some (bs, rest), 3 * bs.length + 2) := by
  rw [emitBitsRun_value]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    parseBitsRun_code bs rest

def parsePathRun : Word → Measured (Option (List Branch × Word)) Nat
  | [] => (none, 2)
  | tag :: raw =>
      if tag = endMoveTag then (some ([], raw), 2)
      else if tag = pathLeftTag then
        bind (parsePathRun raw) (fun result => match result with
          | none => (none, 2)
          | some (path, rest) => (some (Branch.left :: path, rest), 3))
      else if tag = pathRightTag then
        bind (parsePathRun raw) (fun result => match result with
          | none => (none, 2)
          | some (path, rest) => (some (Branch.right :: path, rest), 3))
      else (none, 2)

@[simp] theorem parsePathRun_nil : parsePathRun [] = (none, 2) := rfl

@[simp] theorem parsePathRun_end (rest : Word) :
    parsePathRun (endMoveTag :: rest) = (some ([], rest), 2) := rfl

theorem parsePathRun_branch (d : Branch) (raw : Word) :
    parsePathRun (branchTag d :: raw) =
      bind (parsePathRun raw) (fun result => match result with
        | none => (none, 2)
        | some (path, rest) => (some (d :: path, rest), 3)) := by
  cases d <;> rfl

theorem parsePathRun_foreign (tag : Tag) (raw : Word)
    (notEnd : tag ≠ endMoveTag) (notLeft : tag ≠ pathLeftTag) (notRight : tag ≠ pathRightTag) :
    parsePathRun (tag :: raw) = (none, 2) := by
  simp only [parsePathRun, ite_eq_right notEnd, ite_eq_right notLeft, ite_eq_right notRight]

theorem parsePathRun_code (path : List Branch) (rest : Word) :
    parsePathRun (pathTags path ++ [endMoveTag] ++ rest) =
      (some (path, rest), 3 * path.length + 2) := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      change parsePathRun (branchTag d :: (pathTags path ++ [endMoveTag] ++ rest)) = _
      rw [parsePathRun_branch, ih]
      simp only [bind, List.length_cons]
      apply Prod.ext
      · rfl
      · dsimp; omega

private theorem parsePathRun_sound (raw : Word) (path : List Branch) (rest : Word)
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    raw = pathTags path ++ [endMoveTag] ++ rest := by
  induction raw generalizing path rest with
  | nil => cases returned
  | cons tag raw ih =>
      by_cases ended : tag = endMoveTag
      · subst tag
        rw [parsePathRun_end] at returned
        simp only [Option.some.injEq, Prod.mk.injEq] at returned
        rcases returned with ⟨rfl, rfl⟩
        rfl
      · by_cases left : tag = pathLeftTag
        · subst tag
          change (parsePathRun (branchTag .left :: raw)).1 = some (path, rest) at returned
          rw [parsePathRun_branch] at returned
          simp only [bind] at returned
          cases child : (parsePathRun raw).1 with
          | none => simp only [child] at returned; cases returned
          | some pair =>
              rcases pair with ⟨ds, suffix⟩
              simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
              rcases returned with ⟨rfl, rfl⟩
              change branchTag .left :: raw = branchTag .left :: (pathTags ds ++ [endMoveTag] ++ suffix)
              rw [ih ds suffix child]
        · by_cases right : tag = pathRightTag
          · subst tag
            change (parsePathRun (branchTag .right :: raw)).1 = some (path, rest) at returned
            rw [parsePathRun_branch] at returned
            simp only [bind] at returned
            cases child : (parsePathRun raw).1 with
            | none => simp only [child] at returned; cases returned
            | some pair =>
                rcases pair with ⟨ds, suffix⟩
                simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
                rcases returned with ⟨rfl, rfl⟩
                change branchTag .right :: raw = branchTag .right :: (pathTags ds ++ [endMoveTag] ++ suffix)
                rw [ih ds suffix child]
          · rw [parsePathRun_foreign tag raw ended left right] at returned
            cases returned

theorem parsePathRun_iff (raw : Word) (path : List Branch) (rest : Word) :
    (parsePathRun raw).1 = some (path, rest) ↔
      raw = pathTags path ++ [endMoveTag] ++ rest := by
  constructor
  · exact parsePathRun_sound raw path rest
  · intro encoded
    subst raw
    exact congrArg Prod.fst (parsePathRun_code path rest)

theorem parsePathRun_cost_of_some (raw : Word) (path : List Branch) (rest : Word)
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    (parsePathRun raw).2 = 3 * path.length + 2 := by
  rw [(parsePathRun_iff raw path rest).1 returned, parsePathRun_code]

theorem parsePathRun_cost_le (raw : Word) :
    (parsePathRun raw).2 ≤ 3 * raw.length + 2 := by
  induction raw with
  | nil => decide
  | cons tag raw ih =>
      rw [parsePathRun]
      simp only [List.length_cons]
      split
      · dsimp; omega
      · split
        · simp only [bind]
          cases child : (parsePathRun raw).1 <;> dsimp <;> omega
        · split
          · simp only [bind]
            cases child : (parsePathRun raw).1 <;> dsimp <;> omega
          · dsimp; omega

theorem parsePathRun_consumed_length (raw : Word) (path : List Branch) (rest : Word)
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    raw.length = path.length + 1 + rest.length := by
  rw [(parsePathRun_iff raw path rest).1 returned]
  simp only [List.length_append, pathTags_length, List.length_cons, List.length_nil]

theorem pathTags_prefix_injective (path other : List Branch) (rest suffix : Word)
    (encoded : pathTags path ++ [endMoveTag] ++ rest =
      pathTags other ++ [endMoveTag] ++ suffix) : path = other ∧ rest = suffix := by
  have observed := congrArg (fun raw => (parsePathRun raw).1) encoded
  simpa only [parsePathRun_code, Option.some.injEq, Prod.mk.injEq] using observed

theorem parsePathRun_emit (path : List Branch) (rest : Word) :
    parsePathRun (emitPathRun path (endMoveTag :: rest)).1 =
      (some (path, rest), 3 * path.length + 2) := by
  rw [emitPathRun_value]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    parsePathRun_code path rest

/-- Decode syntax only; the returned move need not be legal on any chosen tree. -/
def parseMoveRun : Word → Measured (Option (RotationMove × Word)) Nat
  | [] => (none, 2)
  | tag :: raw =>
      if tag = rotateLeftTag then
        bind (parsePathRun raw) (fun result => match result with
          | none => (none, 2)
          | some (path, rest) => (some (⟨.left, path⟩, rest), 2))
      else if tag = rotateRightTag then
        bind (parsePathRun raw) (fun result => match result with
          | none => (none, 2)
          | some (path, rest) => (some (⟨.right, path⟩, rest), 2))
      else (none, 2)

@[simp] theorem parseMoveRun_nil : parseMoveRun [] = (none, 2) := rfl

theorem parseMoveRun_direction (d : RotationDirection) (raw : Word) :
    parseMoveRun (directionTag d :: raw) =
      bind (parsePathRun raw) (fun result => match result with
        | none => (none, 2)
        | some (path, rest) => (some (⟨d, path⟩, rest), 2)) := by
  cases d <;> rfl

theorem parseMoveRun_foreign (tag : Tag) (raw : Word)
    (notLeft : tag ≠ rotateLeftTag) (notRight : tag ≠ rotateRightTag) :
    parseMoveRun (tag :: raw) = (none, 2) := by
  simp only [parseMoveRun, ite_eq_right notLeft, ite_eq_right notRight]

theorem parseMoveRun_code (move : RotationMove) (rest : Word) :
    parseMoveRun (moveCode move ++ rest) =
      (some (move, rest), 3 * move.position.length + 4) := by
  change parseMoveRun (directionTag move.direction ::
    (pathTags move.position ++ [endMoveTag] ++ rest)) = _
  rw [parseMoveRun_direction, parsePathRun_code]
  simp only [bind]

private theorem parseMoveRun_sound (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    raw = moveCode move ++ rest := by
  cases raw with
  | nil => cases returned
  | cons tag raw =>
      by_cases left : tag = rotateLeftTag
      · subst tag
        change (parseMoveRun (directionTag .left :: raw)).1 = some (move, rest) at returned
        rw [parseMoveRun_direction] at returned
        simp only [bind] at returned
        cases child : (parsePathRun raw).1 with
        | none => simp only [child] at returned; cases returned
        | some pair =>
            rcases pair with ⟨path, suffix⟩
            simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
            rcases returned with ⟨rfl, rfl⟩
            change directionTag .left :: raw =
              directionTag .left :: (pathTags path ++ [endMoveTag] ++ suffix)
            rw [(parsePathRun_iff raw path suffix).1 child]
      · by_cases right : tag = rotateRightTag
        · subst tag
          change (parseMoveRun (directionTag .right :: raw)).1 = some (move, rest) at returned
          rw [parseMoveRun_direction] at returned
          simp only [bind] at returned
          cases child : (parsePathRun raw).1 with
          | none => simp only [child] at returned; cases returned
          | some pair =>
              rcases pair with ⟨path, suffix⟩
              simp only [child, Option.some.injEq, Prod.mk.injEq] at returned
              rcases returned with ⟨rfl, rfl⟩
              change directionTag .right :: raw =
                directionTag .right :: (pathTags path ++ [endMoveTag] ++ suffix)
              rw [(parsePathRun_iff raw path suffix).1 child]
        · rw [parseMoveRun_foreign tag raw left right] at returned
          cases returned

theorem parseMoveRun_iff (raw : Word) (move : RotationMove) (rest : Word) :
    (parseMoveRun raw).1 = some (move, rest) ↔ raw = moveCode move ++ rest := by
  constructor
  · exact parseMoveRun_sound raw move rest
  · intro encoded
    subst raw
    exact congrArg Prod.fst (parseMoveRun_code move rest)

theorem parseMoveRun_cost_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    (parseMoveRun raw).2 = 3 * move.position.length + 4 := by
  rw [(parseMoveRun_iff raw move rest).1 returned, parseMoveRun_code]

theorem parseMoveRun_cost_le (raw : Word) :
    (parseMoveRun raw).2 ≤ 4 * raw.length + 2 := by
  cases raw with
  | nil => decide
  | cons tag raw =>
      have bound := parsePathRun_cost_le raw
      rw [parseMoveRun]
      simp only [List.length_cons]
      split
      · simp only [bind]
        cases child : (parsePathRun raw).1 <;> dsimp <;> omega
      · split
        · simp only [bind]
          cases child : (parsePathRun raw).1 <;> dsimp <;> omega
        · dsimp; omega

theorem parseMoveRun_consumed_length (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) :
    raw.length = move.position.length + 2 + rest.length := by
  rw [(parseMoveRun_iff raw move rest).1 returned]
  simp only [List.length_append, moveCode_length]

theorem parseMoveRun_consumes_two (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) : rest.length + 2 ≤ raw.length := by
  have length := parseMoveRun_consumed_length raw move rest returned
  omega

theorem parseMoveRun_rest_length_lt (raw : Word) (move : RotationMove) (rest : Word)
    (returned : (parseMoveRun raw).1 = some (move, rest)) : rest.length < raw.length := by
  have length := parseMoveRun_consumed_length raw move rest returned
  omega

theorem moveCode_prefix_injective (move other : RotationMove) (rest suffix : Word)
    (encoded : moveCode move ++ rest = moveCode other ++ suffix) :
    move = other ∧ rest = suffix := by
  have observed := congrArg (fun raw => (parseMoveRun raw).1) encoded
  simpa only [parseMoveRun_code, Option.some.injEq, Prod.mk.injEq] using observed

theorem parseMoveRun_emit (move : RotationMove) (rest : Word) :
    parseMoveRun (emitMoveRun move rest).1 = (some (move, rest), 3 * move.position.length + 4) := by
  rw [emitMoveRun_value, parseMoveRun_code]

end Resources.RotationCertificate

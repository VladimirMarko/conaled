import Applications.Resources.RotationCertificate.TreeParser

/-!
# Complete finite-word rotation-certificate input parsing

The parser binds the actual tree, separator, tree, separator and bit-parser
results, then checks that the actual remaining word is empty. It preserves the
represented threshold bits, including redundant high zeros, and permits
syntactically valid trees of different sizes. Rotation legality is a later
semantic check. Every failure stops without traversing the remaining input.

The input wrapper charges one entry. Each separator parser and the final EOF
checker charge one entry and one returned Option. Newly propagated none costs
one. Other record/pair/control packaging and measured sequencing are free.
The successful overhead beyond the two tree parsers and bit parser is seven.
These are declared source-event observations, not machine-time or bit costs.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Resources.BinaryCounter (Bits)

abbrev ParsedInput := BinaryTree Unit × BinaryTree Unit × Bits

/-- Inspect exactly one separator; never inspect its returned suffix. -/
def parseSeparatorRun : Word → Measured (Option Word) Nat
  | [] => (none, 2)
  | tag :: raw => if tag = separatorTag then (some raw, 2) else (none, 2)

@[simp] theorem parseSeparatorRun_nil : parseSeparatorRun [] = (none, 2) := rfl

@[simp] theorem parseSeparatorRun_separator (rest : Word) :
    parseSeparatorRun (separatorTag :: rest) = (some rest, 2) := rfl

theorem parseSeparatorRun_foreign (tag : Tag) (rest : Word)
    (different : tag ≠ separatorTag) :
    parseSeparatorRun (tag :: rest) = (none, 2) := by
  simp only [parseSeparatorRun, ite_eq_right different]

@[simp] theorem parseSeparatorRun_cost (raw : Word) : (parseSeparatorRun raw).2 = 2 := by
  cases raw with
  | nil => rfl
  | cons tag raw => simp only [parseSeparatorRun]; split <;> rfl

theorem parseSeparatorRun_iff (raw rest : Word) :
    (parseSeparatorRun raw).1 = some rest ↔ raw = separatorTag :: rest := by
  cases raw with
  | nil => simp only [parseSeparatorRun_nil, reduceCtorEq]
  | cons tag raw =>
      by_cases same : tag = separatorTag
      · subst tag
        simp only [parseSeparatorRun_separator, Option.some.injEq, List.cons.injEq,
          true_and]
      · rw [parseSeparatorRun_foreign tag raw same]
        simp only [reduceCtorEq, List.cons.injEq, same, false_and]

theorem parseSeparatorRun_consumed_length (raw rest : Word)
    (returned : (parseSeparatorRun raw).1 = some rest) :
    raw.length = rest.length + 1 := by
  rw [(parseSeparatorRun_iff raw rest).1 returned, List.length_cons]

/-- Final state: inspect EOF and construct the single final result Option. -/
def finishInputRun (source target : BinaryTree Unit) (bs : Bits) :
    Word → Measured (Option ParsedInput) Nat
  | [] => (some (source, target, bs), 2)
  | _ :: _ => (none, 2)

theorem finishInputRun_eq (source target : BinaryTree Unit) (bs : Bits) (rest : Word) :
    finishInputRun source target bs rest =
      (if rest = [] then some (source, target, bs) else none, 2) := by
  cases rest <;> rfl

@[simp] theorem finishInputRun_cost (source target : BinaryTree Unit) (bs : Bits)
    (rest : Word) : (finishInputRun source target bs rest).2 = 2 := by
  cases rest <;> rfl

/-- Recognize the complete input, including EOF after the threshold delimiter. -/
def parseInputRun (raw : Word) : Measured (Option ParsedInput) Nat :=
  CallCount.tick (bind (parseTreeRun raw) (fun result => match result with
    | none => (none, 1)
    | some (source, afterSource) =>
      bind (parseSeparatorRun afterSource) (fun result => match result with
        | none => (none, 1)
        | some beforeTarget =>
          bind (parseTreeRun beforeTarget) (fun result => match result with
            | none => (none, 1)
            | some (target, afterTarget) =>
              bind (parseSeparatorRun afterTarget) (fun result => match result with
                | none => (none, 1)
                | some beforeBits =>
                  bind (parseBitsRun beforeBits) (fun result => match result with
                    | none => (none, 1)
                    | some (bs, rest) => finishInputRun source target bs rest))))))

/-- Encoded input followed by material reaches the final EOF check without scanning it. -/
theorem parseInputRun_code_append (source target : BinaryTree Unit) (bs : Bits)
    (rest : Word) :
    parseInputRun (inputCode source target bs ++ rest) =
      (if rest = [] then some (source, target, bs) else none,
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) := by
  have parsedBits : parseBitsRun (bitTags bs ++ endInputTag :: rest) =
      (some (bs, rest), 3 * bs.length + 2) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      parseBitsRun_code bs rest
  simp only [parseInputRun, inputCode, List.append_assoc, List.cons_append, List.nil_append,
    parseTreeRun_code, parseSeparatorRun_separator, parsedBits,
    CallCount.tick, bind, finishInputRun_eq]
  apply Prod.ext
  · rfl
  · dsimp
    omega

theorem parseInputRun_code (source target : BinaryTree Unit) (bs : Bits) :
    parseInputRun (inputCode source target bs) =
      (some (source, target, bs),
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) := by
  simpa only [List.append_nil, ite_true] using
    parseInputRun_code_append source target bs []

theorem parseInputRun_trailing (source target : BinaryTree Unit) (bs : Bits)
    (tag : Tag) (tail : Word) :
    parseInputRun (inputCode source target bs ++ tag :: tail) =
      (none, 7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) := by
  simpa only [List.cons_ne_nil, ite_false] using
    parseInputRun_code_append source target bs (tag :: tail)

private theorem parseInputRun_sound (raw : Word) (source target : BinaryTree Unit)
    (bs : Bits) (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    raw = inputCode source target bs := by
  simp only [parseInputRun, CallCount.tick, bind] at returned
  cases first : (parseTreeRun raw).1 with
  | none => simp only [first] at returned; cases returned
  | some pair =>
      rcases pair with ⟨s, afterSource⟩
      simp only [first] at returned
      cases firstSep : (parseSeparatorRun afterSource).1 with
      | none => simp only [firstSep] at returned; cases returned
      | some beforeTarget =>
          simp only [firstSep] at returned
          cases second : (parseTreeRun beforeTarget).1 with
          | none => simp only [second] at returned; cases returned
          | some pair =>
              rcases pair with ⟨t, afterTarget⟩
              simp only [second] at returned
              cases secondSep : (parseSeparatorRun afterTarget).1 with
              | none => simp only [secondSep] at returned; cases returned
              | some beforeBits =>
                  simp only [secondSep] at returned
                  cases threshold : (parseBitsRun beforeBits).1 with
                  | none => simp only [threshold] at returned; cases returned
                  | some pair =>
                      rcases pair with ⟨bits, rest⟩
                      simp only [threshold] at returned
                      cases rest with
                      | cons tag tail => cases returned
                      | nil =>
                          simp only [finishInputRun, Option.some.injEq,
                            Prod.mk.injEq] at returned
                          rcases returned with ⟨rfl, rfl, rfl⟩
                          rw [(parseTreeRun_iff raw s afterSource).1 first,
                            (parseSeparatorRun_iff afterSource beforeTarget).1 firstSep,
                            (parseTreeRun_iff beforeTarget t afterTarget).1 second,
                            (parseSeparatorRun_iff afterTarget beforeBits).1 secondSep,
                            (parseBitsRun_iff beforeBits bits []).1 threshold]
                          simp only [inputCode, List.append_assoc, List.cons_append,
                            List.nil_append, List.append_nil]

/-- Complete recognition for every raw word; syntax imposes no equality of tree sizes. -/
theorem parseInputRun_iff (raw : Word) (source target : BinaryTree Unit) (bs : Bits) :
    (parseInputRun raw).1 = some (source, target, bs) ↔
      raw = inputCode source target bs := by
  constructor
  · exact parseInputRun_sound raw source target bs
  · intro encoded
    subst raw
    exact congrArg Prod.fst (parseInputRun_code source target bs)

theorem parseInputRun_cost_of_some (raw : Word) (source target : BinaryTree Unit)
    (bs : Bits) (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    (parseInputRun raw).2 =
      7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15 := by
  rw [(parseInputRun_iff raw source target bs).1 returned, parseInputRun_code]

/-- Uniform work includes malformed input and uninspected trailing material. -/
theorem parseInputRun_cost_le (raw : Word) :
    (parseInputRun raw).2 ≤ 20 * (raw.length + 1) := by
  have firstBound := parseTreeRun_cost_le raw
  simp only [parseInputRun, CallCount.tick, bind]
  cases first : (parseTreeRun raw).1 with
  | none => dsimp; omega
  | some pair =>
      rcases pair with ⟨source, afterSource⟩
      have firstLength := parseTreeRun_consumed_length raw source afterSource first
      simp only [parseSeparatorRun_cost]
      cases firstSep : (parseSeparatorRun afterSource).1 with
      | none => dsimp; omega
      | some beforeTarget =>
          dsimp only
          have firstSepLength :=
            parseSeparatorRun_consumed_length afterSource beforeTarget firstSep
          have secondBound := parseTreeRun_cost_le beforeTarget
          cases second : (parseTreeRun beforeTarget).1 with
          | none => dsimp; omega
          | some pair =>
              rcases pair with ⟨target, afterTarget⟩
              have secondLength :=
                parseTreeRun_consumed_length beforeTarget target afterTarget second
              dsimp only
              cases secondSep : (parseSeparatorRun afterTarget).1 with
              | none => dsimp; omega
              | some beforeBits =>
                  dsimp only
                  have secondSepLength :=
                    parseSeparatorRun_consumed_length afterTarget beforeBits secondSep
                  have bitsBound := parseBitsRun_cost_le beforeBits
                  cases threshold : (parseBitsRun beforeBits).1 with
                  | none => dsimp; omega
                  | some pair =>
                      rcases pair with ⟨bs, rest⟩
                      simp only [finishInputRun_cost]
                      omega

theorem parseInputRun_length (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    raw.length = 2 * source.numNodes + 2 * target.numNodes + bs.length + 5 := by
  rw [(parseInputRun_iff raw source target bs).1 returned, inputCode_length]

/-- Sizes are specifications of represented inputs, never executed parser work. -/
theorem parseInputRun_sizes_le (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    source.numNodes ≤ raw.length ∧ target.numNodes ≤ raw.length ∧ bs.length ≤ raw.length := by
  have length := parseInputRun_length raw source target bs returned
  omega

theorem parseInputRun_injective (source target : BinaryTree Unit) (bs : Bits)
    (otherSource otherTarget : BinaryTree Unit) (otherBits : Bits)
    (encoded : inputCode source target bs = inputCode otherSource otherTarget otherBits) :
    source = otherSource ∧ target = otherTarget ∧ bs = otherBits := by
  have observed := congrArg (fun raw => (parseInputRun raw).1) encoded
  simpa only [parseInputRun_code, Option.some.injEq, Prod.mk.injEq] using observed

theorem parseInputRun_emit (source target : BinaryTree Unit) (bs : Bits) :
    parseInputRun (emitInputRun source target bs).1 =
      (some (source, target, bs),
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15) := by
  rw [emitInputRun_value, parseInputRun_code]

end Resources.RotationCertificate

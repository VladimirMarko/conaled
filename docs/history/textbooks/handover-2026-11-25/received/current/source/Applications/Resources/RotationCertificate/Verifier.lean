import Applications.Resources.RotationCertificate.InputParser
import Applications.Resources.RotationCertificate.Streaming
import Applications.Resources.RotationCertificate.Witness

/-!
# Complete encoded rotation-certificate verifier

The actual input parser supplies both trees and the original binary fuel to
the actual streaming checker. The represented language uses the attained
minimum, while execution neither computes distance nor expands fuel into unary.
Every yes input has a quadratic-size encoded certificate. The measured work
bound covers arbitrary malformed or overlong input and certificate words.
These source-event results still require a separate computational-model bridge
before asserting membership in a named formal machine complexity class.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Trees.Rotations (RotationMove applyMoves?)
open Resources.BinaryCounter (Bits value)

/-- Parse the actual complete input before running the actual certificate stream. -/
def verifyRun (input cert : Word) : Measured Bool Nat :=
  CallCount.tick (bind (parseInputRun input) (fun parsed => match parsed with
    | none => (false, 1)
    | some (source, target, bs) => checkStreamRun bs source target cert))

/-- Input failure never invokes the certificate checker. -/
theorem verifyRun_of_none (input cert : Word)
    (failed : (parseInputRun input).1 = none) :
    verifyRun input cert = (false, (parseInputRun input).2 + 2) := by
  simp only [verifyRun, CallCount.tick, bind, failed]

/-- The checker consumes the returned fields, and its actual Boolean is reused. -/
theorem verifyRun_of_some (input cert : Word) (source target : BinaryTree Unit)
    (bs : Bits) (parsed : (parseInputRun input).1 = some (source, target, bs)) :
    verifyRun input cert =
      ((checkStreamRun bs source target cert).1,
        (parseInputRun input).2 + (checkStreamRun bs source target cert).2 + 1) := by
  simp only [verifyRun, CallCount.tick, bind, parsed]

theorem verifyRun_code (source target : BinaryTree Unit) (bs : Bits) (cert : Word) :
    verifyRun (inputCode source target bs) cert =
      ((checkStreamRun bs source target cert).1,
        7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 16 +
          (checkStreamRun bs source target cert).2) := by
  simp only [verifyRun, parseInputRun_code, CallCount.tick, bind]
  congr 1
  omega

/-- Complete raw-word acceptance, with no assumed syntax or equal-size premise. -/
theorem verifyRun_accept_iff (input cert : Word) :
    (verifyRun input cert).1 = true ↔
      ∃ (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
        input = inputCode source target bs ∧ cert = certCode moves ∧
        applyMoves? moves source = some target ∧ moves.length ≤ value bs := by
  constructor
  · intro accepted
    cases parsed : (parseInputRun input).1 with
    | none =>
        rw [verifyRun_of_none input cert parsed] at accepted
        cases accepted
    | some fields =>
        rcases fields with ⟨source, target, bs⟩
        rw [verifyRun_of_some input cert source target bs parsed] at accepted
        obtain ⟨moves, encoded, run, bound⟩ :=
          (checkStreamRun_iff bs source target cert).1 accepted
        exact ⟨source, target, bs, moves,
          (parseInputRun_iff input source target bs).1 parsed, encoded, run, bound⟩
  · rintro ⟨source, target, bs, moves, encodedInput, encodedCert, run, bound⟩
    rw [encodedInput, verifyRun_code]
    exact (checkStreamRun_iff bs source target cert).2 ⟨moves, encodedCert, run, bound⟩

/-- Actual acceptance implies the independently specified rotation-distance language. -/
theorem verifyRun_sound (input cert : Word) (accepted : (verifyRun input cert).1 = true) :
    Yes input := by
  obtain ⟨source, target, bs, moves, encoded, _, run, bound⟩ :=
    (verifyRun_accept_iff input cert).1 accepted
  exact (yes_iff_trace input).2 ⟨source, target, bs, moves, encoded, run, bound⟩

/-- The chosen witness is an attained minimum, so it fits even a tight threshold. -/
theorem verifyRun_complete_small (input : Word) (yes : Yes input) :
    ∃ cert : Word, cert.length ≤ 2 * input.length ^ 2 ∧
      (verifyRun input cert).1 = true := by
  obtain ⟨source, target, bs, moves, encoded, run, bound, size⟩ := yes_small_trace input yes
  refine ⟨certCode moves, size, ?_⟩
  exact (verifyRun_accept_iff input (certCode moves)).2
    ⟨source, target, bs, moves, encoded, rfl, run, bound⟩

theorem yes_iff_exists_certificate (input : Word) :
    Yes input ↔ ∃ cert : Word, (verifyRun input cert).1 = true := by
  constructor
  · intro yes
    obtain ⟨cert, _, accepted⟩ := verifyRun_complete_small input yes
    exact ⟨cert, accepted⟩
  · rintro ⟨cert, accepted⟩
    exact verifyRun_sound input cert accepted

/-- Every pair of raw words has polynomial measured work, including all failures. -/
theorem verifyRun_work_all (input cert : Word) :
    (verifyRun input cert).2 ≤ 32 * (input.length + cert.length + 1) ^ 2 := by
  have inputBound := parseInputRun_cost_le input
  cases parsed : (parseInputRun input).1 with
  | none =>
      rw [verifyRun_of_none input cert parsed]
      dsimp only
      nlinarith [Nat.zero_le (input.length * input.length),
        Nat.zero_le (cert.length * cert.length), Nat.zero_le (input.length * cert.length)]
  | some fields =>
      rcases fields with ⟨source, target, bs⟩
      rw [verifyRun_of_some input cert source target bs parsed]
      dsimp only
      have streamBound := checkStreamRun_cost_le bs source target cert
      have sizes := parseInputRun_sizes_le input source target bs parsed
      have sourceScaled := Nat.mul_le_mul_right cert.length sizes.1
      have bitsScaled := Nat.mul_le_mul_right cert.length sizes.2.2
      nlinarith [Nat.zero_le (input.length * input.length),
        Nat.zero_le (cert.length * cert.length), Nat.zero_le (input.length * cert.length)]

/-- Trailing input is rejected before inspecting any certificate or trailing tail. -/
theorem verifyRun_trailing_input (source target : BinaryTree Unit) (bs : Bits)
    (tag : Tag) (tail cert : Word) :
    verifyRun (inputCode source target bs ++ tag :: tail) cert =
      (false, 7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 17) := by
  have failed := congrArg Prod.fst (parseInputRun_trailing source target bs tag tail)
  rw [verifyRun_of_none _ cert failed, parseInputRun_trailing]

/-- Compose actual input/certificate emitters with actual verification. -/
theorem verifyRun_emit_trace (source target : BinaryTree Unit) (bs : Bits)
    (moves : List RotationMove) (run : applyMoves? moves source = some target)
    (bound : moves.length ≤ value bs) :
    (verifyRun (emitInputRun source target bs).1 (emitCertificateRun moves []).1).1 =
      true := by
  rw [emitInputRun_value, emitCertificateRun_value, List.append_nil]
  exact (verifyRun_accept_iff (inputCode source target bs) (certCode moves)).2
    ⟨source, target, bs, moves, rfl, rfl, run, bound⟩

end Resources.RotationCertificate

import Protocol144b

set_option autoImplicit false
set_option warningAsError true

/-!
# Existing arbitrary-raw checking relation and fixed parser cases

UNCOMPILED connected clients. The requested parser converse and exact language
equivalence already exist in Protocol144b; the anonymous examples below consume
those proofs directly. No second parser proof or public duplicate API is added.
-/

namespace Examples.DelimiterCheckingRelation150

open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open Resources.RotationCertificate.DelimiterPreludeDraft

/-- The existing converse applies to arbitrary raw words. -/
example (raw : Raw) (input cert : Bits) :
    splitLiteral raw = some (input, cert) ↔ raw = literalPair input cert :=
  GeneralProof1.splitLiteral_iff raw input cert

/-- This is already the exact arbitrary-raw checking-relation theorem. -/
example (raw : Raw) :
    verifyDelimited raw = true ↔
      ∃ input cert : Bits,
        raw = literalPair input cert ∧ (verifyBitsRun input cert).1 = true :=
  GeneralProof1.verifyDelimited_accept_iff raw

/-- Parser failure forces rejection without inspecting a Boolean verifier. -/
example (raw : Raw) (malformed : splitLiteral raw = none) :
    verifyDelimited raw = false := by
  simp only [verifyDelimited, malformed]

theorem empty_missing_rejects :
    splitLiteral ([] : Raw) = none ∧ verifyDelimited [] = false :=
  ⟨rfl, rfl⟩

theorem present_false_missing_rejects :
    splitLiteral [some false] = none ∧ verifyDelimited [some false] = false :=
  ⟨rfl, rfl⟩

theorem delimiter_only_parses :
    splitLiteral [none] = some ([], []) := rfl

theorem empty_input_false_certificate_parses :
    splitLiteral [none, some false] = some ([], [false]) := rfl

theorem false_input_empty_certificate_parses :
    splitLiteral [some false, none] = some ([false], []) := rfl

theorem mixed_order_parses :
    splitLiteral [some true, some false, none, some false, some true] =
      some ([true, false], [false, true]) := rfl

/-- The mixed fixture preserves the actual checker result, without guessing it. -/
theorem mixed_pair_checker :
    verifyDelimited [some true, some false, none, some false, some true] =
      (verifyBitsRun [true, false] [false, true]).1 :=
  verifyDelimited_pair [true, false] [false, true]

theorem two_delimiters_reject :
    splitLiteral [none, none] = none ∧ verifyDelimited [none, none] = false :=
  ⟨rfl, rfl⟩

theorem repeated_with_more_tail_rejects :
    splitLiteral [some false, none, some true, none, some false, none] = none ∧
      verifyDelimited [some false, none, some true, none, some false, none] = false :=
  ⟨rfl, rfl⟩

end Examples.DelimiterCheckingRelation150

import CertifiedNatChecker
import QueensNatChecker
import Squares

/-!
Experimental clients of the preserved checker. See
`docs/research/certified-nat-checker-preview.md` for provenance and scope.
The doubling specification and successor consumer are independent of queens.
The adapter preserves the native endpoint and uses the existing square composition.
-/

set_option autoImplicit false

namespace CertifiedNatCheckerPreview

open ADWH.Experiments.Chapter15.CertifiedNatChecker

/-- Natural numbers retain their ordinary equality and interpretation. -/
def natRep : Squares.Rep := ⟨Nat, Nat, id⟩

/-- The endpoint's existing universal agreement is exactly this square law. -/
def endpointSquare {source : Nat → Nat} (endpoint : Endpoint source) :
    Squares.Square natRep natRep where
  impl := endpoint.run
  spec := source
  commutes := endpoint.correct

def successorSquare : Squares.Square natRep natRep where
  impl := Nat.succ
  spec := Nat.succ
  commutes := fun _ => rfl

/-- The declarative result counts two copies of the input. -/
def doubleSpec (n : Nat) : Nat := n + n

def doubleEndpoint : Endpoint doubleSpec where
  name := "double"
  run := fun n => 2 * n
  correct := fun n => Nat.two_mul n

def doubleThenSuccessor : Squares.Square natRep natRep :=
  Squares.compose successorSquare (endpointSquare doubleEndpoint)

theorem doubleThenSuccessor_correct (n : Nat) :
    doubleThenSuccessor.impl n = (n + n) + 1 :=
  doubleThenSuccessor.commutes n

/-- The consumer returns the claimed result plus one only after checking. -/
def report (tokens : List String) : Option Nat :=
  (acceptTokens doubleEndpoint tokens).map (fun claim => claim.value + 1)

theorem report_sound {tokens : List String} {claim : Claim}
    (accepted : acceptTokens doubleEndpoint tokens = some claim) :
    report tokens = some (doubleThenSuccessor.spec claim.input) := by
  have eq := (acceptTokens_sound doubleEndpoint accepted).2
  simp only [report, accepted, Option.map_some]
  change some (claim.value + 1) = some (doubleSpec claim.input + 1)
  rw [eq]

/-- The reusable canonical theorem supplies acceptance, rather than an assumed
runtime result. Three pairs give six, and the consumer adds one. -/
theorem accepts_three :
    acceptTokens doubleEndpoint ["double", "3", "=", "6"] = some ⟨3, 6⟩ :=
  (acceptTokens_render_iff doubleEndpoint ⟨3, 6⟩).2 rfl

theorem reports_seven : report ["double", "3", "=", "6"] = some 7 :=
  report_sound accepts_three

theorem accepts_zero :
    acceptTokens doubleEndpoint ["double", "0", "=", "0"] = some ⟨0, 0⟩ :=
  (acceptTokens_render_iff doubleEndpoint ⟨0, 0⟩).2 rfl

/-- Noncanonical rejection is inherited from the supplied public contract. -/
theorem report_rejects_noncanonical (tokens : List String)
    (h : ∀ claim, tokens ≠ renderTokens doubleEndpoint claim) : report tokens = none := by
  simp only [report, reject_noncanonical doubleEndpoint tokens h, Option.map_none]

theorem rejects_wrong_value :
    report ["double", "3", "=", "7"] = none := by
  change (acceptTokens doubleEndpoint (renderTokens doubleEndpoint ⟨3, 7⟩)).map _ = none
  rw [acceptTokens, parseTokens_render]
  rfl

theorem rejects_wrong_name :
    report ["other", "3", "=", "6"] = none := by
  apply report_rejects_noncanonical
  intro claim h
  simp [renderTokens, doubleEndpoint] at h

theorem rejects_wrong_operator :
    report ["double", "3", "<", "6"] = none := by
  apply report_rejects_noncanonical
  intro claim h
  simp [renderTokens, doubleEndpoint] at h

private theorem decode_leading_zero : "03".toNat? = some 3 := by
  have digits : "03".isNat = true := String.isNat_of_isDigit (by decide) (by decide)
  rw [String.toNat?_eq_some_ofDigitChars digits]
  rfl

theorem rejects_leading_zero :
    report ["double", "03", "=", "6"] = none := by
  apply report_rejects_noncanonical
  intro claim h
  have hi : "03" = Nat.repr claim.input := by
    simpa [renderTokens] using congrArg (fun ts => ts[1]!) h
  have parsed := congrArg String.toNat? hi
  rw [decode_leading_zero, Nat.toNat?_repr] at parsed
  have input_eq : claim.input = 3 := (Option.some.inj parsed).symm
  rw [input_eq] at hi
  exact (by decide : "03" ≠ Nat.repr 3) hi

theorem rejects_extra_token :
    report ["double", "3", "=", "6", "extra"] = none := by
  apply report_rejects_noncanonical
  intro claim h
  have lengths := congrArg List.length h
  simp [renderTokens] at lengths

/-- Pin the actual imported source, independently of the endpoint's text label.
This theorem does not evaluate any concrete queens instance. -/
theorem queens_endpoint_source (n : Nat) :
    ADWH.Experiments.Chapter15.QueensNatChecker.endpoint.run n =
      ADWH.Chapter15.Queens.BitRepresentation.cqueens n :=
  ADWH.Experiments.Chapter15.QueensNatChecker.endpoint.correct n

end CertifiedNatCheckerPreview

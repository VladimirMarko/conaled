import Applications.Resources.TuringSimulation.ConventionalPolynomialDecider
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

/-!
# Conventional checking relations and verifier criterion

The checking machine recognizes a literal-pair language on every raw
word. A separate fixed exponent bounds certificate length. This is
the stated verifier characterization, without an NTM equivalence.
-/

/- Complete preserved component: verifier_criterion. -/
section

namespace Resources.TuringSimulation.ConventionalVerifier

open ConventionalPolynomial

abbrev Bits := List Bool
abbrev Raw := List (Option Bool)

/-- A present delimiter separates the two literal Boolean words. -/
def literalPair (input cert : Bits) : Raw :=
  input.map some ++ [none] ++ cert.map some

theorem literalPair_length (input cert : Bits) :
    (literalPair input cert).length = input.length + cert.length + 1 := by
  simp only [literalPair, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

/-- Unique pair encoding follows from the absence of the delimiter in each
mapped word, using the generic list theorem rather than another parser. -/
theorem literalPair_eq_iff (input cert otherInput otherCert : Bits) :
    literalPair input cert = literalPair otherInput otherCert ↔
      input = otherInput ∧ cert = otherCert := by
  constructor
  · intro equal
    have shaped : input.map some ++ none :: cert.map some =
        otherInput.map some ++ none :: otherCert.map some := by
      simpa only [literalPair, List.append_assoc, List.singleton_append] using equal
    have parts := (List.append_cons_inj_of_notMem
      (x₁ := input.map some) (x₂ := otherInput.map some)
      (z₁ := cert.map some) (z₂ := otherCert.map some)
      (a₁ := (none : Option Bool)) (a₂ := none) (by simp) (by simp)).1 shaped
    have injective : Function.Injective (fun bits : Bits => bits.map (some : Bool → Option Bool)) :=
      List.map_injective_iff.2 (fun _ _ same => Option.some.inj same)
    exact ⟨injective parts.1, injective parts.2.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem literalPair_ne_nil (input cert : Bits) : literalPair input cert ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  rw [literalPair_length, List.length_nil] at length
  omega

/-- The exact language of a checking relation over all raw delimiter words. -/
def PairLanguage (relation : Bits → Bits → Prop) (raw : Raw) : Prop :=
  ∃ input cert : Bits, raw = literalPair input cert ∧ relation input cert

/-- A fixed actual conventional polynomial machine recognizing precisely the
literal-pair language of this relation, including every malformed raw word. -/
structure PolynomialCheckingRelation (relation : Bits → Bits → Prop) where
  answer : Raw → Bool
  decider : PolynomialDecider (Option Bool) answer
  language : ∀ raw : Raw, decider.Accepts raw ↔ PairLanguage relation raw

namespace PolynomialCheckingRelation

variable {relation : Bits → Bits → Prop} (checking : PolynomialCheckingRelation relation)

/-- Literal pair recognition uses both arbitrary-raw language directions and
the injectivity of the literal protocol. -/
theorem accepts_pair_iff (input cert : Bits) :
    checking.decider.Accepts (literalPair input cert) ↔ relation input cert := by
  rw [checking.language]
  constructor
  · rintro ⟨otherInput, otherCert, equal, related⟩
    rcases (literalPair_eq_iff input cert otherInput otherCert).1 equal with ⟨rfl, rfl⟩
    exact related
  · intro related
    exact ⟨input, cert, rfl, related⟩

/-- The empty raw word contains no delimiter, regardless of the relation. -/
theorem empty_raw_rejects : ¬ checking.decider.Accepts [] := by
  intro accepted
  obtain ⟨input, cert, equal, _⟩ := (checking.language []).1 accepted
  exact literalPair_ne_nil input cert equal.symm

end PolynomialCheckingRelation

/-- The selected conventional verifier characterization. Both the checking
machine and witness exponent precede all inputs and witnesses. -/
structure ConventionalVerifierCriterion (language : Bits → Prop) where
  relation : Bits → Bits → Prop
  checking : PolynomialCheckingRelation relation
  witnessExponent : Nat
  witness_iff : ∀ input : Bits,
    language input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ witnessExponent ∧ relation input cert

namespace ConventionalVerifierCriterion

variable {language : Bits → Prop} (criterion : ConventionalVerifierCriterion language)

/-- A bounded witness is accepted by the actual fixed conventional machine. -/
theorem accepted_witness_iff (input : Bits) :
    language input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ criterion.witnessExponent ∧
      criterion.checking.decider.Accepts (literalPair input cert) := by
  rw [criterion.witness_iff]
  constructor
  · rintro ⟨cert, small, related⟩
    exact ⟨cert, small, (criterion.checking.accepts_pair_iff input cert).2 related⟩
  · rintro ⟨cert, small, accepted⟩
    exact ⟨cert, small, (criterion.checking.accepts_pair_iff input cert).1 accepted⟩

/-- The paid delimiter length is a separate consequence of the pure witness
bound; it is not an additive constant hidden inside that bound. -/
theorem accepted_small_pair_iff (input : Bits) :
    language input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ criterion.witnessExponent ∧
      (literalPair input cert).length ≤
        input.length ^ criterion.witnessExponent + input.length + 1 ∧
      criterion.checking.decider.Accepts (literalPair input cert) := by
  constructor
  · intro member
    obtain ⟨cert, small, accepted⟩ := (criterion.accepted_witness_iff input).1 member
    refine ⟨cert, small, ?_, accepted⟩
    rw [literalPair_length]
    omega
  · rintro ⟨cert, small, _length, accepted⟩
    exact (criterion.accepted_witness_iff input).2 ⟨cert, small, accepted⟩

/-- The witness exponent is existentially fixed before the universal input. -/
theorem exists_fixed_power : ∃ k : Nat, ∀ input : Bits,
    language input ↔ ∃ cert : Bits, cert.length ≤ input.length ^ k ∧
      criterion.checking.decider.Accepts (literalPair input cert) :=
  ⟨criterion.witnessExponent, criterion.accepted_witness_iff⟩

end ConventionalVerifierCriterion

end Resources.TuringSimulation.ConventionalVerifier

end
